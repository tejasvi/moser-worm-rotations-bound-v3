#!/usr/bin/env python3
"""Worker pool for the worm certificate search with time-budgeted tasks; same certificate format as wsearch.py.

A task is a sequence of boxes of the branch-and-bound trees of one part; the root task of a part is its cells in
order.  A task runs the depth-first search of wsearch.py over its boxes in order (one DFS stack, the later boxes at the
bottom) until it is done or its time budget is used up.  In the second case the rest of its preorder sequence (the
DFS stack in pop order) is cut into at most NSPLIT contiguous chunks, each chunk becomes a child task, and the task
writes the code 252 once per child at the end of its codes.  The DFS preorder is compositional, so replacing each
placeholder (recursively) by the child's codes gives exactly the codes of the uninterrupted search of the part, and
the leaf records follow the same order.

Layout (Q = OUT.q on the VM):
  Q/queue/NAME.json          waiting task; NAME = RANK_PART_PATH (RANK = the part's rank in the VM's list, so the
                             sorted queue follows the list; PATH = r, r.3, r.3.0, ...: child indices)
  Q/claimed/NAME.json.PID    task being run by worker PID (moved back to queue/ when PID is gone)
  Q/res/NAME.npy, NAME.leaves.jsonl.gz, NAME.json   task result; the json (written last) lists the children
  OUT/partNNNN.{npy,leaves.jsonl.gz,json}            assembled part, written by the worker that finishes the part's
                                                     last task (no task of the part waiting or running); the task
                                                     results of the part are then deleted
  Q/STOP                     workers exit before claiming another task
Cell units (for a run that already has per-cell results from wsearch.py --cell in OUT/cells/): a root task can be one
cell (NAME = G RANK_PART_cKK_PATH, G = 0 or 1 priority group); a finished cell tree is written as
OUT/cells/partNNNN.cKK.* (the wsearch --cell format), and the part is assembled from its cells as by assemble.py
(same lock file OUT/cells/lock.PART as cellone.sh).  A cell task is dropped when the cell file exists, the part file
exists, or OUT.cells/UNDONE exists and no longer lists the part.

  wtask.py seed     FAMILY TAU NPARTS SPLIT0 OUT LISTFILE    root tasks of the listed parts (rank = line number)
  wtask.py seedcelllist FAMILY TAU NPARTS SPLIT0 OUT LISTFILE  cell root tasks for explicit "PART CELL" lines
  wtask.py seedcells FAMILY TAU NPARTS SPLIT0 OUT LISTFILE   cell root tasks for the listed parts' missing cells
                                                            (group 1 if OUT.cells/pids/PART.CELL exists, else 0)
  wtask.py worker   FAMILY TAU NPARTS SPLIT0 OUT BUDGET_SECONDS
  wtask.py assemble FAMILY TAU NPARTS SPLIT0 OUT RANK PART
"""
import sys, os, json, time, gzip, hashlib, random, fcntl
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import wsearch
from wsearch import CertFamily, root_domain
from lbsearch import Rm
import wfam

PLACEHOLDER = 252
NSPLIT = 8


def cell_boxes(famspec, tau, part, nparts, split0):
    """root domain and the part's cell boxes, computed as in wsearch.run (cell list(np.ndindex)[part::nparts] =
    C-order unravel of part, part + nparts, ...)"""
    lo, hi = root_domain(famspec, tau)
    s0 = np.array(split0)
    cells = [tuple(int(v) for v in np.unravel_index(i, split0)) for i in range(part, int(np.prod(s0)), nparts)]
    return lo, hi, [(lo + (hi - lo) * np.array(cell) / s0, lo + (hi - lo) * (np.array(cell) + 1) / s0) for cell in cells]


def atomic_write(path, data):
    with open(path + '.tmp', 'w') as f:
        f.write(data)
    os.rename(path + '.tmp', path)


def hexbox(l, h):
    return [[float(x).hex() for x in l], [float(x).hex() for x in h]]


def child_name(parent, i):
    prefix, path = parent.rsplit('_', 1)
    path = f'{path}.{i}'
    if len(path) > 150:
        path = 'x' + hashlib.blake2b(path.encode(), digest_size=10).hexdigest()
    return f'{prefix}_{path}'


def unit_prefix(task):
    if 'cell' in task:
        return f"{task['grp']}{task['rank']:05d}_{task['part']:05d}_c{task['cell']:02d}_"
    return f"{task['rank']:05d}_{task['part']:05d}_"


def seed(famspec, tau, nparts, split0, out, listfile):
    Q = out + '.q'
    for d in ('queue', 'claimed', 'res', 'logs', 'locks'):
        os.makedirs(os.path.join(Q, d), exist_ok=True)
    os.makedirs(out, exist_ok=True)
    parts = [int(l) for l in open(listfile) if l.strip()]
    n = 0
    for rank, part in enumerate(parts):
        nm = f'{rank:05d}_{part:05d}_r'
        if os.path.exists(os.path.join(out, f'part{part:04d}.json')) or os.path.exists(os.path.join(Q, 'res', nm + '.json')):
            continue
        atomic_write(os.path.join(Q, 'queue', nm + '.json'), json.dumps(dict(rank=rank, part=part, root=True)))
        n += 1
    print('seeded', n, 'root tasks of', len(parts), 'parts')


def seedcells(famspec, tau, nparts, split0, out, listfile):
    Q = out + '.q'
    for d in ('queue', 'claimed', 'res', 'logs', 'locks'):
        os.makedirs(os.path.join(Q, d), exist_ok=True)
    parts = [int(l) for l in open(listfile) if l.strip()]
    n = [0, 0]
    present = set(os.listdir(os.path.join(Q, 'queue'))) | set(os.listdir(os.path.join(Q, 'res'))) | \
        {c.rpartition('.')[0] for c in os.listdir(os.path.join(Q, 'claimed'))}      # waiting, done or running
    for rank, part in enumerate(parts):
        if os.path.exists(os.path.join(out, f'part{part:04d}.json')):
            continue
        ncell = len(cell_boxes(famspec, tau, part, nparts, split0)[2])
        for k in range(ncell):
            if os.path.exists(os.path.join(out, 'cells', f'part{part:04d}.c{k:02d}.json')):
                continue
            g = 1 if os.path.exists(os.path.join(out + '.cells', 'pids', f'{part}.{k}')) else 0
            task = dict(rank=rank, part=part, cell=k, grp=g, root=True)
            nm = unit_prefix(task) + 'r'
            if nm + '.json' in present:
                continue
            atomic_write(os.path.join(Q, 'queue', nm + '.json'), json.dumps(task))
            n[g] += 1
    print('seeded cell tasks: group 0', n[0], 'group 1', n[1], 'parts', len(parts))


def seedcelllist(famspec, tau, nparts, split0, out, listfile):
    """cell root tasks for explicit "PART CELL" lines (cells of heavy parts spread over several machines; the part is
    assembled on its owner from the cell files gathered there); rank = order of first appearance of the part"""
    Q = out + '.q'
    for d in ('queue', 'claimed', 'res', 'logs', 'locks'):
        os.makedirs(os.path.join(Q, d), exist_ok=True)
    present = set(os.listdir(os.path.join(Q, 'queue'))) | set(os.listdir(os.path.join(Q, 'res'))) | \
        {c.rpartition('.')[0] for c in os.listdir(os.path.join(Q, 'claimed'))}
    rank = {}; n = 0
    for line in open(listfile):
        f = line.split()
        if len(f) != 2:
            continue
        part, k = int(f[0]), int(f[1])
        rank.setdefault(part, len(rank))
        if os.path.exists(os.path.join(out, f'part{part:04d}.json')) or \
                os.path.exists(os.path.join(out, 'cells', f'part{part:04d}.c{k:02d}.json')):
            continue
        task = dict(rank=rank[part], part=part, cell=k, grp=0, root=True)
        nm = unit_prefix(task) + 'r'
        if nm + '.json' in present:
            continue
        atomic_write(os.path.join(Q, 'queue', nm + '.json'), json.dumps(task))
        n += 1
    print('seeded heavy cell tasks', n, 'of', len(rank), 'parts')


def task_boxes(famspec, tau, nparts, split0, task):
    if task.get('root') and 'cell' in task:
        return [cell_boxes(famspec, tau, task['part'], nparts, split0)[2][task['cell']]]
    if task.get('root'):
        return cell_boxes(famspec, tau, task['part'], nparts, split0)[2]
    return [(np.array([float.fromhex(x) for x in l]), np.array([float.fromhex(x) for x in h])) for l, h in task['boxes']]


SPLIT_EPS = 1e-5
MIN_HW = 1e-12


def hull_area(fam, c):
    fam.mask = None
    ib, Q = fam.witnesses(c)
    pl = fam.place(c)
    X = np.array([Rm(pl[i][0]) @ q + pl[i][1] for i, q in zip(ib, Q)])
    return 0.5 * float(np.sum(X[:, 0] * np.roll(X[:, 1], -1) - np.roll(X[:, 0], -1) * X[:, 1]))


def split_coord(fam, info, c, hw, L):
    """split coordinate: the steering vector of the bound (wsearch rule), unless it explains less than half of the
    loss against the true hull area at the centre (max < 1e-5 or sum < (A(c) - L) / 2).  Then the loss is structural
    (vertices dropped for fan validity, sub-structures: the box is too wide where vertices move), and the steering
    vector is noise (a Lemma K combination whose gradient cancels: 1e-9..1e-4, which used to keep halving coordinates
    that were already tiny); split the coordinate of largest vertex movement instead: angle of body i -> (max arm
    length of body i) x h, translation -> h.  Any split is valid for the checker."""
    if info is None:
        return int(np.argmax(hw))
    s = info.get('split', info['contrib'])
    if float(np.max(s)) < SPLIT_EPS or float(np.sum(s)) < 0.5 * (hull_area(fam, c) - L):
        arm = getattr(fam, '_arm', None)
        if arm is None:
            arm = np.ones(fam.dim)
            for i in range(1, fam.k + 1):
                ir, ix, iy = fam.pidx(i)
                arm[ir] = float(np.max(np.linalg.norm(fam.Vb[i], axis=1)))
            fam._arm = arm
        score = arm * hw
    else:
        score = s + 1e-15 * hw
    # v5: never split a coordinate narrower than MIN_HW (a box split below float resolution fails the checker's
    # exact-box test); the caller's stuck test (max half-width < 1e-9) fires before every coordinate is that narrow
    score = np.where(hw < MIN_HW, -np.inf, score)
    return int(np.argmax(score))


def run_task(fam, tau, boxes, budget):
    tau_s = tau + 1e-7
    stack = list(reversed(boxes))            # pop() yields the boxes in order; each box's subtree is finished first
    codes = bytearray(); leaves = []; children = []
    nbox = nleaf = nK = 0; minL = np.inf; t0 = time.time()
    while stack:
        if time.time() - t0 > budget:
            rest = stack[::-1]                # remaining preorder sequence (pop order)
            k = min(NSPLIT, len(rest))
            cuts = [round(i * len(rest) / k) for i in range(k + 1)]
            for i in range(k):
                codes.append(PLACEHOLDER); children.append(rest[cuts[i]:cuts[i + 1]])
            break
        l, h = stack.pop(); nbox += 1
        c = 0.5 * (l + h); hw = 0.5 * (h - l)
        L, info = fam.bound_best(c, hw, tau_s)
        if L >= tau_s and info is not None:
            if info.get('combo'):
                codes.append(253); nK += 1
                leaves.append({"S": info['stK'], "w": info['lamK']})
            else:
                codes.append(254)
                leaves.append({"S": [info['st']], "w": [1.0]})
            nleaf += 1; minL = min(minL, L)
            continue
        if hw.max() < 1e-9:
            raise RuntimeError(f'stuck at {list(c)} L={L}')
        k = split_coord(fam, info, c, hw, L)
        codes.append(k)
        m = 0.5 * (l[k] + h[k])
        l2, h2 = l.copy(), h.copy(); l2[k] = m
        l1, h1 = l.copy(), h.copy(); h1[k] = m
        stack.append((l2, h2)); stack.append((l1, h1))
    return codes, leaves, children, dict(boxes=nbox, leaves=nleaf, lemmaK=nK, minL=(minL if np.isfinite(minL) else None),
                                         secs=time.time() - t0)


def outstanding(Q, prefix):
    return any(n.startswith(prefix) for n in os.listdir(os.path.join(Q, 'queue'))) or \
        any(n.startswith(prefix) for n in os.listdir(os.path.join(Q, 'claimed')))


def code_shas():
    return {os.path.basename(p): hashlib.sha256(open(p, 'rb').read()).hexdigest()
            for p in [os.path.abspath(__file__), wsearch.__file__, wsearch.wbnb.__file__, sys.modules['wchord'].__file__,
                      wfam.__file__, sys.modules['lbsearch'].__file__]}


def build(Q, root):
    """splice the task tree below root: (codes, leaf lines, totals, task names)"""
    def load(nm):
        base = os.path.join(Q, 'res', nm)
        meta = json.load(open(base + '.json'))
        with gzip.open(base + '.leaves.jsonl.gz', 'rt') as g:
            lv = g.read().splitlines(keepends=True)
        return dict(codes=np.load(base + '.npy'), pos=0, ch=meta['children'], ci=0, lv=lv, li=0, meta=meta, nm=nm)
    out = bytearray(); lines = []; names = []
    tot = dict(boxes=0, leaves=0, lemmaK=0, secs=0.0, minL=np.inf, tasks=0)
    st = [load(root)]
    while st:
        fr = st[-1]
        if fr['pos'] == len(fr['codes']):
            assert fr['ci'] == len(fr['ch']) and fr['li'] == len(fr['lv']), f"task result inconsistent: {fr['nm']}"
            m = fr['meta']
            for k in ('boxes', 'leaves', 'lemmaK', 'secs'):
                tot[k] += m[k]
            if m['minL'] is not None:
                tot['minL'] = min(tot['minL'], m['minL'])
            tot['tasks'] += 1; names.append(fr['nm'])
            st.pop(); continue
        code = int(fr['codes'][fr['pos']]); fr['pos'] += 1
        if code == PLACEHOLDER:
            st.append(load(fr['ch'][fr['ci']])); fr['ci'] += 1
        else:
            out.append(code)
            if code >= 253:
                lines.append(fr['lv'][fr['li']]); fr['li'] += 1
    return out, lines, tot, names


def assemble(famspec, family, tau, nparts, split0, out, rank, part):
    Q = out + '.q'
    stem = os.path.join(out, f'part{part:04d}')
    if os.path.exists(stem + '.json'):
        return False
    lo, hi = root_domain(famspec, tau)
    codes, lines, tot, names = build(Q, f'{rank:05d}_{part:05d}_r')
    assert sum(1 for b in codes if b >= 253) == len(lines) == tot['leaves']
    with open(stem + '.npy.tmp', 'wb') as f:
        np.save(f, np.frombuffer(bytes(codes), dtype=np.uint8))
    with gzip.open(stem + '.leaves.jsonl.gz.tmp', 'wt') as f:
        f.writelines(lines)
    fam = CertFamily(famspec)
    meta = dict(family=family, famspec=famspec, gid_map=fam.gid_map, tau=tau, part=part, nparts=nparts,
                split0=list(split0), lo=lo.tolist(), hi=hi.tolist(), maxsmall=wsearch.MAXSMALL, boxes=tot['boxes'],
                leaves=tot['leaves'], lemmaK=tot['lemmaK'], minL=tot['minL'], secs=tot['secs'], tasks=tot['tasks'],
                code_sha256=code_shas())
    os.rename(stem + '.npy.tmp', stem + '.npy')
    os.rename(stem + '.leaves.jsonl.gz.tmp', stem + '.leaves.jsonl.gz')
    atomic_write(stem + '.json', json.dumps(meta))
    for nm in names:
        for e in ('.npy', '.leaves.jsonl.gz', '.json'):
            os.remove(os.path.join(Q, 'res', nm + e))
    return True


def assemble_cell(famspec, family, tau, nparts, split0, out, task):
    """write OUT/cells/partNNNN.cKK.* from the cell's task tree (wsearch --cell format); False if it exists"""
    Q = out + '.q'
    part, k = task['part'], task['cell']
    os.makedirs(os.path.join(out, 'cells'), exist_ok=True)
    stem = os.path.join(out, 'cells', f'part{part:04d}.c{k:02d}')
    if os.path.exists(stem + '.json'):
        return False
    lo, hi = root_domain(famspec, tau)
    codes, lines, tot, names = build(Q, unit_prefix(task) + 'r')
    assert sum(1 for b in codes if b >= 253) == len(lines) == tot['leaves']
    with open(stem + '.npy.tmp', 'wb') as f:
        np.save(f, np.frombuffer(bytes(codes), dtype=np.uint8))
    with gzip.open(stem + '.leaves.jsonl.gz.tmp', 'wt') as f:
        f.writelines(lines)
    fam = CertFamily(famspec)
    meta = dict(family=family, famspec=famspec, gid_map=fam.gid_map, tau=tau, part=part, nparts=nparts,
                split0=list(split0), lo=lo.tolist(), hi=hi.tolist(), maxsmall=wsearch.MAXSMALL, boxes=tot['boxes'],
                leaves=tot['leaves'], lemmaK=tot['lemmaK'], minL=tot['minL'], secs=tot['secs'], tasks=tot['tasks'],
                code_sha256=code_shas(), cell_index=k)
    os.rename(stem + '.npy.tmp', stem + '.npy')
    os.rename(stem + '.leaves.jsonl.gz.tmp', stem + '.leaves.jsonl.gz')
    atomic_write(stem + '.json', json.dumps(meta))
    for nm in names:
        for e in ('.npy', '.leaves.jsonl.gz', '.json'):
            os.remove(os.path.join(Q, 'res', nm + e))
    return True


def assemble_from_cells(out, part, ncells):
    """assemble.py: the part from its ncells cell files, in cell order (caller holds OUT/cells/lock.PART)"""
    stem = os.path.join(out, f'part{part:04d}')
    if os.path.exists(stem + '.json'):
        return False
    names = [os.path.join(out, 'cells', f'part{part:04d}.c{k:02d}') for k in range(ncells)]
    if not all(os.path.exists(n + '.json') for n in names):
        return False
    metas = [json.load(open(n + '.json')) for n in names]
    assert all(m['cell_index'] == k and m['part'] == part for k, m in enumerate(metas))
    codes = np.concatenate([np.load(n + '.npy') for n in names])
    with open(stem + '.npy.tmp', 'wb') as f:
        np.save(f, codes)
    with gzip.open(stem + '.leaves.jsonl.gz.tmp', 'wt') as f:
        for n in names:
            with gzip.open(n + '.leaves.jsonl.gz', 'rt') as g:
                for line in g:
                    f.write(line)
    meta = dict(metas[0]); del meta['cell_index']
    for k in ('boxes', 'leaves', 'lemmaK', 'secs'):
        meta[k] = sum(m[k] for m in metas)
    meta['minL'] = min(m['minL'] for m in metas)
    meta['assembled_from_cells'] = ncells
    with open(stem + '.json.tmp', 'w') as f:
        json.dump(meta, f)
    os.rename(stem + '.npy.tmp', stem + '.npy')
    os.rename(stem + '.leaves.jsonl.gz.tmp', stem + '.leaves.jsonl.gz')
    os.rename(stem + '.json.tmp', stem + '.json')
    return True


class Undone:
    """OUT.cells/UNDONE (re-read when it changes); None = no such file = no restriction"""
    def __init__(self, out):
        self.path = os.path.join(out + '.cells', 'UNDONE'); self.mtime = None; self.parts = None

    def has(self, part):
        try:
            mt = os.path.getmtime(self.path)
        except FileNotFoundError:
            return True
        if mt != self.mtime:
            self.parts = {int(l) for l in open(self.path) if l.strip()}; self.mtime = mt
        return part in self.parts


def sweep(Q):
    """move claims of dead workers back to the queue"""
    cd = os.path.join(Q, 'claimed')
    for n in os.listdir(cd):
        nm, _, pid = n.rpartition('.')
        if pid.isdigit() and not os.path.exists(f'/proc/{pid}'):
            try:
                os.rename(os.path.join(cd, n), os.path.join(Q, 'queue', nm))
            except FileNotFoundError:
                pass


def worker(famspec, family, tau, nparts, split0, out, budget):
    Q = out + '.q'
    fam = CertFamily(famspec)
    me = os.getpid(); rng = random.Random(me)
    logf = open(os.path.join(Q, 'logs', f'w{me}.log'), 'a')
    undone = Undone(out)
    idle = 0
    while not os.path.exists(os.path.join(Q, 'STOP')):
        names = sorted(n for n in os.listdir(os.path.join(Q, 'queue')) if n.endswith('.json'))
        if not names:
            sweep(Q)
            idle = idle + 1 if not os.listdir(os.path.join(Q, 'claimed')) else 0
            if idle >= 6:
                break
            time.sleep(5); continue
        idle = 0
        cand = names[:32]; rng.shuffle(cand)
        claim = None
        for nm in cand:
            try:
                os.rename(os.path.join(Q, 'queue', nm), os.path.join(Q, 'claimed', f'{nm}.{me}'))
                claim = nm; break
            except FileNotFoundError:
                continue
        if claim is None:
            continue
        cpath = os.path.join(Q, 'claimed', f'{claim}.{me}')
        task = json.load(open(cpath))
        part = task['part']
        if os.path.exists(os.path.join(out, f'part{part:04d}.json')) or not undone.has(part) or \
                ('cell' in task and os.path.exists(os.path.join(out, 'cells', f"part{part:04d}.c{task['cell']:02d}.json"))):
            os.remove(cpath)
            logf.write(f"{time.strftime('%H:%M:%S')} {claim[:-5]} dropped (done elsewhere)\n"); logf.flush()
            continue
        codes, leaves, children, st = run_task(fam, tau, task_boxes(famspec, tau, nparts, split0, task), budget)
        stem = claim[:-5]
        base = os.path.join(Q, 'res', stem)
        with open(base + '.npy.tmp', 'wb') as f:
            np.save(f, np.frombuffer(bytes(codes), dtype=np.uint8))
        os.rename(base + '.npy.tmp', base + '.npy')
        with gzip.open(base + '.leaves.jsonl.gz.tmp', 'wt') as f:
            for lf in leaves:
                f.write(json.dumps(lf, separators=(',', ':')) + '\n')
        os.rename(base + '.leaves.jsonl.gz.tmp', base + '.leaves.jsonl.gz')
        chn = []
        for i, seq in enumerate(children):
            nm = child_name(stem, i)
            ch = dict(rank=task['rank'], part=task['part'], boxes=[hexbox(l, h) for l, h in seq])
            if 'cell' in task:
                ch.update(cell=task['cell'], grp=task['grp'])
            atomic_write(os.path.join(Q, 'queue', nm + '.json'), json.dumps(ch))
            chn.append(nm)
        atomic_write(base + '.json', json.dumps(dict(st, name=stem, children=chn)))
        os.remove(cpath)
        logf.write(f"{time.strftime('%H:%M:%S')} {stem} boxes {st['boxes']} secs {st['secs']:.1f} children {len(chn)}\n")
        logf.flush()
        prefix = unit_prefix(task)
        if chn or outstanding(Q, prefix):
            continue
        try:        # v6: a unit whose tasks were removed (dropped, or deleted on purpose) cannot be built: log, go on
            if 'cell' not in task:
                with open(os.path.join(Q, 'locks', f"{part}.lock"), 'w') as lk:
                    fcntl.flock(lk, fcntl.LOCK_EX)
                    if not outstanding(Q, prefix) and assemble(famspec, family, tau, nparts, split0, out, task['rank'], part):
                        logf.write(f"{time.strftime('%H:%M:%S')} assembled part {part}\n"); logf.flush()
                continue
            with open(os.path.join(Q, 'locks', f"{part}.{task['cell']}.lock"), 'w') as lk:
                fcntl.flock(lk, fcntl.LOCK_EX)
                if outstanding(Q, prefix) or not assemble_cell(famspec, family, tau, nparts, split0, out, task):
                    continue
            logf.write(f"{time.strftime('%H:%M:%S')} assembled cell {part}.{task['cell']}\n"); logf.flush()
            ncell = len(cell_boxes(famspec, tau, part, nparts, split0)[2])
            with open(os.path.join(out, 'cells', f'lock.{part}'), 'a') as lk:
                fcntl.flock(lk, fcntl.LOCK_EX)
                if assemble_from_cells(out, part, ncell):
                    logf.write(f"{time.strftime('%H:%M:%S')} assembled part {part} from cells\n"); logf.flush()
        except (FileNotFoundError, AssertionError, KeyError) as e:
            logf.write(f"{time.strftime('%H:%M:%S')} {prefix} not assembled (incomplete unit: {type(e).__name__} {e})\n"); logf.flush()
    logf.write(f"{time.strftime('%H:%M:%S')} exit\n"); logf.close()


if __name__ == '__main__':
    if not __debug__:
        raise SystemExit('run without -O')
    mode, family, tau, nparts, split0, out = sys.argv[1], sys.argv[2], float(sys.argv[3]), int(sys.argv[4]), \
        tuple(int(x) for x in sys.argv[5].split(',')), sys.argv[6]
    famspec = wfam.FAMILIES[family]
    if mode == 'seed':
        seed(famspec, tau, nparts, split0, out, sys.argv[7])
    elif mode == 'seedcelllist':
        seedcelllist(famspec, tau, nparts, split0, out, sys.argv[7])
    elif mode == 'seedcells':
        seedcells(famspec, tau, nparts, split0, out, sys.argv[7])
    elif mode == 'worker':
        worker(famspec, family, tau, nparts, split0, out, float(sys.argv[7]))
    elif mode == 'assemble':
        print(assemble(famspec, family, tau, nparts, split0, out, int(sys.argv[7]), int(sys.argv[8])))
