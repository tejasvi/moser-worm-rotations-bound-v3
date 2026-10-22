#!/usr/bin/env python3
"""Search side (float) of the certified worm lower bound: branch and bound over the placement domain D_tau (Lemma W1)
that writes a certificate with EXPLICIT leaf structures, to be verified by wcheck.py (arb).

Bounds per box: the prototype pipeline (wbnb.py PolyFamily + wchord.py
ChordFamily): full-hull fan, sub-hull fans, small lists (<= MAXSMALL points), chord-certified lists, and a Lemma K
combination (LP) of all of these plus fans of structures at shifted points. Every candidate carries its structure:
  {"v": [g, ...]  global vertex ids in list order, "m": "fan" | "small" | "chord", "z": [zx, zy] (fan centre),
   "t": chord tree}
chord tree: ["s"] (<= MAXSMALL points), ["f", r] (fan from the list's r-th vertex), ["c", s, t, tree1, tree2] (cut by
the chord (list[s], list[t]); piece 1 = list[s..t], piece 2 = list[t..s] cyclically).
Certificate per part: partNNNN.npy (uint8 DFS preorder: 0..dim-1 split coordinate, lower half first; 254 single-list
leaf; 253 Lemma K leaf), partNNNN.leaves.jsonl.gz (one line per leaf in DFS order: {"S": [structures], "w": [weights]}),
partNNNN.json (header).

  wsearch.py FAMILY TAU PART NPARTS SPLIT0 OUTDIR [MAXSMALL]
"""
import sys, os, json, time, gzip, hashlib
import numpy as np
sys.path.insert(0, __import__('os').path.dirname(__import__('os').path.abspath(__file__)))
sys.path.insert(0, __import__('os').path.dirname(__import__('os').path.abspath(__file__)))
sys.path.insert(0, __import__('os').path.dirname(__import__('os').path.abspath(__file__)))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from lbsearch import Rm
import wbnb
from wbnb import PolyFamily
from wchord import ChordFamily
import wfam

MAXSMALL = 4     # lists of <= 4 points need no condition (Lemma W4); 5 would need Keller's Appendix A


class CertFamily(ChordFamily):
    """ChordFamily whose candidates carry their structure (global vertex ids + validity method)."""

    def __init__(self, fam):
        arcs = [wfam.float_vertices(a) for a in fam['arcs']]
        super().__init__(arcs, use_near=False)
        # global vertex ids: body b, row j of self.Vb[b]  <->  g = offs[b] + j; gid_map[g] = (b, polyline vertex index)
        self.offs = np.cumsum([0] + [len(V) for V in self.Vb])[:-1]
        self.gid_map = []
        for b, (A, V) in enumerate(zip(arcs, self.Vb)):
            assert len(V) == len(A), 'every polyline vertex must be a hull vertex (centring = mean of all vertices)'
            ctr = 0.0 if b == 0 else A.mean(axis=0)
            for v in V:
                d = np.abs(A - ctr - v).sum(axis=1); j = int(np.argmin(d))
                assert d[j] < 1e-12
                self.gid_map.append([b, j])

    # map (ib, Q) rows to global ids by matching body-frame coordinates
    def gids(self, ib, Q):
        out = []
        for b, q in zip(ib, Q):
            d = np.abs(self.Vb[b] - q).sum(axis=1)
            j = int(np.argmin(d))
            assert d[j] < 1e-12, 'vertex not found'
            out.append(int(self.offs[b] + j))
        return out

    # candidates without a recorded structure are switched off (they did not help in the measurements)
    def fan_variant(self, c, h, rule):
        return None

    def near_lists(self, c, h, maxvar=8):
        return []

    # ---- small lists: restrict to MAXSMALL points ----
    def small_lists(self, c, mask, sizes=None, noff=6):
        sizes = tuple(s for s in (5, 4, 3) if s <= MAXSMALL)
        return PolyFamily.small_lists(self, c, mask, sizes=sizes, noff=noff)

    def bound_list(self, ib, Q, c, h):
        L, info = PolyFamily.bound_list(self, ib, Q, c, h)
        info['st'] = {"v": self.gids(ib, Q), "m": "small"}
        return L, info

    def bound(self, c, h):
        fz = self.fan(c, h)
        if fz is None:
            return -np.inf, None
        ib, Q, z = fz
        L, info = self._eval(ib, Q, c, h, z=z)
        info['st'] = {"v": self.gids(ib, Q), "m": "fan", "z": [float(z[0]), float(z[1])]}
        return L, info

    def _model(self, ib, Q, c, h):
        L, info = self._eval(ib, Q, c, h)
        return info['F'], info['g'], info['e2']

    # ---- chord certification returning a tree ----
    def _certify_tree(self, lst, LB, UB, DL, memo, ctr):
        n = len(lst)
        if n <= MAXSMALL:
            return ["s"]
        key = tuple(lst)
        if key in memo:
            return memo[key]
        ctr[0] += 1
        if ctr[0] > self.budget:
            return None
        for r in range(n):
            l = lst[r:] + lst[:r]
            p0 = l[0]
            if all(LB[p0, l[1], l[i]] > 0 for i in range(2, n)) and all(LB[p0, l[i], l[i + 1]] > 0 for i in range(2, n - 1)):
                memo[key] = ["f", r]
                return memo[key]
        opts = []
        for s in range(n):
            for d in range(2, n - 1):
                t = (s + d) % n
                pa, pb = lst[s], lst[t]
                if DL[pa, pb] <= 0:
                    continue
                right = [lst[(s + k) % n] for k in range(1, d)]
                left = [lst[(t + k) % n] for k in range(1, n - d)]
                m = min(min(-UB[pa, pb, i] for i in right), min(LB[pa, pb, i] for i in left))
                if m < 0:
                    continue
                p1 = [lst[(s + k) % n] for k in range(0, d + 1)]
                p2 = [lst[(t + k) % n] for k in range(0, n - d + 1)]
                big = (len(p1) > MAXSMALL) + (len(p2) > MAXSMALL)
                opts.append((big, abs(len(p1) - len(p2)), -m, s, t, p1, p2))
        seen = set(); uniq = []
        for o in sorted(opts, key=lambda o: o[:3]):
            chd = frozenset((lst[o[3]], lst[o[4]]))
            if chd in seen:
                continue
            seen.add(chd); uniq.append(o)
        res = None
        for o in uniq[:self.topk]:
            t1 = self._certify_tree(o[5], LB, UB, DL, memo, ctr)
            if t1 is None:
                continue
            t2 = self._certify_tree(o[6], LB, UB, DL, memo, ctr)
            if t2 is None:
                continue
            res = ["c", o[3], o[4], t1, t2]
            break
        memo[key] = res
        return res

    def chord_cands(self, c, h, tau_s):
        out = []
        seen = set()
        lists = []
        self.mask = None
        ib, Q = self.witnesses(c)
        lists.append(('full', ib, Q))
        cand = sorted((((self.subarea(c, m) - tau_s) / np.sqrt(len(m)), m) for m in self.masks), reverse=True)
        for s, m in cand[:4]:
            if s <= 0:
                continue
            self.mask = m
            ib, Q = self.witnesses(c)
            self.mask = None
            lists.append(('sub', ib, Q))
        self.mask = None
        for kind, ib, Q in lists:
            key = (tuple(ib.tolist()), tuple(np.round(Q, 12).ravel().tolist()))
            if key in seen or len(ib) < 3:
                continue
            seen.add(key)
            LB, UB, DL = self._det_bounds(np.asarray(ib, dtype=np.int64), np.asarray(Q, float), c, h)
            tree = self._certify_tree(list(range(len(ib))), LB, UB, DL, {}, [0, 0])
            if tree is not None:
                r = self._eval(ib, Q, c, h)
                r[1]['chord'] = kind
                r[1]['st'] = {"v": self.gids(ib, Q), "m": "chord", "t": tree}
                out.append(r)
        return out

    # ---- Lemma K over candidates (records structures and weights) ----
    def combine(self, c, h, cands, nshift=4):
        models = [(r[1]['F'], r[1]['g'], r[1]['e2'], r[1]['st']) for r in cands if r[1] is not None and 'st' in r[1]]
        if not models:
            return -np.inf, None
        g0 = max(cands, key=lambda r: r[0])[1]['g']
        for k in np.argsort(-(np.abs(g0) * h))[:nshift]:
            sv = np.zeros(len(c)); sv[k] = -np.sign(g0[k]) if g0[k] != 0 else 1.0
            st = self._structure_at(c + sv * h, c, h)
            if st is not None:
                L_, inf_ = self._eval(st[0], st[1], c, h)
                models.append((inf_['F'], inf_['g'], inf_['e2'],
                               {"v": self.gids(st[0], st[1]), "m": "fan", "z": [float(st[2][0]), float(st[2][1])]}))
        m = len(models); d = len(c)
        a = np.array([F - e for (F, g, e, s) in models]); G = np.array([g for (F, g, e, s) in models])
        cvec = np.concatenate([-a, h])
        A_ub = np.vstack([np.hstack([G.T, -np.eye(d)]), np.hstack([-G.T, -np.eye(d)])])
        A_eq = np.concatenate([np.ones(m), np.zeros(d)])[None, :]
        xs = lp_min(cvec, A_ub, np.zeros(2 * d), A_eq, np.array([1.0]))
        if xs is None:
            return -np.inf, None
        lam = np.maximum(xs[:m], 0.0)
        if not lam.sum() > 0:
            return -np.inf, None
        lam = lam / lam.sum()
        keep = lam > 0
        gc = G.T @ lam
        Lc = float(a @ lam - np.abs(gc) @ h)
        info = dict(F=float(np.array([F for (F, g, e, s) in models]) @ lam), g=gc,
                    e2=float(np.array([e for (F, g, e, s) in models]) @ lam), contrib=np.abs(gc) * h, nw=m,
                    small=False, combo=True,
                    stK=[models[i][3] for i in range(m) if keep[i]], lamK=[float(lam[i]) for i in range(m) if keep[i]])
        return Lc, info


_HIGHS = None
def lp_min(cvec, A_ub, b_ub, A_eq, b_eq):
    """min c.x s.t. A_ub x <= b_ub, A_eq x = b_eq, x >= 0 (HiGHS, one thread); x or None."""
    import scipy.sparse as sp
    import highspy
    n = len(cvec); inf = highspy.kHighsInf
    hs = highspy.Highs(); hs.setOptionValue('output_flag', False); hs.setOptionValue('threads', 1)
    lp = highspy.HighsLp(); lp.num_col_ = n; lp.num_row_ = A_ub.shape[0] + A_eq.shape[0]
    lp.col_cost_ = np.asarray(cvec, float); lp.col_lower_ = np.zeros(n); lp.col_upper_ = np.full(n, inf)
    lp.row_lower_ = np.concatenate([np.full(A_ub.shape[0], -inf), b_eq]); lp.row_upper_ = np.concatenate([b_ub, b_eq])
    A = sp.csc_matrix(np.vstack([A_ub, A_eq]))
    lp.a_matrix_.format_ = highspy.MatrixFormat.kColwise
    lp.a_matrix_.start_ = A.indptr; lp.a_matrix_.index_ = A.indices; lp.a_matrix_.value_ = A.data
    hs.passModel(lp); hs.run()
    if hs.getModelStatus() != highspy.HighsModelStatus.kOptimal:
        return None
    return np.array(hs.getSolution().col_value)


def dyadic_up(x, bits=24):
    return float(np.ceil(x * 2 ** bits) / 2 ** bits)


def root_domain(fam, tau):
    """D_tau of Lemma W1 (outward dyadic): angles [0, period_i * pi] (T: [0, pi/3]), |t_x| <= X, |t_y| <= Y."""
    w = np.sqrt(3) / 4
    X = dyadic_up(2 * tau / w - 0.5 + 1e-9); Y = dyadic_up(2 * tau + 1e-9)
    lo, hi = [], []
    for i, per in enumerate(fam['periods']):
        num, den = (int(v) for v in (per.split('/') + ['1'])[:2])
        ang = np.pi * num / den
        if i == 0:
            ang = np.pi / 3          # T: period 2 pi/3, halved by the global half-turn
        lo += [0.0, -X, -Y]; hi += [dyadic_up(ang + 1e-12), X, Y]
    return np.array(lo), np.array(hi)


def run(family, tau, part, nparts, split0, outdir, cap=10 ** 9, cell_index=None):
    famspec = wfam.FAMILIES[family]
    fam = CertFamily(famspec)
    lo, hi = root_domain(famspec, tau)
    d = fam.dim
    s0 = np.array(split0)
    cells = list(np.ndindex(*split0))[part::nparts]
    if cell_index is not None:      # cell mode: one cell of the part (assembled later in cell order by assemble.py)
        cells = [cells[cell_index]]
    tau_s = tau + 1e-7
    codes = bytearray(); leaves = []
    nbox = nleaf = nK = 0; minL = np.inf; t0 = time.time()
    for cell in cells:
        cl = lo + (hi - lo) * np.array(cell) / s0; ch = lo + (hi - lo) * (np.array(cell) + 1) / s0
        stack = [(cl, ch)]
        while stack:
            l, h = stack.pop(); nbox += 1
            if nbox > cap:
                raise RuntimeError('cap')
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
            if info is None:
                k = int(np.argmax(hw))
            else:
                k = int(np.argmax(info.get('split', info['contrib']) + 1e-15 * hw))
            codes.append(k)
            m = 0.5 * (l[k] + h[k])
            l2, h2 = l.copy(), h.copy(); l2[k] = m
            l1, h1 = l.copy(), h.copy(); h1[k] = m
            stack.append((l2, h2)); stack.append((l1, h1))
    if cell_index is not None:
        outdir = os.path.join(outdir, 'cells')
        stem = f'part{part:04d}.c{cell_index:02d}'
    else:
        stem = f'part{part:04d}'
    os.makedirs(outdir, exist_ok=True)
    np.save(os.path.join(outdir, stem + '.npy'), np.frombuffer(bytes(codes), dtype=np.uint8))
    with gzip.open(os.path.join(outdir, stem + '.leaves.jsonl.gz'), 'wt') as f:
        for lf in leaves:
            f.write(json.dumps(lf, separators=(',', ':')) + '\n')
    code_sha = {os.path.basename(p): hashlib.sha256(open(p, 'rb').read()).hexdigest()
                for p in [__file__, wbnb.__file__, sys.modules['wchord'].__file__, wfam.__file__,
                          sys.modules['lbsearch'].__file__]}
    meta = dict(family=family, famspec=famspec, gid_map=fam.gid_map, tau=tau, part=part, nparts=nparts, split0=list(split0),
                lo=lo.tolist(), hi=hi.tolist(), maxsmall=MAXSMALL, boxes=nbox, leaves=nleaf, lemmaK=nK,
                minL=minL, secs=time.time() - t0, code_sha256=code_sha)
    if cell_index is not None:
        meta['cell_index'] = cell_index
    json.dump(meta, open(os.path.join(outdir, stem + '.json'), 'w'))
    return meta


if __name__ == '__main__':
    family, tau, part, nparts = sys.argv[1], float(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
    split0 = [int(v) for v in sys.argv[5].split(',')]
    outdir = sys.argv[6]
    cell_index = None
    if '--cell' in sys.argv:
        cell_index = int(sys.argv[sys.argv.index('--cell') + 1])
    m = run(family, tau, part, nparts, split0, outdir, cell_index=cell_index)
    print(json.dumps({k: m[k] for k in ('part', 'boxes', 'leaves', 'lemmaK', 'minL', 'secs')}), flush=True)
