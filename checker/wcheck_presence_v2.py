#!/usr/bin/env python3
"""Completes a distributed check of a worm certificate (v2: leaf-range checks): every part 0..nparts-1 is present in
MERGED (npy, json, leaves), all headers agree (family spec, gid_map, tau, split0, nparts, lo, hi, maxsmall), and for
every part the passing check-log lines (ok, 0 fails) whose sha256 of the three part files equal the merged copy's
have leaf ranges [a, b) that cover [0, leaves) exactly with one consistent leaf count.  Lines of wcheck.py (v1, no
leaf_range) count as the full range.
  wcheck_presence_v2.py MERGED CHECKLOG [CHECKLOG ...]"""
import sys, os, json, hashlib
if not __debug__:
    raise SystemExit('run without -O')
merged = sys.argv[1]
logs = {}
for f in sys.argv[2:]:
    for line in open(f):
        if line.startswith('{'):
            r = json.loads(line)
            if r.get('ok') and r.get('fails') == 0:
                logs.setdefault(int(r['part']), []).append(r)
first = json.load(open(os.path.join(merged, 'part0000.json')))
NP = int(first['nparts'])
keys = ('famspec', 'gid_map', 'tau', 'split0', 'nparts', 'lo', 'hi', 'maxsmall')
bad = []; leaves = 0; minm = None; nlines = 0
for p in range(NP):
    files = {ext: os.path.join(merged, f'part{p:04d}{ext}') for ext in ('.npy', '.json', '.leaves.jsonl.gz')}
    if not all(os.path.exists(v) for v in files.values()):
        bad.append((p, 'missing')); continue
    meta = json.load(open(files['.json']))
    if any(meta[k] != first[k] for k in keys) or int(meta['part']) != p:
        bad.append((p, 'header mismatch')); continue
    sh = {ext: hashlib.sha256(open(v, 'rb').read()).hexdigest() for ext, v in files.items()}
    rs = [r for r in logs.get(p, []) if r.get('sha256') == sh]
    if not rs:
        bad.append((p, 'no passing check log for these bytes')); continue
    tot = {r['leaves'] for r in rs}
    if len(tot) != 1:
        bad.append((p, 'inconsistent leaf counts')); continue
    n = tot.pop()
    ivs = sorted(tuple(r.get('leaf_range', [0, r['leaves']])) for r in rs)
    reach = 0
    for a, b in ivs:
        if a > reach:
            break
        reach = max(reach, b)
    if reach < n:
        bad.append((p, f'leaf ranges cover only [0, {reach}) of {n}')); continue
    leaves += n; nlines += len(rs)
    for r in rs:
        m = r['min_margin']
        if m is not None:
            minm = m if minm is None else min(minm, m)
print(json.dumps(dict(nparts=NP, all_ok=(len(bad) == 0), leaves=leaves, min_margin=minm, bad=bad[:20], nbad=len(bad),
                      check_lines=nlines, tau=first['tau'], family=first['family'])))
