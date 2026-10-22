#!/usr/bin/env python3
"""Leaf-level test at the placement with the smallest hull area found (data/opt_point.json): finds the part, cell and
leaf of the certificate whose box contains the placement, checks that the box is exactly c +- h, and runs the leaf
routine of wcheck_v2.py on it with the target of the header and with the targets given on the command line.
  negtest_leaf.py CERTDIR [TAU ...]"""
import sys, os, json, gzip
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
import wcheck_v2 as wc

cert = sys.argv[1]; taus = [float(x) for x in sys.argv[2:]]
here = os.path.dirname(os.path.abspath(__file__))
P = np.array(json.load(open(os.path.join(here, '..', 'data', 'opt_point.json')))['p'])
h0 = json.load(open(os.path.join(cert, 'part0000.json')))
lo = np.array(h0['lo']); hi = np.array(h0['hi']); s0 = np.array(h0['split0'])
k = [min(int(s0[a]) - 1, int((P[a] - lo[a]) / (hi[a] - lo[a]) * s0[a])) for a in range(12)]
idx = 0
for a in range(12):
    idx = idx * int(s0[a]) + k[a]
part = idx % int(h0['nparts'])
meta = json.load(open(os.path.join(cert, f'part{part:04d}.json')))
codes = np.load(os.path.join(cert, f'part{part:04d}.npy'))
recs = gzip.open(os.path.join(cert, f'part{part:04d}.leaves.jsonl.gz'), 'rt')
cells = list(np.ndindex(*meta['split0']))[part::int(meta['nparts'])]
pos = 0; li = 0; found = None
for ci, cell in enumerate(cells):
    cl = lo + (hi - lo) * np.array(cell) / s0; ch = lo + (hi - lo) * (np.array(cell) + 1) / s0
    stack = [(cl, ch)]
    while stack:
        l, h = stack.pop(); code = int(codes[pos]); pos += 1
        if code >= 253:
            line = recs.readline()
            if found is None and np.all(l <= P) and np.all(P <= h):
                found = (li, ci, l, h, json.loads(line))
            li += 1
        else:
            m = 0.5 * (l[code] + h[code]); l2, h2 = l.copy(), h.copy(); l2[code] = m; l1, h1 = l.copy(), h.copy(); h1[code] = m
            stack.append((l2, h2)); stack.append((l1, h1))
    if found is not None:
        break
li, ci, l, h, rec = found
okb, c, r = wc.exact_box(l, h)
print(json.dumps(dict(part=part, cell_in_part=ci, leaf=li, contains_opt_point=True, exact_box=okb)))
for tau in [meta['tau']] + taus:
    m2 = dict(meta); m2['tau'] = tau
    chk = wc.Checker(m2)
    ok, msg = chk.leaf(c, r, rec)
    print(json.dumps(dict(tau=tau, leaf_ok=bool(ok), min_margin=chk.min_margin)))
