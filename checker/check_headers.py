#!/usr/bin/env python3
"""Header and grid check for the worm certificate (complements wcheck.py and wcheck_presence_v2.py).
For every part header in CERTDIR it verifies:
  - the arcs are exactly those of Definition 2.1 of the paper (start points, rational lengths, directions in degrees),
    with the angle periods used by the root box (T: 2/3, U: 2, C and S: 1, in units of pi), and the vertex numbering
    lists every polyline vertex once;
  - the grid split0 consists of 12 positive integers, all headers carry the same grid, root box, target and number of
    parts, and the part index equals the file index;
  - the cell endpoints, computed in double precision exactly as wcheck.py computes them (lo + (hi - lo) * k / s), start at
    lo, end at hi, increase with k and equal the rational numbers lo + (hi - lo) k / s in every coordinate, so that the
    cells of the grid tile the root box and are equal.
  check_headers.py CERTDIR"""
import sys, os, json
from fractions import Fraction as Fr
if not __debug__:
    raise SystemExit('run without -O')
import numpy as np

DEF21 = [  # (start, lengths, directions in degrees): Definition 2.1
    (('-1/2', '0'), ('1',), ('0',)),
    (('-1/4', '0'), ('1/2', '1/2'), ('60', '-60')),
    (('0', '0'), ('1/3', '1/3', '1/3'), ('0', '84', '168')),
    (('0', '0'), ('3/20', '7/10', '3/20'), ('0', '-70', '0')),
    (('0', '0'), ('41/250', '84/125', '41/250'), ('0', '75', '0')),
]
PERIODS = ['2/3', '2', '1', '1']

certdir = sys.argv[1]
names = [f for f in os.listdir(certdir) if f.startswith('part') and f.endswith('.json')]
first = None; errs = []
for f in sorted(names):
    h = json.load(open(os.path.join(certdir, f)))
    if int(f[4:-5]) != int(h['part']):
        errs.append(f'{f}: part index {h["part"]}')
    arcs = h['famspec']['arcs']
    if len(arcs) != 5:
        errs.append(f'{f}: {len(arcs)} arcs')
    for a, (st, ls, ds) in zip(arcs, DEF21):
        if [Fr(x) for x in a['start']] != [Fr(x) for x in st] or [Fr(x) for x in a['lengths']] != [Fr(x) for x in ls] or \
                [Fr(x) for x in a['dirs_deg']] != [Fr(x) for x in ds]:
            errs.append(f'{f}: arc {a} differs from Definition 2.1')
    if h['famspec']['periods'] != PERIODS:
        errs.append(f'{f}: periods {h["famspec"]["periods"]}')
    seen = {(b, j) for b, j in h['gid_map']}
    if len(seen) != len(h['gid_map']) or seen != {(b, j) for b, (st, ls, ds) in enumerate(DEF21) for j in range(len(ls) + 1)}:
        errs.append(f'{f}: vertex numbering does not list every vertex once')
    s0 = h['split0']
    if not (isinstance(s0, list) and len(s0) == 12 and all(isinstance(s, int) and s > 0 for s in s0)):
        errs.append(f'{f}: grid {s0}')
    key = (json.dumps(h['famspec'], sort_keys=True), h['gid_map'], h['tau'], h['lo'], h['hi'], s0, h['nparts'], h['maxsmall'])
    if first is None:
        first = key
    elif key != first:
        errs.append(f'{f}: header differs from the first header')
if first is not None and not errs:
    lo = np.array(first[3]); hi = np.array(first[4]); s0 = np.array(first[5]); nparts = int(first[6])
    if len(names) != nparts:
        errs.append(f'{len(names)} headers for {nparts} parts')
    for a in range(12):
        ends = []
        for kk in range(int(s0[a]) + 1):
            k = np.zeros(12, dtype=np.int64); k[a] = kk
            ends.append((lo + (hi - lo) * k / s0)[a])
        if not (ends[0] == lo[a] and ends[-1] == hi[a]):
            errs.append(f'coordinate {a}: cell endpoints {ends[0]!r}, {ends[-1]!r} differ from lo, hi')
        if not all(x < y for x, y in zip(ends, ends[1:])):
            errs.append(f'coordinate {a}: cell endpoints do not increase')
        fl, fh = Fr(float(lo[a])), Fr(float(hi[a]))
        if any(Fr(float(e)) != fl + (fh - fl) * kk / int(s0[a]) for kk, e in enumerate(ends)):
            errs.append(f'coordinate {a}: a cell endpoint is not the exact rational lo + (hi - lo) k / s')
    ncells = int(np.prod(s0))
    print(json.dumps(dict(ok=not errs, headers=len(names), grid=[int(x) for x in s0], cells=ncells, nparts=nparts,
                          tau=first[2], errors=errs[:10])))
else:
    print(json.dumps(dict(ok=False, headers=len(names), errors=errs[:10])))
sys.exit(0 if not errs else 1)
