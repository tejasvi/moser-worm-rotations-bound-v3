#!/usr/bin/env python3
"""Negative and consistency tests for wcheck.py on a small test certificate (cells of wsearch run with nparts = 65536).
  wcheck_selftest.py CERTDIR PART
Each test tampers with a COPY of one leaf record or the header in memory and expects the checker to reject it."""
import sys, os, json, gzip, copy
import numpy as np
os.environ['WCHECK_TEST_PARTIAL'] = '1'
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import wcheck

certdir, part = sys.argv[1], int(sys.argv[2])
meta = json.load(open(os.path.join(certdir, f'part{part:04d}.json')))
codes = np.load(os.path.join(certdir, f'part{part:04d}.npy'))
recs = [json.loads(l) for l in gzip.open(os.path.join(certdir, f'part{part:04d}.leaves.jsonl.gz'), 'rt')]
lo = np.array(meta['lo']); hi = np.array(meta['hi']); s0 = np.array(meta['split0'])
cell = list(np.ndindex(*meta['split0']))[part::int(meta['nparts'])][0]
cl = lo + (hi - lo) * np.array(cell) / s0; chh = lo + (hi - lo) * (np.array(cell) + 1) / s0
leaves = []
stack = [(cl, chh)]; pos = 0
while stack:
    l, h = stack.pop(); code = int(codes[pos]); pos += 1
    if code >= 253:
        leaves.append((0.5 * (l + h), 0.5 * (h - l)))
    else:
        m = 0.5 * (l[code] + h[code]); l2, h2 = l.copy(), h.copy(); l2[code] = m; l1, h1 = l.copy(), h.copy(); h1[code] = m
        stack.append((l2, h2)); stack.append((l1, h1))
ch = wcheck.Checker(meta)
res = []
def expect(name, ok_expected, ok):
    res.append((name, ok_expected == ok))
    print(('PASS ' if ok_expected == ok else 'FAIL ') + name, '(checker said %s)' % ok)

# 0: every original leaf passes
allok = all(ch.leaf(c, h, r)[0] for (c, h), r in zip(leaves, recs))
expect('original leaves accepted', True, allok)
# pick a leaf with a fan structure
idx = next(i for i, r in enumerate(recs) if r['S'][0]['m'] == 'fan')
c, h = leaves[idx]; r0 = recs[idx]
# 1: duplicated vertex in a fan
r = copy.deepcopy(r0); r['S'][0]['v'] = r['S'][0]['v'] + [r['S'][0]['v'][0]]
expect('fan with a repeated vertex rejected', False, ch.leaf(c, h, r)[0])
# 2: fan list reversed (clockwise): order condition must fail
r = copy.deepcopy(r0); r['S'][0]['v'] = r['S'][0]['v'][::-1]
expect('clockwise fan rejected', False, ch.leaf(c, h, r)[0])
# 3: fan centre far outside the hull: winding 0
r = copy.deepcopy(r0); r['S'][0]['z'] = [5.0, 5.0]
expect('fan centre outside rejected', False, ch.leaf(c, h, r)[0])
# 4: 'small' structure with 5 vertices (more than maxsmall = 4)
r = copy.deepcopy(r0); r['S'][0] = {'v': list(range(5)), 'm': 'small'}
expect('5-point small list rejected', False, ch.leaf(c, h, r)[0])
# 5: Lemma K with a negative weight
r = {'S': [r0['S'][0], r0['S'][0]], 'w': [1.5, -0.5]}
expect('negative weight rejected', False, ch.leaf(c, h, r)[0])
# 6: tau raised above the leaf value
ch2 = wcheck.Checker(dict(meta, tau=10.0))
expect('tau = 10 rejected', False, ch2.leaf(c, h, r0)[0])
# 7: coincident vertices: a fan whose two consecutive vertices coincide at the box centre (T apex placed onto L's end)
#    is built by moving the box centre so that vertex g1 sits on vertex g0; the det at the centre is 0 -> reject
fam = ch.fam
r = copy.deepcopy(r0)
lst = r['S'][0]['v']
cc = c.copy()
pa, rot = ch.boxes(cc, h)
g0, g1 = lst[0], lst[1]
if fam.gb[g1] != 0:
    b = fam.gb[g1]; ir, ix, iy = fam.pidx(b)
    X0 = ch.placed(g0, pa, rot); X1 = ch.placed(g1, pa, rot)
    cc[ix] += float((X0[0] - X1[0]).mid()); cc[iy] += float((X0[1] - X1[1]).mid())
    expect('coincident consecutive vertices rejected', False, ch.leaf(cc, h * 0 + 1e-9, r)[0])
# 8: a chord tree with a wrong side condition: swap the cut indices order if a chord leaf exists
ci = [i for i, rr in enumerate(recs) if any(st['m'] == 'chord' and st['t'][0] == 'c' for st in rr['S'])]
if ci:
    i = ci[0]; r = copy.deepcopy(recs[i]); c8, h8 = leaves[i]
    for st in r['S']:
        if st['m'] == 'chord' and st['t'][0] == 'c':
            st['t'][1], st['t'][2] = st['t'][2], st['t'][1]     # same chord, sides exchanged
    expect('chord with exchanged sides rejected', False, ch.leaf(c8, h8, r)[0])
else:
    print('SKIP chord test (no cut in this part)')
print('ALL PASS' if all(ok for _, ok in res) else 'SOME FAILED')
