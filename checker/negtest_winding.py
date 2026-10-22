#!/usr/bin/env python3
"""Negative test of the angle-sum (winding) condition of the fan test in wcheck.py.
Every fan of odd length m >= 5 in the leaf records of the given parts is reordered in star order (the vertex in position
2j mod m moves to position j). The reordered list winds twice around the point z. At the centre of the leaf box (all
half-widths 0) its determinants det(x_j - z, x_{j+1} - z) are all positive in the cases counted, so only the angle-sum
test can reject it. The test passes if fan_ok accepts every original fan on its leaf box and rejects every such
reordering, and if there is at least one such case.
  negtest_winding.py CERTDIR [PART ...]      (default: every part in CERTDIR)"""
import sys, os, json, gzip
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
from flint import arb
import wcheck as wc

certdir = sys.argv[1]
parts = [int(p) for p in sys.argv[2:]] or sorted(int(f[4:-5]) for f in os.listdir(certdir)
                                                 if f.startswith('part') and f.endswith('.json'))
res = dict(fans=0, star_all_positive=0, star_rejected=0, star_with_nonpositive_det=0, original_rejected=0, angle_sums_over_pi=[])
for part in parts:
    meta = json.load(open(os.path.join(certdir, f'part{part:04d}.json')))
    ch = wc.Checker(meta)
    codes = np.load(os.path.join(certdir, f'part{part:04d}.npy'))
    recs = gzip.open(os.path.join(certdir, f'part{part:04d}.leaves.jsonl.gz'), 'rt')
    lo = np.array(meta['lo']); hi = np.array(meta['hi']); s0 = np.array(meta['split0'])
    pos = 0
    for cell in list(np.ndindex(*meta['split0']))[part::int(meta['nparts'])]:
        stack = [(lo + (hi - lo) * np.array(cell) / s0, lo + (hi - lo) * (np.array(cell) + 1) / s0)]
        while stack:
            l, h = stack.pop(); code = int(codes[pos]); pos += 1
            if code < 253:
                m = 0.5 * (l[code] + h[code]); l2, h2 = l.copy(), h.copy(); l2[code] = m; l1, h1 = l.copy(), h.copy(); h1[code] = m
                stack.append((l2, h2)); stack.append((l1, h1))
                continue
            rec = json.loads(recs.readline())
            c = 0.5 * (l + h); r = 0.5 * (h - l)
            pa, rot = ch.boxes(c, r); pa0, rot0 = ch.boxes(c, 0 * r)
            for st, w in zip(rec['S'], rec['w']):
                v = [int(g) for g in st['v']]; mm = len(v)
                if st['m'] != 'fan' or float(w) == 0 or mm < 5 or mm % 2 == 0:
                    continue
                res['fans'] += 1
                if not ch.fan_ok(v, st['z'], pa, rot):
                    res['original_rejected'] += 1
                star = [v[(2 * j) % mm] for j in range(mm)]
                za = [wc.A(st['z'][0]), wc.A(st['z'][1])]
                X = [ch.placed(g, pa0, rot0) for g in star]
                tot = arb(0); allpos = True
                for j in range(mm):
                    x = [X[j][0] - za[0], X[j][1] - za[1]]; y = [X[(j + 1) % mm][0] - za[0], X[(j + 1) % mm][1] - za[1]]
                    d = wc.det(x, y); allpos = allpos and bool(d > 0)
                    tot += arb.atan2(d, x[0] * y[0] + x[1] * y[1])
                if not allpos:
                    res['star_with_nonpositive_det'] += 1
                    continue
                res['star_all_positive'] += 1
                res['angle_sums_over_pi'].append(round(float((tot / wc.PI).mid()), 6))
                if not ch.fan_ok(star, st['z'], pa0, rot0):
                    res['star_rejected'] += 1
res['angle_sums_over_pi'] = sorted(set(res['angle_sums_over_pi']))[:10]
res['ok'] = (res['star_all_positive'] > 0 and res['star_rejected'] == res['star_all_positive'] and res['original_rejected'] == 0)
print(json.dumps(res))
sys.exit(0 if res['ok'] else 1)
