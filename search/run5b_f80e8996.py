#!/usr/bin/env python3
"""Global minimum of the joint hull area for Keller's four arcs plus extra arcs (fixed chirality, proper motions).

  run5b.py ARCSJSON REFLS SEED NRANDOM OUT
REFLS: comma list of 0/1 per extra arc. Starts: every distinct pool configuration (pool_s*.jsonl) with each extra arc at
its best-fit pose in that configuration's hull, then NRANDOM random starts, then basin hopping from the best.
"""
import sys, json, time, glob
import numpy as np
from scipy.optimize import linprog
sys.path.insert(0, '.')
from worm import Fam, keller, _points, _hull
from fitscale import halfplanes


def best_pose(H, V, ngrid=180):
    """Largest s with t + s R(phi) V inside H; returns (s, phi, t)."""
    N, b = halfplanes(H)
    best = (-1, 0.0, np.zeros(2))
    for phi in np.linspace(0, 2 * np.pi, ngrid, endpoint=False):
        c, s = np.cos(phi), np.sin(phi)
        RV = V @ np.array([[c, s], [-s, c]])
        A = np.vstack([np.c_[np.tile(N[k], (len(V), 1)), RV @ N[k]] for k in range(len(N))])
        rhs = np.repeat(b, len(V))
        res = linprog([0, 0, -1.0], A_ub=A, b_ub=rhs, bounds=[(None, None), (None, None), (0, None)], method='highs')
        if res.status == 0 and -res.fun > best[0]:
            best = (-res.fun, phi, res.x[:2].copy())
    return best


if __name__ == "__main__":
    extra = [np.array(a) for a in json.load(open(sys.argv[1]))]
    refls = [int(v) for v in sys.argv[2].split(',')]
    seed, nrandom, out = int(sys.argv[3]), int(sys.argv[4]), sys.argv[5]
    rng = np.random.default_rng(seed)
    fam = Fam(keller() + extra, refl=[0, 0, 0, 0] + refls)
    fam4 = Fam(keller())
    pool = {}
    for f in sorted(glob.glob('pool_s*.jsonl')):
        for l in open(f):
            r = json.loads(l)
            k = round(r['A'], 8)
            if k not in pool:
                pool[k] = np.array(r['x'])
    nE = len(extra)
    Vex = [fam.V[fam.aidx == 4 + e] for e in range(nE)]
    t0 = time.time()
    found = []
    for k in sorted(pool):
        x4 = pool[k]
        P = _points(fam4.V, fam4.aidx, x4); H = P[_hull(P)]
        xe = []
        for e in range(nE):
            s, phi, t = best_pose(H, Vex[e])
            xe += [phi, t[0], t[1]]
        x, A = fam.local_min(np.r_[x4, xe], r0=0.02, rng=rng)
        found.append((A, x, f"pool {k}"))
    for i in range(nrandom):
        x, A = fam.local_min(fam.random_x(rng), r0=0.05, rng=rng)
        found.append((A, x, f"random {i}"))
    found.sort(key=lambda r: r[0])
    best = (found[0][0], found[0][1])
    for it in range(60):
        xp = best[1].copy()
        a = rng.integers(0, len(fam.arcs) - 1)
        xp[3 * a:3 * a + 3] += rng.normal(0, [0.4, 0.06, 0.06])
        x, A = fam.local_min(xp, r0=0.02, rng=rng)
        if A < best[0] - 1e-13:
            best = (A, x)
    rec = {"refls": refls, "best": best[0], "x": list(map(float, best[1])),
           "top": [(float(a), lab) for a, _, lab in found[:12]], "secs": time.time() - t0}
    print(json.dumps(rec), flush=True)
    json.dump(rec, open(out, "w"))
