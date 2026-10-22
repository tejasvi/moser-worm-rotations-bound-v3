"""Robust global minimum of the joint hull area for Keller's arcs plus extra arcs (proper motions only)."""
import sys, json, glob
import numpy as np
sys.path.insert(0, '.')
from worm import Fam, keller, _points, _hull
from run5b import best_pose

_POOL = None
def pool():
    global _POOL
    if _POOL is None:
        _POOL = {}
        for f in sorted(glob.glob('pool_s*.jsonl')):
            for l in open(f):
                r = json.loads(l); k = round(r['A'], 8)
                if k not in _POOL:
                    _POOL[k] = np.array(r['x'])
    return _POOL

def fammin(extra, refls, seed=0, nrandom=16, hops=30, base=None, pool_max=0.2460):
    rng = np.random.default_rng(seed)
    base = base if base is not None else keller()
    nb = len(base)
    fam = Fam(base + extra, refl=[0] * nb + list(refls))
    fam4 = Fam(base)
    found = []
    nE = len(extra)
    Vex = [fam.V[fam.aidx == nb + e] for e in range(nE)]
    for k, x4 in sorted(pool().items()):
        if k > pool_max or len(x4) != fam4.n:
            continue
        P = _points(fam4.V, fam4.aidx, x4); H = P[_hull(P)]
        xe = []
        for e in range(nE):
            s, phi, t = best_pose(H, Vex[e], ngrid=90)
            xe += [phi, t[0], t[1]]
        x, A = fam.local_min(np.r_[x4, xe], r0=0.02, rng=rng)
        found.append((A, x))
    for i in range(nrandom):
        x, A = fam.local_min(fam.random_x(rng), r0=0.05, rng=rng)
        found.append((A, x))
    found.sort(key=lambda r: r[0])
    best = found[0]
    for it in range(hops):
        xp = best[1].copy()
        a = rng.integers(0, len(fam.arcs) - 1)
        xp[3 * a:3 * a + 3] += rng.normal(0, [0.4, 0.06, 0.06])
        x, A = fam.local_min(xp, r0=0.02, rng=rng)
        if A < best[0] - 1e-13:
            best = (A, x)
    return best[0], best[1], sorted(a for a, _ in found)[:6]

def zarc(a, th, sign=+1):
    """Centrally symmetric Z: ends a, middle 1-2a, directions 0, sign*th, 0."""
    m = 1 - 2 * a
    return np.array([[0, 0], [a, 0], [a + m * np.cos(th), sign * m * np.sin(th)], [2 * a + m * np.cos(th), sign * m * np.sin(th)]])
