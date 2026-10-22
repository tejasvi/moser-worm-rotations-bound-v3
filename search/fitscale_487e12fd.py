#!/usr/bin/env python3
"""Hardest unit arcs for a fixed convex polygon H: minimise s*(arc) = the largest s such that a rigid copy (or mirror
copy) of s*arc fits in H. s* < 1 means the arc does not fit, so adding it to the family must raise the minimum.

  fitscale.py HFILE NSEG SEED NRUNS OUT
"""
import sys, json, time
import numpy as np
from scipy.optimize import linprog, minimize
sys.path.insert(0, '.')
from worm import arc_from_turns


def halfplanes(H):
    """H CCW vertices -> (N, b) with N y <= b."""
    E = np.roll(H, -1, axis=0) - H
    N = np.stack([E[:, 1], -E[:, 0]], axis=1)
    N /= np.linalg.norm(N, axis=1)[:, None]
    b = np.sum(N * H, axis=1)
    return N, b


def smax_phi(N, b, V, phi):
    c, s = np.cos(phi), np.sin(phi)
    RV = V @ np.array([[c, s], [-s, c]])  # rows R(phi) v
    # constraints: N_k . t + s * (N_k . R v_j) <= b_k
    A = np.zeros((len(N) * len(V), 3)); rhs = np.zeros(len(N) * len(V))
    q = 0
    for k in range(len(N)):
        A[q:q + len(V), 0] = N[k, 0]; A[q:q + len(V), 1] = N[k, 1]
        A[q:q + len(V), 2] = RV @ N[k]
        rhs[q:q + len(V)] = b[k]
        q += len(V)
    res = linprog([0, 0, -1.0], A_ub=A, b_ub=rhs, bounds=[(None, None), (None, None), (0, None)], method='highs')
    return -res.fun if res.status == 0 else 0.0


def sstar(H, arc, ngrid=120, refine=3):
    N, b = halfplanes(H)
    best = 0.0
    for refl in (0, 1):
        V = arc.copy()
        if refl:
            V[:, 1] = -V[:, 1]
        V = V - V.mean(axis=0)
        phis = np.linspace(0, 2 * np.pi, ngrid, endpoint=False)
        vals = np.array([smax_phi(N, b, V, p) for p in phis])
        for i in np.argsort(-vals)[:refine]:
            lo, hi = phis[i] - 2 * np.pi / ngrid, phis[i] + 2 * np.pi / ngrid
            for _ in range(30):  # golden section
                m1 = hi - 0.618 * (hi - lo); m2 = lo + 0.618 * (hi - lo)
                if smax_phi(N, b, V, m1) > smax_phi(N, b, V, m2):
                    hi = m2
                else:
                    lo = m1
            best = max(best, smax_phi(N, b, V, 0.5 * (lo + hi)), vals[i])
    return best


def shape(z, nseg):
    w = np.exp(z[:nseg]); w /= w.sum()
    turns = np.pi * np.tanh(z[nseg:])
    return arc_from_turns(w, turns)


if __name__ == "__main__":
    hfile, nseg, seed, nruns, out = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), sys.argv[5]
    H = np.array(json.load(open(hfile))["H"])
    rng = np.random.default_rng(seed)
    for run in range(nruns):
        z0 = np.r_[rng.normal(0, 0.5, nseg), rng.normal(0, 1.0, nseg - 1)]
        t0 = time.time()
        res = minimize(lambda z: sstar(H, shape(z, nseg), ngrid=72, refine=2), z0, method='Nelder-Mead',
                       options={'maxfev': 400, 'xatol': 1e-5, 'fatol': 1e-8})
        arc = shape(res.x, nseg)
        s_check = sstar(H, arc, ngrid=720, refine=6)
        rec = {"run": run, "nseg": nseg, "s_nm": res.fun, "s_check": s_check, "z": list(map(float, res.x)),
               "arc": arc.tolist(), "secs": time.time() - t0}
        print(json.dumps(rec), flush=True)
        with open(out, "a") as f:
            f.write(json.dumps(rec) + "\n")
