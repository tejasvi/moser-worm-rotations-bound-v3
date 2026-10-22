#!/usr/bin/env python3
"""Moser worm (13a) finite-family exploration (float, numerical only).

A family is a list of unit polygonal arcs (vertex arrays). Arc 0 is placed as given; arc a >= 1 is placed by
x[3(a-1):3a] = (phi, tx, ty): p = t + R(phi) (v - centre_a). The joint hull area A(x) is minimised over x by a
trust-region SLP on the structures (hull vertex sequences) seen near x; global minimum by multistart.
"""
import sys, time, json
import numpy as np
import numba as nb
from scipy.optimize import linprog

S3 = np.sqrt(3.0)


def keller():
    L = np.array([[-0.5, 0.0], [0.5, 0.0]])
    T = np.array([[-0.25, 0.0], [0.0, S3 / 4], [0.25, 0.0]])
    b = 11 * np.pi / 24
    U = np.array([[0.0, 0.0]] + [[sum(np.cos(r * b) for r in range(j)) / 3, sum(np.sin(r * b) for r in range(j)) / 3]
                                 for j in (1, 2, 3)])
    t = np.sqrt(8745) / 1024
    C = np.array([[0, 0], [7 / 128, t], [105 / 128, -t], [7 / 8, 0]])
    return [L, T, U, C]


def arc_from_turns(lengths, turns):
    """Polygonal arc with given segment lengths and turning angles (len(turns) = len(lengths) - 1)."""
    pts = [np.zeros(2)]
    ang = 0.0
    for k, l in enumerate(lengths):
        if k:
            ang += turns[k - 1]
        pts.append(pts[-1] + l * np.array([np.cos(ang), np.sin(ang)]))
    return np.array(pts)


def arclen(V):
    return float(np.sum(np.hypot(*np.diff(V, axis=0).T)))


@nb.njit(cache=True)
def _points(V, aidx, x):
    n = V.shape[0]
    P = np.empty((n, 2))
    for i in range(n):
        a = aidx[i]
        if a == 0:
            P[i, 0] = V[i, 0]; P[i, 1] = V[i, 1]
        else:
            ph = x[3 * (a - 1)]; c = np.cos(ph); s = np.sin(ph)
            P[i, 0] = x[3 * (a - 1) + 1] + c * V[i, 0] - s * V[i, 1]
            P[i, 1] = x[3 * (a - 1) + 2] + s * V[i, 0] + c * V[i, 1]
    return P


@nb.njit(cache=True)
def _cross(o0, o1, a0, a1, b0, b1):
    return (a0 - o0) * (b1 - o1) - (a1 - o1) * (b0 - o0)


@nb.njit(cache=True)
def _hull(P):
    """Andrew monotone chain; CCW vertex indices, collinear points dropped."""
    n = P.shape[0]
    key = P[:, 0] * 1.0
    order = np.argsort(key, kind='mergesort')
    # tie-break on y for equal x (stable insertion pass)
    for i in range(1, n):
        j = i
        while j > 0 and P[order[j - 1], 0] == P[order[j], 0] and P[order[j - 1], 1] > P[order[j], 1]:
            tmp = order[j - 1]; order[j - 1] = order[j]; order[j] = tmp
            j -= 1
    H = np.empty(2 * n + 1, dtype=np.int64)
    k = 0
    for ii in range(n):
        i = order[ii]
        while k >= 2 and _cross(P[H[k - 2], 0], P[H[k - 2], 1], P[H[k - 1], 0], P[H[k - 1], 1], P[i, 0], P[i, 1]) <= 0:
            k -= 1
        H[k] = i; k += 1
    t = k + 1
    for ii in range(n - 2, -1, -1):
        i = order[ii]
        while k >= t and _cross(P[H[k - 2], 0], P[H[k - 2], 1], P[H[k - 1], 0], P[H[k - 1], 1], P[i, 0], P[i, 1]) <= 0:
            k -= 1
        H[k] = i; k += 1
    return H[:k - 1].copy()


@nb.njit(cache=True)
def _area(P, S):
    m = S.shape[0]
    a = 0.0
    for k in range(m):
        i = S[k]; j = S[(k + 1) % m]
        a += P[i, 0] * P[j, 1] - P[i, 1] * P[j, 0]
    return 0.5 * a


@nb.njit(cache=True)
def _area_grad(V, aidx, x, S):
    P = _points(V, aidx, x)
    m = S.shape[0]
    g = np.zeros(x.shape[0])
    a = 0.0
    for k in range(m):
        i = S[k]; j = S[(k + 1) % m]; h = S[(k - 1) % m]
        a += P[i, 0] * P[j, 1] - P[i, 1] * P[j, 0]
        gx = 0.5 * (P[j, 1] - P[h, 1]); gy = 0.5 * (P[h, 0] - P[j, 0])
        ar = aidx[i]
        if ar > 0:
            b = 3 * (ar - 1)
            rx = P[i, 0] - x[b + 1]; ry = P[i, 1] - x[b + 2]
            g[b] += gx * (-ry) + gy * rx
            g[b + 1] += gx
            g[b + 2] += gy
    return 0.5 * a, g


class Fam:
    def __init__(self, arcs, refl=None, center=True):
        arcs = [np.asarray(A, float) for A in arcs]
        refl = refl or [0] * len(arcs)
        Vs, ai = [], []
        for a, A in enumerate(arcs):
            B = A.copy()
            if refl[a]:
                B[:, 1] = -B[:, 1]
            if a > 0 and center:
                B = B - B.mean(axis=0)
            Vs.append(B); ai += [a] * len(B)
        self.arcs = arcs
        self.V = np.vstack(Vs)
        self.aidx = np.array(ai, dtype=np.int64)
        self.n = 3 * (len(arcs) - 1)

    def area(self, x):
        P = _points(self.V, self.aidx, x)
        return _area(P, _hull(P))

    def struct(self, x):
        return _hull(_points(self.V, self.aidx, x))

    def local_min(self, x0, r0=0.05, iters=3000, nsamp=16, rng=None, tol=1e-12):
        """Trust-region SLP on the max of the shoelace pieces seen near x. A rejected trial point adds its
        own structures (cutting planes) before the radius shrinks."""
        rng = rng or np.random.default_rng(0)
        n = self.n
        x = np.array(x0, float); A = self.area(x); r = r0
        c = np.r_[np.zeros(n), 1.0]
        structs = None
        for it in range(iters):
            if structs is None:
                structs = {tuple(self.struct(x))}
                for _ in range(nsamp):
                    structs.add(tuple(self.struct(x + r * rng.uniform(-1, 1, n))))
            rows, rhs = [], []
            for S in structs:
                a, g = _area_grad(self.V, self.aidx, x, np.array(S, dtype=np.int64))
                rows.append(np.r_[g, -1.0]); rhs.append(-a)
            res = linprog(c, A_ub=np.array(rows), b_ub=np.array(rhs), bounds=[(-r, r)] * n + [(None, None)],
                          method='highs')
            if res.status != 0:
                r *= 0.25; structs = None
                if r < tol:
                    break
                continue
            d = res.x[:n]; pred = A - res.x[n]
            if pred <= 1e-15:
                r *= 0.25; structs = None
                if r < tol:
                    break
                continue
            An = self.area(x + d)
            if A - An >= 0.1 * pred:
                x = x + d; A = An; structs = None
                if np.max(np.abs(d)) > 0.9 * r:
                    r = min(2 * r, 0.3)
            else:
                new = {tuple(self.struct(x + f * d)) for f in (1.0, 0.5, 0.25, 0.1)} - structs
                if new:
                    structs |= new
                else:
                    r *= 0.25; structs = None
                    if r < tol:
                        break
        return x, A

    def random_x(self, rng, X=0.61, Y=0.48):
        k = len(self.arcs) - 1
        x = np.empty(self.n)
        for a in range(k):
            x[3 * a] = rng.uniform(0, 2 * np.pi)
            x[3 * a + 1] = rng.uniform(-X, X)
            x[3 * a + 2] = rng.uniform(-Y, Y)
        return x

    def global_min(self, starts=100, seed=0, verbose=False, pre_r=0.05):
        rng = np.random.default_rng(seed)
        best = (np.inf, None)
        vals = []
        for s in range(starts):
            x0 = self.random_x(rng)
            x, A = self.local_min(x0, r0=pre_r, rng=rng)
            vals.append(A)
            if A < best[0]:
                best = (A, x)
                if verbose:
                    print(f"  start {s}: {A:.9f}", flush=True)
        return best, np.array(vals)


if __name__ == "__main__":
    fam = Fam(keller())
    for A in fam.arcs:
        print("arc length", arclen(A))
    t0 = time.time()
    (A, x), vals = fam.global_min(starts=int(sys.argv[1]) if len(sys.argv) > 1 else 20, verbose=True)
    print("best", A, "time", time.time() - t0)
    print("x", list(x))
    print("sorted vals", np.sort(vals)[:10])
