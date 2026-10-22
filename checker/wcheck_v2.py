#!/usr/bin/env python3
"""Checker for the worm (Moser 13a, rotation-only M+) lower-bound certificate written by wsearch.py.
Interval arithmetic: python-flint arb. Does not import the search code. Everything the proof uses is re-derived here
from the exact arc data in the header (the lemmas of Sections 2 and 3 of the paper):
  root   the root box covers D_tau (Lemma W1), and the family has the symmetries W1 uses;
  tree   DFS preorder codes (0..dim-1 split, lower half first; 254 single-structure leaf; 253 Lemma K leaf), every leaf
         box exactly c +- h (Fraction test), all parts present, no truncated or trailing data;
  leaf   every structure valid on the leaf box: "fan" (W3: det(x_j - z, x_{j+1} - z) > 0 on the box, winding 1 at the
         centre), "small" (W4: <= maxsmall <= 4 points), "chord" (W5 cuts; pieces small or a fan from one of their
         vertices, Keller Lemma 3.4); Taylor bound (W6) F(c) - sum|g|h - e2 with e2 = -q/2 + h^T W h/2, q from H(c)
         (the bound Lambda_2 of the paper, or the certified eigenvalue bounds Lambda_1, Lambda_3), W = entrywise bound
         of |Hess(p) - Hess(c)| on the box, summed from the variation bounds of the paper (Lemma 3.8) over the run
         and transition terms; Lemma K (W7) with the weights normalised in arb. q is rounded to double precision
         (see "Rounding of Lambda" in Section 4.3 of the paper).
Usage: wcheck.py CERTDIR PART [PART ...]   |   wcheck.py CERTDIR present   |   wcheck.py --selftest
"""
import sys, os, json, gzip, hashlib
from fractions import Fraction as Fr
if not __debug__:
    raise SystemExit('wcheck.py uses assert statements; run it without -O')
import numpy as np
from flint import arb, ctx
ctx.prec = 100

PI = arb.pi()
ZERO = arb(0)


def A(x):
    """exact arb from a float, int, str (decimal or p/q) or Fraction."""
    if isinstance(x, arb):
        return x
    if isinstance(x, float):
        return arb(Fr(x).numerator) / arb(Fr(x).denominator)
    f = Fr(x)
    return arb(f.numerator) / arb(f.denominator)


def det(a, b):
    return a[0] * b[1] - a[1] * b[0]


def safe_sqrt(x):
    """sqrt of a ball known to enclose a NONNEGATIVE quantity (a sum of squares): a ball straddling 0 would give nan,
    so it is replaced by [0, sqrt(upper)] (an enclosure of the true value)."""
    if x > 0:
        return x.sqrt()
    u = float(x.upper())
    if not u > 0:
        return ZERO
    s = float(arb(u).sqrt().upper()) * (1 + 1e-12) + 1e-300
    return arb(s / 2, s / 2)


def lower(x):
    return float(x.lower())


def upper(x):
    return float(x.upper())


# ---------------------------------------------------------------- family -------------------------------------------
class Family:
    def __init__(self, famspec, gid_map):
        self.famspec = famspec
        self.arcs = famspec['arcs']
        self.k = len(self.arcs) - 1
        self.dim = 3 * self.k
        self.periods = famspec['periods']
        V = []
        for arc in self.arcs:
            s = [A(arc['start'][0]), A(arc['start'][1])]
            pts = [s]
            for l, d in zip(arc['lengths'], arc['dirs_deg']):
                ang = PI * A(d) / 180
                pts.append([pts[-1][0] + A(l) * ang.cos(), pts[-1][1] + A(l) * ang.sin()])
            V.append(pts)
        self.V = V
        # material points q_g (body frame, centred at the mean of all polyline vertices for bodies >= 1)
        self.gb = []; self.q = []
        for b, j in gid_map:
            if b == 0:
                self.q.append(V[0][j])
            else:
                n = len(V[b])
                cx = sum((p[0] for p in V[b]), ZERO) / n; cy = sum((p[1] for p in V[b]), ZERO) / n
                self.q.append([V[b][j][0] - cx, V[b][j][1] - cy])
            self.gb.append(b)
        self.check_family(gid_map)

    def check_family(self, gid_map):
        arcs = self.arcs
        for arc in arcs:
            assert sum(Fr(l) for l in arc['lengths']) <= 1, 'arc longer than 1'
            assert all(Fr(l) > 0 for l in arc['lengths'])
        L = arcs[0]
        assert [Fr(x) for x in L['start']] == [Fr(-1, 2), 0] and [Fr(x) for x in L['lengths']] == [1] and \
            [Fr(x) for x in L['dirs_deg']] == [0], 'body 0 must be the unit segment centred at 0'
        T = arcs[1]
        assert [Fr(x) for x in T['lengths']] == [Fr(1, 2), Fr(1, 2)] and \
            [Fr(x) for x in T['dirs_deg']] == [60, -60], 'body 1 must be the equilateral two-link worm (side 1/2)'
        assert self.periods[0] == '2/3'
        for i, per in enumerate(self.periods):
            if per == '2':
                continue
            if per == '1':      # parallelogram hull: lengths (a, m, a), directions (d, e, d)
                a = arcs[i + 1]
                ls = [Fr(x) for x in a['lengths']]; ds = [Fr(x) for x in a['dirs_deg']]
                assert len(ls) == 3 and ls[0] == ls[2] and ds[0] == ds[2], 'period-pi body must be a centred Z'
            elif per != '2/3' or i != 0:
                raise AssertionError('unsupported period')
        if self.famspec.get('reflections'):
            # M+-: every body except the one whose mirror is absorbed by the global reflection in the x-axis must be
            # mirror-symmetric: lengths palindromic and d_k + d_{n-1-k} constant (the reflected polyline traversed
            # backwards then coincides with the original up to a rotation and a translation)
            cabs = int(self.famspec['mirror_absorbed_by_global_reflection'])
            assert 1 <= cabs <= self.k and self.periods[cabs - 1] == '1', 'absorbed body must be a centred Z'
            for b in range(1, self.k + 1):
                if b == cabs:
                    continue
                ls = [Fr(x) for x in arcs[b]['lengths']]; ds = [Fr(x) for x in arcs[b]['dirs_deg']]
                n = len(ls)
                assert all(ls[k] == ls[n - 1 - k] for k in range(n)), f'body {b} lengths not palindromic'
                sums = {(ds[k] + ds[n - 1 - k]) % 360 for k in range(n)}
                assert len(sums) == 1, f'body {b} is not mirror-symmetric'
        seen = set()
        for b, j in gid_map:
            assert 0 <= b <= self.k and 0 <= j < len(self.V[b]) and (b, j) not in seen
            seen.add((b, j))
        for b in range(self.k + 1):
            assert all((b, j) in seen for j in range(len(self.V[b]))), 'every polyline vertex must be listed'

    def pidx(self, b):
        return 3 * (b - 1), 3 * (b - 1) + 1, 3 * (b - 1) + 2

    def vertex(self, g, P):
        """position, first derivatives {param: vec}, second derivatives {(k, k): vec} of vertex g at parameters P
        (list of arb: exact values or balls)."""
        b = self.gb[g]; q = self.q[g]
        if b == 0:
            return q, {}, {}
        ir, ix, iy = self.pidx(b)
        c, s = P[ir].cos(), P[ir].sin()
        Rq = [c * q[0] - s * q[1], s * q[0] + c * q[1]]
        x = [P[ix] + Rq[0], P[iy] + Rq[1]]
        d1 = {ir: [-Rq[1], Rq[0]], ix: [arb(1), ZERO], iy: [ZERO, arb(1)]}
        d2 = {(ir, ir): [-Rq[0], -Rq[1]]}
        return x, d1, d2

    def diff(self, g1, g2, P):
        """x_{g2} - x_{g1} with the same-body correlation kept (exact rotation of q2 - q1)."""
        b1, b2 = self.gb[g1], self.gb[g2]
        if b1 == b2 and b1 != 0:
            ir = self.pidx(b1)[0]
            c, s = P[ir].cos(), P[ir].sin()
            dq = [self.q[g2][0] - self.q[g1][0], self.q[g2][1] - self.q[g1][1]]
            return [c * dq[0] - s * dq[1], s * dq[0] + c * dq[1]]
        x1 = self.vertex(g1, P)[0]; x2 = self.vertex(g2, P)[0]
        return [x2[0] - x1[0], x2[1] - x1[1]]

    def model(self, lst, P, want_hess=True):
        """F, gradient, Hessian of F = 1/2 sum det(x_j, x_{j+1}) over the cyclic list at parameters P.
        Not called by the checker: taylor() computes F, its gradient and Hessian through the run identity."""
        d = self.dim
        F = ZERO; g = [ZERO] * d
        H = [[ZERO] * d for _ in range(d)] if want_hess else None
        data = [self.vertex(gid, P) for gid in lst]
        m = len(lst)
        for j in range(m):
            xa, da, dda = data[j]; xb, db, ddb = data[(j + 1) % m]
            F += det(xa, xb)
            for k, v in da.items():
                g[k] += det(v, xb)
            for k, v in db.items():
                g[k] += det(xa, v)
            if want_hess:
                for (k, l), v in dda.items():
                    H[k][l] += det(v, xb)
                for (k, l), v in ddb.items():
                    H[k][l] += det(xa, v)
                for k, va in da.items():
                    for l, vb in db.items():
                        t = det(va, vb)
                        H[k][l] += t; H[l][k] += t
        F = F / 2; g = [x / 2 for x in g]
        if want_hess:
            H = [[x / 2 for x in row] for row in H]
        return F, g, H


# ---------------------------------------------------------------- linear algebra -----------------------------------
def certified_min_eig(M):
    """a float lam with lambda_min(M) >= lam certified by an arb LDL^T of M - lam I (None if it fails)."""
    n = len(M)
    Mf = np.array([[float(M[i][j].mid()) for j in range(n)] for i in range(n)])
    lam = float(np.linalg.eigvalsh(0.5 * (Mf + Mf.T))[0])
    lam = lam - 1e-9 * (1 + abs(lam)) - 1e-12
    S = [[M[i][j] - (A(lam) if i == j else ZERO) for j in range(n)] for i in range(n)]
    Dg = []
    Lm = [[ZERO] * n for _ in range(n)]
    for i in range(n):
        s = S[i][i] - sum((Lm[i][k] * Lm[i][k] * Dg[k] for k in range(i)), ZERO)
        if not s > 0:
            return None
        Dg.append(s)
        for r in range(i + 1, n):
            t = S[r][i] - sum((Lm[r][k] * Lm[i][k] * Dg[k] for k in range(i)), ZERO)
            Lm[r][i] = t / s
    return lam


# ---------------------------------------------------------------- checker ------------------------------------------
class Checker:
    def __init__(self, meta):
        self.fam = Family(meta['famspec'], meta['gid_map'])
        self.tau = A(repr(float(meta['tau'])))
        self.maxsmall = int(meta['maxsmall'])
        assert 0 <= self.maxsmall <= 4, 'lists of 5 or more points need a proof not included here'
        self.min_margin = None

    def box_arb(self, c, h):
        """per body: (phi_c, phi_rad, (t_cx, t_cy), t_rad) in arb (t_rad = Euclidean radius of the translation box)."""
        out = [(ZERO, ZERO, (ZERO, ZERO), ZERO)]
        for b in range(1, self.fam.k + 1):
            ir, ix, iy = self.fam.pidx(b)
            out.append((A(float(c[ir])), A(float(h[ir])), (A(float(c[ix])), A(float(c[iy]))),
                        (A(float(h[ix])) ** 2 + A(float(h[iy])) ** 2).sqrt()))
        return out

    def boxes(self, c, h):
        pa = self.box_arb(c, h)
        rot = [(x[0].cos(), x[0].sin()) for x in pa]
        return pa, rot

    def placed(self, g, pa, rot):
        """position of vertex g at the box centre (arb)."""
        b = self.fam.gb[g]; q = self.fam.q[g]
        if b == 0:
            return q
        cs, sn = rot[b]; t = pa[b][2]
        return [cs * q[0] - sn * q[1] + t[0], sn * q[0] + cs * q[1] + t[1]]

    def move(self, g, pa):
        """upper bound of |x_g(p) - x_g(c)| on the box: |q| phi_rad + t_rad (|R(phi) - R(phi_c)| <= |phi - phi_c|)."""
        b = self.fam.gb[g]
        if b == 0:
            return ZERO
        q = self.fam.q[g]
        return safe_sqrt(q[0] * q[0] + q[1] * q[1]) * pa[b][1] + pa[b][3]

    @staticmethod
    def nrm(v):
        return safe_sqrt(v[0] * v[0] + v[1] * v[1])

    def det3(self, a, b, i, pa, rot):
        """enclosure-type bounds (lo, hi) of det(x_b - x_a, x_i - x_a) over the box: centre value -+ the movement
        error e_ab |v| + e_ai |u| + e_ab e_ai (zero when all three vertices are on one body: det is rotation invariant)."""
        fam = self.fam
        Xa, Xb, Xi = self.placed(a, pa, rot), self.placed(b, pa, rot), self.placed(i, pa, rot)
        u = [Xb[0] - Xa[0], Xb[1] - Xa[1]]; v = [Xi[0] - Xa[0], Xi[1] - Xa[1]]
        d0 = det(u, v)
        if fam.gb[a] == fam.gb[b] == fam.gb[i]:
            return d0, d0
        eab = self.pair_move(a, b, pa); eai = self.pair_move(a, i, pa)
        err = eab * self.nrm(v) + eai * self.nrm(u) + eab * eai
        return d0 - err, d0 + err

    def pair_move(self, a, b, pa):
        """upper bound of |(x_b - x_a)(p) - (x_b - x_a)(c)| on the box."""
        fam = self.fam
        if fam.gb[a] == fam.gb[b]:
            if fam.gb[a] == 0:
                return ZERO
            dq = [fam.q[b][0] - fam.q[a][0], fam.q[b][1] - fam.q[a][1]]
            return self.nrm(dq) * pa[fam.gb[a]][1]
        return self.move(a, pa) + self.move(b, pa)

    # --- validity ---
    def fan_ok(self, lst, z, pa, rot):
        """Lemma W3 on the box: det(x_j - z, x_{j+1} - z) > 0 for every consecutive pair (centre value minus the
        movement error), and winding 1 at the centre."""
        fam = self.fam; m = len(lst)
        if m < 3:
            return False
        za = [A(z[0]), A(z[1])]
        X = [self.placed(g, pa, rot) for g in lst]
        tot = ZERO
        for j in range(m):
            a, b = lst[j], lst[(j + 1) % m]
            x = [X[j][0] - za[0], X[j][1] - za[1]]; y = [X[(j + 1) % m][0] - za[0], X[(j + 1) % m][1] - za[1]]
            d0 = det(x, y)
            ba, bb = fam.gb[a], fam.gb[b]
            if ba == bb:
                if ba == 0:
                    var = ZERO
                else:
                    # det(x_a - z, x_b - z) = det(q_a, q_b - q_a) + det(t - z, R(phi)(q_b - q_a)): only the second term
                    # moves, by at most |q_b - q_a| (t_rad (1 + phi_rad) + |t_c - z| phi_rad)
                    rr, tr = pa[ba][1], pa[ba][3]
                    w = self.nrm([fam.q[b][0] - fam.q[a][0], fam.q[b][1] - fam.q[a][1]])
                    tz = self.nrm([pa[ba][2][0] - za[0], pa[ba][2][1] - za[1]])
                    var = w * (tr * (1 + rr) + tz * rr)
            else:
                dx = self.move(a, pa); dy = self.move(b, pa)
                var = dx * (self.nrm(y) + dy) + self.nrm(x) * dy
            if not (d0 - var > 0):
                return False
            tot += arb.atan2(d0, x[0] * y[0] + x[1] * y[1])
        return bool(abs(tot - 2 * PI) < 1)

    def vertex_fan_ok(self, piece, r, pa, rot):
        """Keller Lemma 3.4 for the piece rotated to start at position r."""
        m = len(piece)
        l = piece[r:] + piece[:r]
        for i in range(2, m):
            if not self.det3(l[0], l[1], l[i], pa, rot)[0] > 0:
                return False
        for i in range(2, m - 1):
            if not self.det3(l[0], l[i], l[i + 1], pa, rot)[0] > 0:
                return False
        return True

    def chord_ok(self, piece, tree, pa, rot, depth=0):
        if depth > 64:
            return False
        n = len(piece)
        if tree[0] == 's':
            return n <= self.maxsmall
        if tree[0] == 'f':
            r = int(tree[1])
            return 0 <= r < n and n >= 3 and self.vertex_fan_ok(piece, r, pa, rot)
        if tree[0] != 'c':
            return False
        s, t = int(tree[1]), int(tree[2])
        if not (0 <= s < n and 0 <= t < n):
            return False
        dd = (t - s) % n
        if not (2 <= dd <= n - 2):
            return False
        ps, pt = piece[s], piece[t]
        Xs, Xt = self.placed(ps, pa, rot), self.placed(pt, pa, rot)
        if not (self.nrm([Xt[0] - Xs[0], Xt[1] - Xs[1]]) - self.pair_move(ps, pt, pa) > 0):
            return False                                   # P_s != P_t on the box
        for k in range(1, dd):                             # strictly between s and t: closed right half-plane
            if not self.det3(ps, pt, piece[(s + k) % n], pa, rot)[1] <= 0:
                return False
        for k in range(1, n - dd):                         # strictly between t and s: closed left half-plane
            if not self.det3(ps, pt, piece[(t + k) % n], pa, rot)[0] >= 0:
                return False
        p1 = [piece[(s + k) % n] for k in range(0, dd + 1)]
        p2 = [piece[(t + k) % n] for k in range(0, n - dd + 1)]
        return self.chord_ok(p1, tree[3], pa, rot, depth + 1) and self.chord_ok(p2, tree[4], pa, rot, depth + 1)

    def struct_ok(self, st, pa, rot):
        lst = [int(g) for g in st['v']]
        if any(g < 0 or g >= len(self.fam.gb) for g in lst) or len(set(lst)) != len(lst):
            return False
        mth = st['m']
        if mth == 'small':
            return len(lst) <= self.maxsmall
        if mth == 'fan':
            return self.fan_ok(lst, st['z'], pa, rot)
        if mth == 'chord':
            return self.chord_ok(lst, st['t'], pa, rot)
        return False

    # --- Taylor model of one structure on the box (Taylor bound and variation bounds of the paper) ---
    def taylor(self, lst, h, pa, rot):
        fam = self.fam; d = fam.dim; n = len(lst)
        half = arb(1) / 2
        F = ZERO; g = [ZERO] * d
        Hm = [[ZERO] * d for _ in range(d)]; Wm = [[ZERO] * d for _ in range(d)]

        def add(M, k, l, v):
            M[k][l] += v
            if k != l:
                M[l][k] += v

        def rotv(b, v):
            cs, sn = rot[b]
            return [cs * v[0] - sn * v[1], sn * v[0] + cs * v[1]]

        def Jv(v):
            return [-v[1], v[0]]

        ib = [fam.gb[x] for x in lst]; Q = [fam.q[x] for x in lst]
        s0 = 0
        for j in range(n):
            if ib[j] != ib[j - 1]:
                s0 = j; break
        ibr = ib[s0:] + ib[:s0]; Qr = Q[s0:] + Q[:s0]
        runs = []; j = 0
        while j < n:
            jj = j
            while jj + 1 < n and ibr[jj + 1] == ibr[j]:
                jj += 1
            C = ZERO
            for mm in range(j, jj):
                C += Qr[mm][0] * Qr[mm + 1][1] - Qr[mm][1] * Qr[mm + 1][0]
            runs.append((ibr[j], Qr[j], Qr[jj], C)); j = jj + 1
        nr = len(runs)
        for r in range(nr):
            i, qa, qb, C = runs[r]
            F += half * C
            if i != 0:
                ir, ix, iy = fam.pidx(i)
                t = pa[i][2]; w = [qb[0] - qa[0], qb[1] - qa[1]]; Rw = rotv(i, w); RJw = rotv(i, Jv(w))
                F += half * det(t, Rw)
                g[ix] += half * Rw[1]; g[iy] += -half * Rw[0]
                g[ir] += half * det(t, RJw)
                add(Hm, ir, ir, -half * det(t, Rw)); add(Hm, ir, ix, half * RJw[1]); add(Hm, ir, iy, -half * RJw[0])
                rr, tr = pa[i][1], pa[i][3]; nw = self.nrm(w); tn = self.nrm(t)
                add(Wm, ir, ir, half * nw * (tr * (1 + rr) + tn * rr)); add(Wm, ir, ix, half * nw * rr)
                add(Wm, ir, iy, half * nw * rr)
            jb, qn = runs[(r + 1) % nr][0], runs[(r + 1) % nr][1]
            x = rotv(i, qb) if i != 0 else qb
            if i != 0:
                x = [x[0] + pa[i][2][0], x[1] + pa[i][2][1]]
            y = rotv(jb, qn) if jb != 0 else qn
            if jb != 0:
                y = [y[0] + pa[jb][2][0], y[1] + pa[jb][2][1]]
            F += half * det(x, y)
            dxs = {}; dys = {}
            if i != 0:
                ir, ix, iy = fam.pidx(i); dxs[ix] = [arb(1), ZERO]; dxs[iy] = [ZERO, arb(1)]; dxs[ir] = rotv(i, Jv(qb))
            if jb != 0:
                jr, jx, jy = fam.pidx(jb); dys[jx] = [arb(1), ZERO]; dys[jy] = [ZERO, arb(1)]; dys[jr] = rotv(jb, Jv(qn))
            for k, v in dxs.items():
                g[k] += half * det(v, y)
            for k, v in dys.items():
                g[k] += half * det(x, v)
            for k, v in dxs.items():
                for l, v2 in dys.items():
                    add(Hm, k, l, half * det(v, v2))
            ra = ZERO if i == 0 else pa[i][1]; ta = ZERO if i == 0 else pa[i][3]
            rb = ZERO if jb == 0 else pa[jb][1]; tb = ZERO if jb == 0 else pa[jb][3]
            nqa = ZERO if i == 0 else self.nrm(qb); nqb = ZERO if jb == 0 else self.nrm(qn)
            dxa = nqa * ra + ta; dyb = nqb * rb + tb
            if i != 0:
                ir = fam.pidx(i)[0]
                Rqb = rotv(i, qb)
                add(Hm, ir, ir, half * det([-Rqb[0], -Rqb[1]], y))
                add(Wm, ir, ir, half * (nqa * ra * (self.nrm(y) + dyb) + nqa * dyb))
            if jb != 0:
                jr = fam.pidx(jb)[0]
                Rqn = rotv(jb, qn)
                add(Hm, jr, jr, half * det(x, [-Rqn[0], -Rqn[1]]))
                add(Wm, jr, jr, half * (nqb * rb * (self.nrm(x) + dxa) + nqb * dxa))
            if i != 0 and jb != 0:
                add(Wm, fam.pidx(i)[0], fam.pidx(jb)[0], half * nqa * nqb * (ra + rb))
                ir = fam.pidx(i)[0]; jr, jx, jy = fam.pidx(jb)
                add(Wm, ir, jx, half * nqa * ra); add(Wm, ir, jy, half * nqa * ra)
                jr = fam.pidx(jb)[0]; ir, ix, iy = fam.pidx(i)
                add(Wm, ix, jr, half * nqb * rb); add(Wm, iy, jr, half * nqb * rb)
        hA = [A(float(v)) for v in h]
        Wh = ZERO
        for k in range(d):
            for l in range(d):
                Wh += Wm[k][l] * hA[k] * hA[l]
        M = [[Hm[k][l] * hA[k] * hA[l] for l in range(d)] for k in range(d)]
        q2 = ZERO
        for k in range(d):
            mk = M[k][k]
            q2 += mk if mk < 0 else (ZERO if mk >= 0 else arb(min(0.0, lower(mk))))
            for l in range(d):
                if l != k:
                    q2 -= abs(M[k][l])
        qs = [lower(q2)]
        lamH = certified_min_eig(Hm)
        if lamH is not None:
            hh = sum((x * x for x in hA), ZERO)
            qs.append(lower(A(min(0.0, lamH)) * hh))
        lamM = certified_min_eig(M)
        if lamM is not None:
            qs.append(min(0.0, lamM) * sum(1 for v in h if v > 0))
        q = max(qs)
        e2 = -A(q) / 2 + Wh / 2
        return F, g, e2

    def leaf(self, c, h, rec):
        pa, rot = self.boxes(c, h)
        S = rec['S']; w = rec['w']
        if len(S) == 0 or len(S) != len(w):
            return False, 'bad leaf record'
        ws = []
        for x in w:
            x = float(x)
            if not (x >= 0) or x != x:
                return False, 'negative or NaN weight'
            ws.append(x)
        if not sum(ws) > 0:
            return False, 'zero weights'
        models = []
        for st, x in zip(S, ws):
            if x == 0:
                continue                                   # unused structure: not part of the combination
            if not self.struct_ok(st, pa, rot):
                return False, 'invalid structure (%s)' % st.get('m')
            models.append((A(x), self.taylor([int(v) for v in st['v']], h, pa, rot)))
        tot = sum((x for x, _ in models), ZERO)
        val = ZERO
        gs = [ZERO] * self.fam.dim
        for x, (F, g, e2) in models:
            lam = x / tot
            val += lam * (F - e2)
            for k in range(self.fam.dim):
                gs[k] += lam * g[k]
        for k in range(self.fam.dim):
            if h[k] > 0:
                val -= arb(abs(gs[k]).upper()) * A(float(h[k]))
        mg = lower(val - self.tau)
        self.min_margin = mg if self.min_margin is None else min(self.min_margin, mg)
        return bool(val > self.tau), 'L < tau'


def check_root(meta):
    errs = []
    tau = A(repr(float(meta['tau'])))
    lo = [Fr(float(v)) for v in meta['lo']]; hi = [Fr(float(v)) for v in meta['hi']]
    k = len(meta['famspec']['arcs']) - 1
    w = arb(3).sqrt() / 4
    X = 2 * tau / w - A('1/2'); Y = 2 * tau
    for b in range(1, k + 1):
        ir, ix, iy = 3 * (b - 1), 3 * (b - 1) + 1, 3 * (b - 1) + 2
        per = meta['famspec']['periods'][b - 1]
        need = PI / 3 if b == 1 else PI * A(per)
        if not (lo[ir] <= 0 and A(hi[ir]) >= need):
            errs.append(f'rotation range of body {b} too small')
        if not (A(lo[ix]) <= -X and A(hi[ix]) >= X):
            errs.append(f'x-translation range of body {b} too small')
        if not (A(lo[iy]) <= -Y and A(hi[iy]) >= Y):
            errs.append(f'y-translation range of body {b} too small')
    return errs


def check_all_present(certdir, nparts):
    miss = [p for p in range(nparts) if not all(os.path.exists(os.path.join(certdir, f'part{p:04d}{ext}'))
                                                for ext in ('.npy', '.json', '.leaves.jsonl.gz'))]
    return (len(miss) == 0), ('missing parts: %s' % miss[:10] if miss else '')


def exact_box(l, h):
    c = 0.5 * (l + h); r = 0.5 * (h - l)
    ok = all(Fr(float(c[k])) - Fr(float(r[k])) == Fr(float(l[k])) and
             Fr(float(c[k])) + Fr(float(r[k])) == Fr(float(h[k])) for k in range(len(l)))
    return ok, c, r


def check_part(certdir, part, lrange=None):
    """v2: lrange = (A, B) checks only the leaves with DFS leaf index A <= i < B (the whole tree is still replayed and
    its structure, the record count and the header are checked); wcheck_presence_v2.py requires that the passing ranges
    of every part cover [0, leaves) exactly."""
    A, B = lrange if lrange is not None else (0, None)
    meta = json.load(open(os.path.join(certdir, f'part{part:04d}.json')))
    okp, msgp = check_all_present(certdir, int(meta['nparts']))
    partial = os.environ.get('WCHECK_TEST_PARTIAL') == '1'      # tests only: a certificate check never sets it
    distributed = os.environ.get('WCHECK_DISTRIBUTED') == '1'   # presence is then verified by wcheck_presence.py
    shas = {ext: hashlib.sha256(open(os.path.join(certdir, f'part{part:04d}{ext}'), 'rb').read()).hexdigest()
            for ext in ('.npy', '.json', '.leaves.jsonl.gz')}
    if not okp and not partial and not distributed:
        return dict(part=part, ok=False, err='presence: ' + msgp)
    errs = check_root(meta)
    if errs:
        return dict(part=part, ok=False, err='; '.join(errs))
    ch = Checker(meta)
    codes = np.load(os.path.join(certdir, f'part{part:04d}.npy'))
    recs = gzip.open(os.path.join(certdir, f'part{part:04d}.leaves.jsonl.gz'), 'rt')
    lo = np.array(meta['lo']); hi = np.array(meta['hi']); s0 = np.array(meta['split0'])
    cells = list(np.ndindex(*meta['split0']))[part::int(meta['nparts'])]
    d = ch.fam.dim
    pos = 0; nleaf = 0; nfail = 0; fails = []; nchk = 0
    for cell in cells:
        cl = lo + (hi - lo) * np.array(cell) / s0; chh = lo + (hi - lo) * (np.array(cell) + 1) / s0
        stack = [(cl, chh)]
        while stack:
            l, h = stack.pop()
            if pos >= len(codes):
                return dict(part=part, ok=False, err='certificate truncated')
            code = int(codes[pos]); pos += 1
            if code in (253, 254):
                line = recs.readline()
                if not line:
                    return dict(part=part, ok=False, err='leaf records truncated')
                idx = nleaf; nleaf += 1
                if idx < A or (B is not None and idx >= B):
                    continue
                rec = json.loads(line)
                if code == 254 and len(rec['S']) != 1:
                    return dict(part=part, ok=False, err='code 254 with several structures')
                nchk += 1
                okb, c_, r_ = exact_box(l, h)
                ok, msg = ch.leaf(c_, r_, rec) if okb else (False, 'leaf box not exactly c +- h')
                if not ok:
                    nfail += 1; fails.append((msg, l.tolist(), h.tolist()))
            elif 0 <= code < d:
                m = 0.5 * (l[code] + h[code])
                l2, h2 = l.copy(), h.copy(); l2[code] = m
                l1, h1 = l.copy(), h.copy(); h1[code] = m
                stack.append((l2, h2)); stack.append((l1, h1))
            else:
                return dict(part=part, ok=False, err=f'bad code {code}')
    if pos != len(codes):
        return dict(part=part, ok=False, err='trailing codes')
    if recs.readline():
        return dict(part=part, ok=False, err='trailing leaf records')
    B = nleaf if B is None else min(B, nleaf)
    if A > B or (lrange is not None and nchk != B - A):
        return dict(part=part, ok=False, err=f'leaf range {A}:{B} outside the {nleaf} leaves')
    return dict(part=part, ok=(nfail == 0) and (okp or not partial), leaves=nleaf, leaf_range=[A, B], leaves_checked=nchk,
                fails=nfail, min_margin=ch.min_margin, first_fails=fails[:3], partial_test=(partial and not okp),
                distributed=(distributed and not okp), tau=meta['tau'], sha256=shas, checker='wcheck_v2')


if __name__ == '__main__':
    certdir = sys.argv[1]
    if certdir == '--selftest':
        raise SystemExit('see wcheck_selftest.py')
    if sys.argv[2] == 'present':
        metas = [f for f in os.listdir(certdir) if f.endswith('.json')]
        meta = json.load(open(os.path.join(certdir, sorted(metas)[0])))
        print(check_all_present(certdir, int(meta['nparts'])))
    else:
        args = sys.argv[2:]
        lrange = None
        if '--leaves' in args:
            i = args.index('--leaves'); a, b = args[i + 1].split(':'); lrange = (int(a), int(b)); del args[i:i + 2]
        for p in args:
            print(json.dumps(check_part(certdir, int(p), lrange)), flush=True)
