"""Search side of the certified lower bound for Lebesgue's universal cover (float arithmetic).
Family: disk D (radius 1/2, centre 0, body 0) and regular Reuleaux polygons B_{n_1},...,B_{n_k} (bodies 1..k) of width 1,
corners V_l = R_n u(2 pi l/n), R_n = 1/(2 cos(pi/(2n))).  Placement p = (t1x, t1y, rho2, t2x, t2y, ..., rhok, tkx, tky);
body 1 has rotation 0 (gauge).  Box bound: inner fan of witness material points + second-order Taylor bound with a
Hessian-variation matrix W (see the Lebesgue paper, Lemmas 3.1 and 3.5).  This file is used only to SEARCH; the certificate is
checked by an independent program (lbcheck.py) in interval arithmetic."""
import numpy as np

J = np.array([[0., -1.], [1., 0.]])
def Rm(r):
    c, s = np.cos(r), np.sin(r); return np.array([[c, -s], [s, c]])
def det2(a, b): return a[0]*b[1] - a[1]*b[0]
def Rn(n): return 1.0/(2*np.cos(np.pi/(2*n)))

class Family:
    def __init__(self, ns, N=1024, eps=1e-6):
        self.ns = list(ns); self.k = len(ns); self.N = N; self.eps = eps
        self.V = [Rn(n)*np.stack([np.cos(2*np.pi*np.arange(n)/n), np.sin(2*np.pi*np.arange(n)/n)], 1) for n in ns]
        # arc of the corner l: normals from angle (2 pi l/n + pi - pi/(2n)) spanning pi/n (regular polygons)
        self.arcs = [[((2*np.pi*l/n + np.pi - np.pi/(2*n)) % (2*np.pi), np.pi/n) for l in range(n)] for n in ns]
        self.th = 2*np.pi*np.arange(N)/N
        self.dim = 2 + 3*(self.k - 1)
    def pidx(self, i):
        if i == 1: return (None, 0, 1)
        b = 2 + 3*(i - 2); return (b, b + 1, b + 2)
    def place(self, p):
        out = [(0.0, np.zeros(2))]
        for i in range(1, self.k + 1):
            ir, ix, iy = self.pidx(i)
            out.append((0.0 if ir is None else p[ir], np.array([p[ix], p[iy]])))
        return out
    def support(self, p, th):
        """hull support data in directions th: (dominant body, support point, support value)."""
        u = np.stack([np.cos(th), np.sin(th)], 1); M = len(th)
        Hb = np.full(M, 0.5); Pb = 0.5*u; Ib = np.zeros(M, dtype=np.int64)
        pl = self.place(p)
        for i in range(1, self.k + 1):
            rho, t = pl[i]; V = self.V[i-1] @ Rm(rho).T
            d = u @ V.T
            jc = np.argmax(d, axis=1); h = d[np.arange(M), jc]; pt = V[jc].copy()
            for l, (a1, span) in enumerate(self.arcs[i-1]):
                inr = ((th - rho - a1) % (2*np.pi)) <= span
                cand = 1.0 + d[:, l]
                upd = inr & (cand > h)
                h = np.where(upd, cand, h); pt = np.where(upd[:, None], V[l][None, :] + u, pt)
            h = h + u @ t; pt = pt + t
            better = h > Hb
            Hb = np.where(better, h, Hb); Pb = np.where(better[:, None], pt, Pb); Ib = np.where(better, i, Ib)
        return Ib, Pb, Hb
    def witnesses(self, c):
        """adaptive inner polygon at placement c: body indices, material points (body frame), world points."""
        Ib, X, _ = self.support(c, self.th)
        keep = np.abs(X - np.roll(X, 1, axis=0)).max(axis=1) > 1e-14
        if not keep.any(): keep[0] = True
        ib = list(Ib[keep]); Xl = [x for x in X[keep]]
        for it in range(60):
            A = np.array(Xl); B = np.roll(A, -1, axis=0); E = B - A
            nrm = np.stack([E[:, 1], -E[:, 0]], 1); ln = np.linalg.norm(nrm, axis=1)
            good = np.nonzero(ln > 1e-15)[0]
            if len(good) == 0: break
            phis = np.arctan2(nrm[good, 1], nrm[good, 0])
            jb, S, Hs = self.support(c, phis)
            gap = Hs - np.einsum('ij,ij->i', A[good], nrm[good]/ln[good, None])
            ins = [(good[m], jb[m], S[m]) for m in range(len(good)) if gap[m] > self.eps]
            if not ins: break
            for (j, b, s) in sorted(ins, key=lambda x: -x[0]):
                ib.insert(j + 1, int(b)); Xl.insert(j + 1, s)
        pl = self.place(c)
        Q = np.array([x if i == 0 else Rm(-pl[i][0]) @ (x - pl[i][1]) for i, x in zip(ib, Xl)])
        return np.array(ib, dtype=np.int64), Q
    # ---- fan validity over the box ----
    def pair_lbs(self, ib, Q, c, h, zs):
        pl = self.place(c)
        rho = np.array([pl[i][0] for i in range(self.k + 1)]); tt = np.array([pl[i][1] for i in range(self.k + 1)])
        a = np.zeros(self.k + 1); dt = np.zeros(self.k + 1)
        for i in range(1, self.k + 1):
            ir, ix, iy = self.pidx(i)
            a[i] = 0.0 if ir is None else h[ir]; dt[i] = np.hypot(h[ix], h[iy])
        cr, sr = np.cos(rho[ib]), np.sin(rho[ib])
        X = np.stack([cr*Q[:, 0] - sr*Q[:, 1], sr*Q[:, 0] + cr*Q[:, 1]], 1) + tt[ib]
        ib2 = np.roll(ib, -1); Q2 = np.roll(Q, -1, axis=0); X2 = np.roll(X, -1, axis=0)
        same = ib == ib2
        nq = np.linalg.norm(Q, axis=1); nq2 = np.linalg.norm(Q2, axis=1)
        dX = nq*a[ib] + dt[ib]; dX2 = nq2*a[ib2] + dt[ib2]
        wq = np.linalg.norm(Q2 - Q, axis=1)
        out = np.empty((len(zs), len(ib)))
        for zi, z in enumerate(zs):
            A = X - z; B = X2 - z
            d0 = A[:, 0]*B[:, 1] - A[:, 1]*B[:, 0]
            tz = np.linalg.norm(tt[ib] - z, axis=1)
            vs = wq*(dt[ib]*(1 + a[ib]) + tz*a[ib])
            vt = dX*(np.linalg.norm(B, axis=1) + dX2) + np.linalg.norm(A, axis=1)*dX2
            out[zi] = d0 - np.where(same, vs, vt)
        return out
    ZS = np.array([[0.0, 0.0]] + [[0.12*np.cos(a), 0.12*np.sin(a)] for a in np.arange(8)*np.pi/4])
    def fan(self, c, h):
        ib, Q = self.witnesses(c)
        lbs = self.pair_lbs(ib, Q, c, h, self.ZS)
        nf = (lbs <= 0).sum(axis=1); zi = int(np.argmin(nf)); z = self.ZS[zi]
        for it in range(400):
            row = self.pair_lbs(ib, Q, c, h, z[None, :])[0]
            bad = np.nonzero(row <= 0)[0]
            if len(bad) == 0: return ib, Q, z
            if len(ib) <= 4: return None
            j = bad[0]; j2 = (j + 1) % len(ib)
            drop = j2 if ib[j2] != 0 else j
            ib = np.delete(ib, drop); Q = np.delete(Q, drop, axis=0)
        return None
    # ---- runs, value, gradient, Hessian, Hessian variation ----
    @staticmethod
    def runs(ib, Q):
        n = len(ib)
        chg = np.nonzero(ib != np.roll(ib, 1))[0]
        if len(chg) == 0: chg = np.array([0])
        s = chg[0]; ib = np.roll(ib, -s); Q = np.roll(Q, -s, axis=0)
        chg = np.nonzero(ib != np.roll(ib, 1))[0]
        if len(chg) == 0 or chg[0] != 0: chg = np.concatenate([[0], chg])
        dets = Q[:-1, 0]*Q[1:, 1] - Q[:-1, 1]*Q[1:, 0]
        cs = np.concatenate([[0.0], np.cumsum(dets)])
        ends = list(chg[1:] - 1) + [n - 1]
        return [(int(ib[a]), Q[a].copy(), Q[b].copy(), cs[b] - cs[a]) for a, b in zip(chg, ends)]
    def taylor(self, runs, c, h):
        d = self.dim; pl = self.place(c)
        F = 0.0; g = np.zeros(d); H = np.zeros((d, d)); W = np.zeros((d, d))
        ra = np.zeros(self.k + 1); dt = np.zeros(self.k + 1)
        for i in range(1, self.k + 1):
            ir, ix, iy = self.pidx(i)
            ra[i] = 0.0 if ir is None else h[ir]; dt[i] = np.hypot(h[ix], h[iy])
        def info(i, q):
            rho, t = pl[i]; R = Rm(rho); x = R @ q + t
            if i == 0: return x, None, None, None, None
            ir, ix, iy = self.pidx(i)
            return x, ir, ix, iy, R
        def addsym(M, k, l, v):
            if k == l: M[k, k] += v
            else: M[k, l] += v; M[l, k] += v
        nr = len(runs)
        for r in range(nr):
            i, qa, qb, C = runs[r]
            F += 0.5*C
            if i != 0:
                rho, t = pl[i]; R = Rm(rho); w = qb - qa; Rw = R @ w; RJw = R @ (J @ w)
                ir, ix, iy = self.pidx(i)
                F += 0.5*det2(t, Rw)
                g[ix] += 0.5*Rw[1]; g[iy] += -0.5*Rw[0]
                if ir is not None:
                    g[ir] += 0.5*det2(t, RJw)
                    H[ir, ir] += -0.5*det2(t, Rw)
                    addsym(H, ir, ix, 0.5*RJw[1]); addsym(H, ir, iy, -0.5*RJw[0])
                    nw = np.linalg.norm(w); tn = np.linalg.norm(t)
                    W[ir, ir] += 0.5*nw*(dt[i]*(1 + ra[i]) + tn*ra[i])
                    addsym(W, ir, ix, 0.5*nw*ra[i]); addsym(W, ir, iy, 0.5*nw*ra[i])
            j = runs[(r + 1) % nr][0]; qn = runs[(r + 1) % nr][1]
            x, ira, ixa, iya, Ra = info(i, qb); y, irb, ixb, iyb, Rb = info(j, qn)
            F += 0.5*det2(x, y)
            # first derivatives
            dxs = {}; dys = {}
            if i != 0:
                dxs[ixa] = np.array([1., 0.]); dxs[iya] = np.array([0., 1.])
                if ira is not None: dxs[ira] = Ra @ (J @ qb)
            if j != 0:
                dys[ixb] = np.array([1., 0.]); dys[iyb] = np.array([0., 1.])
                if irb is not None: dys[irb] = Rb @ (J @ qn)
            for k, v in dxs.items(): g[k] += 0.5*det2(v, y)
            for k, v in dys.items(): g[k] += 0.5*det2(x, v)
            for k, v in dxs.items():
                for l, v2 in dys.items():
                    addsym(H, k, l, 0.5*det2(v, v2))
            if ira is not None: H[ira, ira] += 0.5*det2(-(Ra @ qb), y)
            if irb is not None: H[irb, irb] += 0.5*det2(x, -(Rb @ qn))
            # Hessian variation bounds
            nqa = np.linalg.norm(qb) if i != 0 else 0.0; nqb = np.linalg.norm(qn) if j != 0 else 0.0
            dxa = nqa*ra[i] + dt[i]; dyb = nqb*ra[j] + dt[j]
            ny = np.linalg.norm(y); nx = np.linalg.norm(x)
            if ira is not None:
                W[ira, ira] += 0.5*(nqa*ra[i]*(ny + dyb) + nqa*dyb)
            if irb is not None:
                W[irb, irb] += 0.5*(nqb*ra[j]*(nx + dxa) + nqb*dxa)
            if ira is not None and irb is not None:
                addsym(W, ira, irb, 0.5*nqa*nqb*(ra[i] + ra[j]))
            if ira is not None and j != 0:
                addsym(W, ira, ixb, 0.5*nqa*ra[i]); addsym(W, ira, iyb, 0.5*nqa*ra[i])
            if irb is not None and i != 0:
                addsym(W, ixa, irb, 0.5*nqb*ra[j]); addsym(W, iya, irb, 0.5*nqb*ra[j])
        return F, g, H, W
    def bound2(self, c, h, tau_s, slack=3e-5):
        """two-level bound: cheap witnesses (N=256, eps=1e-5) first; fine witnesses only if the cheap bound is close."""
        N0, e0, th0 = self.N, self.eps, self.th
        self.N, self.eps, self.th = 256, 1e-5, 2*np.pi*np.arange(256)/256
        try:
            L, info = self.bound(c, h)
        finally:
            self.N, self.eps, self.th = N0, e0, th0
        if L >= tau_s or L < tau_s - slack: return L, info
        return self.bound(c, h)
    def bound(self, c, h):
        fz = self.fan(c, h)
        if fz is None: return -np.inf, None
        ib, Q, z = fz
        runs = self.runs(ib, Q)
        F, g, H, W = self.taylor(runs, c, h)
        lam = np.linalg.eigvalsh(H)[0]
        L = F - np.abs(g) @ h + 0.5*min(0.0, lam)*(h @ h) - 0.5*h @ W @ h
        contrib = np.abs(g)*h + 0.5*max(0.0, -lam)*h*h + 0.5*(W @ h)*h
        e2 = 0.5*max(0.0, -lam)*(h @ h) + 0.5*h @ W @ h
        return L, dict(F=F, g=g, lam=lam, contrib=contrib, nruns=len(runs), z=z, nw=len(ib), e2=e2)


# ---------------- multi-structure (kink) bound ----------------
from scipy.optimize import linprog

def _structure_at(self, cprime, c, h):
    """witness structure from the support points at cprime, validated over the box (c, h); returns (ib, Q, z) or None."""
    ib, Q = self.witnesses(cprime)
    lbs = self.pair_lbs(ib, Q, c, h, self.ZS)
    nf = (lbs <= 0).sum(axis=1); zi = int(np.argmin(nf)); z = self.ZS[zi]
    for it in range(400):
        row = self.pair_lbs(ib, Q, c, h, z[None, :])[0]
        bad = np.nonzero(row <= 0)[0]
        if len(bad) == 0: return ib, Q, z
        if len(ib) <= 4: return None
        j = bad[0]; j2 = (j + 1) % len(ib)
        drop = j2 if ib[j2] != 0 else j
        ib = np.delete(ib, drop); Q = np.delete(Q, drop, axis=0)
    return None

def _model(self, ib, Q, c, h):
    runs = self.runs(ib, Q)
    F, g, H, W = self.taylor(runs, c, h)
    lam = np.linalg.eigvalsh(H)[0]
    e = 0.5*max(0.0, -lam)*(h @ h) + 0.5*h @ W @ h
    return F, g, e

def bound_multi(self, c, h, nextra=4, cheap=False):
    """max over convex combinations of several fan models (centre structure + structures at shifted points)."""
    L0, info0 = self.bound(c, h)
    if info0 is None: return L0, info0
    models = []
    s0 = self._structure_at(c, c, h)
    if s0 is None: return L0, info0
    models.append(self._model(*s0[:2], c, h))
    g0 = models[0][1]
    order = np.argsort(-(np.abs(g0)*h))
    specs = []
    for k in order[:nextra]:
        sv = np.zeros(len(c), dtype=np.int8); sv[k] = -int(np.sign(g0[k])) if g0[k] != 0 else 1; specs.append(sv)
    sv = -np.sign(g0).astype(np.int8); sv[sv == 0] = 1; specs.append(sv)
    used = [np.zeros(len(c), dtype=np.int8)]
    for sv in specs:
        cp = c + sv*h
        if cheap:
            N0, e0, th0 = self.N, self.eps, self.th
            self.N, self.eps, self.th = 256, 1e-5, 2*np.pi*np.arange(256)/256
            try:
                s = self._structure_at(cp, c, h)
            finally:
                self.N, self.eps, self.th = N0, e0, th0
        else:
            s = self._structure_at(cp, c, h)
        if s is not None: models.append(self._model(*s[:2], c, h)); used.append(sv)
    m = len(models); d = len(c)
    a = np.array([F - e for (F, g, e) in models]); G = np.array([g for (F, g, e) in models])
    # LP over (lambda_1..m, s_1..d): maximize a.lambda - h.s ; s_k >= +-(G^T lambda)_k ; sum lambda = 1
    cvec = np.concatenate([-a, h])
    A_ub = np.vstack([np.hstack([G.T, -np.eye(d)]), np.hstack([-G.T, -np.eye(d)])])
    b_ub = np.zeros(2*d)
    A_eq = np.concatenate([np.ones(m), np.zeros(d)])[None, :]
    res = linprog(cvec, A_ub=A_ub, b_ub=b_ub, A_eq=A_eq, b_eq=[1.0], bounds=[(0, None)]*(m + d), method='highs')
    if res.status != 0: return L0, info0
    lamv = res.x[:m]
    Lm = float(a @ lamv - np.abs(G.T @ lamv) @ h)
    if Lm > L0:
        info = dict(info0); info['multi'] = (m, lamv, np.array(used))
        return Lm, info
    return L0, info0

Family._structure_at = _structure_at
Family._model = _model
Family.bound_multi = bound_multi
