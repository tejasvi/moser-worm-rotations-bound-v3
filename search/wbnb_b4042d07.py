#!/usr/bin/env python3
"""Cost probe for a certified worm lower bound (float search side only): the Lebesgue fan/Taylor/Lemma-K bounds
(lbsearch.Family) applied to polygonal arcs. Body 0 = L fixed; body i >= 1 placed by (phi_i, t_i), proper motions.

  wbnb.py TAU SEED NCELLS CAP OUT      (family: Keller's L,T,U,C + mirror Z S(0.16, 77 deg))
"""
import sys, json, time
import numpy as np
sys.path.insert(0, __import__('os').path.dirname(__import__('os').path.abspath(__file__)))
from lbsearch import Family, Rm
from scipy.optimize import linprog
sys.path.insert(0, '.')
from worm import keller, _hull
from fammin import zarc


def hullverts(A):
    S = _hull(np.asarray(A, float))
    return np.asarray(A, float)[S]


class PolyFamily(Family):
    def __init__(self, arcs):
        self.k = len(arcs) - 1
        self.Vb = [hullverts(arcs[0])]
        for A in arcs[1:]:
            H = hullverts(A)
            self.Vb.append(H - H.mean(axis=0))
        self.dim = 3 * self.k
        self.ZS = np.zeros((1, 2))
        self.mask = None
        self.masks = [tuple(i for i in range(1, self.k + 1) if (m >> (i - 1)) & 1) for m in range(1, 2 ** self.k - 1)]

    def subarea(self, c, mask):
        pl = self.place(c)
        P = np.vstack([self.Vb[0]] + [self.Vb[i] @ Rm(pl[i][0]).T + pl[i][1] for i in mask])
        H = P[_hull(P)]
        return 0.5 * float(np.sum(H[:, 0] * np.roll(H[:, 1], -1) - np.roll(H[:, 0], -1) * H[:, 1]))

    def small_lists(self, c, mask, sizes=(5, 4), noff=6):
        """cyclic sub-lists of <= 5 hull vertices (Keller's Lemma 3.3: F_P <= area(H) in any order, no conditions):
        hull vertices extreme in m equally spaced directions, best offsets by area at c."""
        self.mask = mask
        ib, Q = PolyFamily.witnesses(self, c)
        self.mask = None
        pl = self.place(c)
        X = np.array([Rm(pl[i][0]) @ q + pl[i][1] for i, q in zip(ib, Q)])
        out = []
        for m in sizes:
            if len(ib) < 3:
                break
            best = None
            for off in np.linspace(0, 2 * np.pi / m, noff, endpoint=False):
                th = off + 2 * np.pi * np.arange(m) / m
                sel = sorted(set(int(np.argmax(X @ np.array([np.cos(t), np.sin(t)]))) for t in th))
                if len(sel) < 3:
                    continue
                Y = X[sel]
                a = 0.5 * np.sum(Y[:, 0] * np.roll(Y[:, 1], -1) - np.roll(Y[:, 0], -1) * Y[:, 1])
                if best is None or a > best[0]:
                    best = (a, sel)
            if best is not None:
                out.append((ib[best[1]], Q[best[1]]))
        return out

    @staticmethod
    def quad_lb(H, h):
        """lower bound of D^T H D over |D_k| <= h_k: max of lambda_lo(H)|h|^2, lambda_lo(M) d and the Gershgorin-type
        sum_k min(0, M_kk) - sum_{k != l} |M_kl|, with M = diag(h) H diag(h) (scale-aware for elongated boxes)."""
        M = H * h[:, None] * h[None, :]
        q1 = min(0.0, np.linalg.eigvalsh(H)[0]) * (h @ h)
        q2 = np.minimum(0.0, np.diag(M)).sum() - (np.abs(M).sum() - np.abs(np.diag(M)).sum())
        q3 = min(0.0, np.linalg.eigvalsh(M)[0]) * float((h > 0).sum())
        return max(q1, q2, q3), M

    def _eval(self, ib, Q, c, h, small=False, z=None):
        runs = self.runs(ib, Q)
        F, g, H, W = self.taylor(runs, c, h)
        q, M = self.quad_lb(H, h)
        e2 = -0.5 * q + 0.5 * h @ W @ h
        L = F - np.abs(g) @ h - e2
        lam = np.linalg.eigvalsh(H)[0]
        contrib = np.abs(g) * h + 0.5 * max(0.0, -lam) * h * h + 0.5 * (W @ h) * h
        return L, dict(F=F, g=g, lam=q, contrib=contrib, nruns=len(runs), z=z, nw=len(ib), e2=e2, small=small)

    def bound(self, c, h):
        ibf, Qf = self.witnesses(c)
        fz = self.fan(c, h)
        if fz is None:
            return -np.inf, None
        ib, Q, z = fz
        L, info = self._eval(ib, Q, c, h, z=z)
        if len(ib) < len(ibf):
            # vertices dropped for fan validity: the lost area is recovered only by shrinking the box in the
            # coordinates of the dropped vertices' bodies, so charge it to those coordinates (split choice only)
            pl = self.place(c)
            def area(ibv, Qv):
                X = np.array([Rm(pl[i][0]) @ q + pl[i][1] for i, q in zip(ibv, Qv)])
                return 0.5 * float(np.sum(X[:, 0] * np.roll(X[:, 1], -1) - np.roll(X[:, 0], -1) * X[:, 1]))
            loss = max(0.0, area(ibf, Qf) - info['F'])
            kept = {(int(i), tuple(np.round(q, 12))) for i, q in zip(ib, Q)}
            m = np.zeros(self.dim)
            for i, q in zip(ibf, Qf):
                if i == 0 or (int(i), tuple(np.round(q, 12))) in kept:
                    continue
                ir, ix, iy = self.pidx(int(i))
                m[ir] += np.linalg.norm(q) * h[ir]; m[ix] += h[ix]; m[iy] += h[iy]
            if m.sum() > 0:
                info['drop_loss'] = loss
                info['contrib_drop'] = loss * m / m.sum()
        return L, info

    def _model(self, ib, Q, c, h):
        L, info = self._eval(ib, Q, c, h)
        return info['F'], info['g'], info['e2']

    def bound_list(self, ib, Q, c, h):
        return self._eval(ib, Q, c, h, small=True)

    def bound_best(self, c, h, tau_s, ntry=4):
        """max of: the full-hull fan bound; fan bounds of sub-hulls (L plus a subset of the placed arcs; A(p) >= area of
        the hull of any subset); and <= 5-point list bounds (valid in any order) of the full hull and the sub-hulls.
        On failure, info['split'] is the contrib of the candidate closest to succeeding, (F - tau)/(F - L) maximal
        among those with F > tau (a dead-end bound with F < tau must not steer the split)."""
        self.mask = None
        cands = [self.bound(c, h)]
        if cands[0][0] >= tau_s:
            return cands[0]
        # prefer sub-hulls with few arcs: their bounds lose only in those arcs' coordinates
        cand = sorted((((self.subarea(c, m) - tau_s) / np.sqrt(len(m)), m) for m in self.masks), reverse=True)
        tries = [None] + [m for s, m in cand[:ntry] if s > 0]
        for m in tries[1:]:
            self.mask = m
            r = self.bound(c, h)
            self.mask = None
            if r[0] >= tau_s:
                return r
            cands.append(r)
        for m in tries:
            for ib, Q in self.small_lists(c, m):
                r = self.bound_list(ib, Q, c, h)
                if r[0] >= tau_s:
                    return r
                cands.append(r)
        # alternative drop choices for fan validity (near-coincident vertices from different arcs at degenerate
        # kinks): each variant is valid on the whole box, so all of them are Lemma K candidates
        for rule in ('first', 'least'):
            st = self.fan_variant(c, h, rule)
            if st is not None:
                cands.append(self._eval(st[0], st[1], c, h, z=st[2]))
        # near-boundary lists: at a degenerate kink every vertex sits on the hull boundary; lists that keep the
        # vertices within the box's movement of the boundary (and variants without one of them) give Lemma K the
        # structures whose gradients cancel
        for ibn, Qn, zn in self.near_lists(c, h):
            cands.append(self._eval(ibn, Qn, c, h, z=zn))
        # Lemma K over every valid candidate (full/sub-hull fans, small lists, fans of structures at shifted points)
        comb = self.combine(c, h, [r for r in cands if r[1] is not None])
        if comb[0] >= tau_s:
            return comb
        L, info = max(cands + [comb], key=lambda r: r[0])
        good = [r for r in cands if r[1] is not None and r[1]['F'] > tau_s]   # comb never steers the split
        full = cands[0][1]
        if good:
            gL, ginfo = max(good, key=lambda r: (r[1]['F'] - tau_s) / max(r[1]['F'] - r[0], 1e-300))
            info = dict(info) if info is not None else dict(F=ginfo['F'], e2=ginfo['e2'], contrib=ginfo['contrib'])
            info['split'] = ginfo['contrib']
            # (the 'drop-split' override that split on the dropped vertices' coordinates was removed 2026-10-20 20:10
            #  PDT: it sent sub-box 54 of the polished optimum cell into a dead end; without it 1,093 boxes)
        return L, info

    def near_lists(self, c, h, maxvar=8):
        pl = self.place(c)
        pts, ib, Q, mv = [], [], [], []
        for i in range(self.k + 1):
            rho, t = pl[i]
            if i == 0:
                a = dt = 0.0
            else:
                ir, ix, iy = self.pidx(i); a = h[ir]; dt = np.hypot(h[ix], h[iy])
            for q in self.Vb[i]:
                pts.append(Rm(rho) @ q + t); ib.append(i); Q.append(q); mv.append(np.linalg.norm(q) * a + dt)
        P = np.array(pts); ib = np.array(ib, dtype=np.int64); Q = np.array(Q); mv = np.array(mv)
        S = _hull(P); H = P[S]
        E = np.roll(H, -1, axis=0) - H
        N = np.stack([E[:, 1], -E[:, 0]], 1) / np.linalg.norm(E, axis=1)[:, None]
        dist = np.min(np.sum(N * H, axis=1)[None, :] - P @ N.T, axis=1)      # >= 0 inside
        near = np.nonzero(dist <= 2.0 * (mv + mv.max()))[0]
        a2 = H[:, 0] * np.roll(H[:, 1], -1) - np.roll(H[:, 0], -1) * H[:, 1]
        z0 = np.array([((H[:, 0] + np.roll(H[:, 0], -1)) * a2).sum(), ((H[:, 1] + np.roll(H[:, 1], -1)) * a2).sum()]) / (3 * a2.sum())
        ang = np.arctan2(P[near, 1] - z0[1], P[near, 0] - z0[0])
        order = near[np.argsort(ang)]
        out = []
        base = [order]
        extra = [k for k in order if k not in set(S.tolist())]
        for k in extra[:maxvar]:
            base.append(np.array([j for j in order if j != k]))
        self.ZS = np.vstack([z0] + [z0 + 0.05 * np.array([np.cos(t), np.sin(t)]) for t in np.arange(8) * np.pi / 4])
        for lst in base:
            if len(lst) < 3:
                continue
            ibl, Ql = ib[lst], Q[lst]
            row = self.pair_lbs(ibl, Ql, c, h, z0[None, :])[0]
            if (row > 0).all():
                out.append((ibl, Ql, z0))
        return out

    def fan_variant(self, c, h, rule):
        """fan validated over the box, dropping the FIRST vertex of a failing pair ('first') or the vertex of the
        failing pair whose removal loses the least area at c ('least'); Family.fan drops the second one."""
        ib, Q = self.witnesses(c)
        pl = self.place(c)
        lbs = self.pair_lbs(ib, Q, c, h, self.ZS)
        z = self.ZS[int(np.argmin((lbs <= 0).sum(axis=1)))]
        for it in range(400):
            row = self.pair_lbs(ib, Q, c, h, z[None, :])[0]
            bad = np.nonzero(row <= 0)[0]
            if len(bad) == 0:
                return ib, Q, z
            if len(ib) <= 4:
                return None
            j = bad[0]; j2 = (j + 1) % len(ib)
            if rule == 'first':
                drop = j if ib[j] != 0 else j2
            else:
                X = np.array([Rm(pl[i][0]) @ q + pl[i][1] for i, q in zip(ib, Q)])
                def loss(k):
                    a, b, d = X[(k - 1) % len(X)], X[k], X[(k + 1) % len(X)]
                    return 0.5 * ((b[0] - a[0]) * (d[1] - a[1]) - (b[1] - a[1]) * (d[0] - a[0]))
                opts = [k for k in (j, j2) if ib[k] != 0] or [j2]
                drop = min(opts, key=loss)
            ib = np.delete(ib, drop); Q = np.delete(Q, drop, axis=0)
        return None

    def combine(self, c, h, cands, nshift=4):
        """max over convex combinations: sum lam_i (F_i - e_i) - sum_k |sum_i lam_i g_ik| h_k (LP in lam)."""
        models = [(r[1]['F'], r[1]['g'], r[1]['e2']) for r in cands]
        if not models:
            return -np.inf, None
        g0 = max(cands, key=lambda r: r[0])[1]['g']
        for k in np.argsort(-(np.abs(g0) * h))[:nshift]:
            sv = np.zeros(len(c)); sv[k] = -np.sign(g0[k]) if g0[k] != 0 else 1.0
            st = self._structure_at(c + sv * h, c, h)
            if st is not None:
                L_, inf_ = self._eval(st[0], st[1], c, h)
                models.append((inf_['F'], inf_['g'], inf_['e2']))
        m = len(models); d = len(c)
        a = np.array([F - e for (F, g, e) in models]); G = np.array([g for (F, g, e) in models])
        cvec = np.concatenate([-a, h])
        A_ub = np.vstack([np.hstack([G.T, -np.eye(d)]), np.hstack([-G.T, -np.eye(d)])])
        A_eq = np.concatenate([np.ones(m), np.zeros(d)])[None, :]
        res = linprog(cvec, A_ub=A_ub, b_ub=np.zeros(2 * d), A_eq=A_eq, b_eq=[1.0], bounds=[(0, None)] * (m + d),
                      method='highs')
        if res.status != 0:
            return -np.inf, None
        lam = res.x[:m]
        gc = G.T @ lam
        Lc = float(a @ lam - np.abs(gc) @ h)
        Fc = float(np.array([F for (F, g, e) in models]) @ lam)
        ec = float(np.array([e for (F, g, e) in models]) @ lam)
        return Lc, dict(F=Fc, g=gc, e2=ec, contrib=np.abs(gc) * h, nw=m, small=False, combo=True)

    def pidx(self, i):
        b = 3 * (i - 1)
        return (b, b + 1, b + 2)

    def place(self, p):
        out = [(0.0, np.zeros(2))]
        for i in range(1, self.k + 1):
            b = 3 * (i - 1)
            out.append((p[b], np.array([p[b + 1], p[b + 2]])))
        return out

    def witnesses(self, c):
        pl = self.place(c)
        pts, ib, Q = [], [], []
        for i in range(self.k + 1):
            if self.mask is not None and i != 0 and i not in self.mask:
                continue
            rho, t = pl[i]
            R = Rm(rho)
            for q in self.Vb[i]:
                pts.append(R @ q + t); ib.append(i); Q.append(q)
        P = np.array(pts)
        S = _hull(P)
        H = P[S]
        # fan centres: area centroid of the hull at c and 8 points around it
        a = H[:, 0] * np.roll(H[:, 1], -1) - np.roll(H[:, 0], -1) * H[:, 1]
        A = a.sum() / 2
        cx = ((H[:, 0] + np.roll(H[:, 0], -1)) * a).sum() / (6 * A)
        cy = ((H[:, 1] + np.roll(H[:, 1], -1)) * a).sum() / (6 * A)
        z0 = np.array([cx, cy])
        self.ZS = np.vstack([z0] + [z0 + 0.05 * np.array([np.cos(t), np.sin(t)]) for t in np.arange(8) * np.pi / 4])
        return np.array(ib, dtype=np.int64)[S], np.array(Q)[S]


def domain(tau, nb_per):
    """Angles: T [0, pi/3], U [0, 2pi], C [0, pi], S [0, pi]; translations |tx| <= X, |ty| <= Y (Keller sec. 3.2)."""
    w = np.sqrt(3) / 4
    X = 2 * tau / w - 0.5; Y = 2 * tau
    lo, hi = [], []
    for per in nb_per:
        lo += [0.0, -X, -Y]; hi += [per, X, Y]
    return np.array(lo), np.array(hi)


def dfs(fam, l0, h0, tau_s, cap):
    stack = [(l0, h0)]
    nbox = nbnd = nmul = 0
    t0 = time.time()
    while stack:
        l, h = stack.pop(); nbox += 1
        if nbox > cap:
            return dict(boxes=nbox, finished=False, bnd=nbnd, multi=nmul, secs=time.time() - t0, left=len(stack))
        c = 0.5 * (l + h); hw = 0.5 * (h - l)
        L, info = fam.bound_best(c, hw, tau_s)
        if L >= tau_s:
            nbnd += 1; continue
        if info is not None and info['F'] - 1.5 * info['e2'] > tau_s:
            Lm, im = fam.bound_multi(c, hw)
            if Lm >= tau_s and 'multi' in im:
                nmul += 1; continue
        k = int(np.argmax(hw)) if info is None else int(np.argmax(info.get('split', info['contrib']) + 1e-15 * hw))
        m = 0.5 * (l[k] + h[k])
        l2, h2 = l.copy(), h.copy(); l2[k] = m
        l1, h1 = l.copy(), h.copy(); h1[k] = m
        stack.append((l2, h2)); stack.append((l1, h1))
    return dict(boxes=nbox, finished=True, bnd=nbnd, multi=nmul, secs=time.time() - t0)


if __name__ == "__main__":
    tau, seed, ncells, cap, out = float(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), sys.argv[5]
    fam = PolyFamily(keller() + [zarc(0.16, np.radians(77), +1)])
    lo, hi = domain(tau, [np.pi / 3, 2 * np.pi, np.pi, np.pi])
    split0 = np.array([2, 2, 2, 8, 2, 2, 4, 2, 2, 4, 2, 2])
    ncell_tot = int(np.prod(split0))
    rng = np.random.default_rng(seed)
    for _ in range(ncells):
        ci = int(rng.integers(ncell_tot))
        cell = np.array(np.unravel_index(ci, split0))
        cl = lo + (hi - lo) * cell / split0; ch = lo + (hi - lo) * (cell + 1) / split0
        r = dfs(fam, cl, ch, tau + 1e-6, cap)
        r['cell'] = ci
        print(json.dumps(r), flush=True)
        open(out, "a").write(json.dumps(r) + "\n")
