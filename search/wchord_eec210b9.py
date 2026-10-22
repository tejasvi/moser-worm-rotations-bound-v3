#!/usr/bin/env python3
"""Search-side (float) prototype of Keller's chord decomposition (arXiv:2609.21968, Lemma 3.5) as an extra source of
valid lists for the worm B&B (wbnb.PolyFamily).

For a cyclic list P (CCW at the box centre) a cut by the chord (P_a, P_b) is valid on the box when
  * P_a != P_b on the box,
  * the vertices strictly between a and b (CCW) satisfy det(P_b - P_a, P_i - P_a) <= 0 on the box (right closed
    half-plane) and the vertices strictly between b and a satisfy det(P_b - P_a, P_i - P_a) >= 0 (left closed half-plane),
  * each piece is certified: <= 5 vertices (Lemma 3.3, no condition), or the fan from one of its vertices (Lemma 3.4,
    xi_1 x xi_i > 0 and xi_i x xi_{i+1} > 0) holds on the box, or it is cut again.
Then F_P <= area(conv P) <= A(p) on the box, so the WHOLE list's Taylor model (PolyFamily._eval) is a valid candidate.

Box bounds of det(P_b - P_a, P_i - P_a): with u = P_b - P_a, v = P_i - P_a at the centre and |du| <= e_ab, |dv| <= e_ai
(e = |q_b - q_a| h_rot for two vertices of one body, else mv_a + mv_b with mv = |q| h_rot + |h_t|),
  |det(u + du, v + dv) - det(u, v)| <= e_ab |v| + e_ai |u| + e_ab e_ai;
the determinant is exactly constant when all three vertices are on one body.
"""
import sys
from collections import Counter
import numpy as np
sys.path.insert(0, __import__('os').path.dirname(__import__('os').path.abspath(__file__)))
sys.path.insert(0, __import__('os').path.dirname(__import__('os').path.abspath(__file__)))
from lbsearch import Rm
from wbnb import PolyFamily
from worm import _hull


class ChordFamily(PolyFamily):
    def __init__(self, arcs, use_full=True, use_near=True, use_sub=True, budget=400, topk=6, base_split=False):
        super().__init__(arcs)
        self.base_split = base_split     # True: split choice exactly as PolyFamily (chord candidates only bound)
        self.use_full, self.use_near, self.use_sub = use_full, use_near, use_sub
        self.budget, self.topk = budget, topk
        self.stats = Counter()

    # ---------- geometry over the box ----------
    def _det_bounds(self, ib, Q, c, h):
        pl = self.place(c)
        a = np.zeros(self.k + 1); dt = np.zeros(self.k + 1)
        for i in range(1, self.k + 1):
            ir, ix, iy = self.pidx(i); a[i] = h[ir]; dt[i] = np.hypot(h[ix], h[iy])
        X = np.array([Rm(pl[i][0]) @ q + pl[i][1] for i, q in zip(ib, Q)])
        mv = np.linalg.norm(Q, axis=1) * a[ib] + dt[ib]
        same = ib[:, None] == ib[None, :]
        dq = np.linalg.norm(Q[None, :, :] - Q[:, None, :], axis=2)
        e = np.where(same, dq * a[ib][:, None], mv[:, None] + mv[None, :])       # |d(X_b - X_a)| <= e[a, b]
        U = X[None, :, :] - X[:, None, :]                                         # U[a, b] = X_b - X_a
        nU = np.linalg.norm(U, axis=2)
        D = U[:, :, None, 0] * U[:, None, :, 1] - U[:, :, None, 1] * U[:, None, :, 0]   # D[a,b,i] = det(X_b-X_a, X_i-X_a)
        E = e[:, :, None] * nU[:, None, :] + e[:, None, :] * nU[:, :, None] + e[:, :, None] * e[:, None, :]
        s3 = same[:, :, None] & same[:, None, :]
        E = np.where(s3, 0.0, E)
        return D - E, D + E, nU - e      # lower / upper bounds of D; lower bound of |X_b - X_a| (distinct if > 0)

    # ---------- certification of F_P <= area(conv P) by cuts ----------
    def _fan_ok(self, lst, LB):
        n = len(lst)
        for r in range(n):
            l = lst[r:] + lst[:r]
            p0 = l[0]
            if all(LB[p0, l[1], l[i]] > 0 for i in range(2, n)) and all(LB[p0, l[i], l[i + 1]] > 0 for i in range(2, n - 1)):
                return True
        return False

    def _certify(self, lst, LB, UB, DL, memo, ctr):
        n = len(lst)
        if n <= 5:
            return True
        key = tuple(lst)
        if key in memo:
            return memo[key]
        ctr[0] += 1
        if ctr[0] > self.budget:
            return False
        if self._fan_ok(lst, LB):
            memo[key] = True; ctr[1] += 1
            return True
        opts = []
        for s in range(n):
            for d in range(2, n - 1):
                t = (s + d) % n
                pa, pb = lst[s], lst[t]
                if DL[pa, pb] <= 0:
                    continue
                right = [lst[(s + k) % n] for k in range(1, d)]
                left = [lst[(t + k) % n] for k in range(1, n - d)]
                mr = min(-UB[pa, pb, i] for i in right)
                ml = min(LB[pa, pb, i] for i in left)
                m = min(mr, ml)
                if m < 0:
                    continue
                p1 = [lst[(s + k) % n] for k in range(0, d + 1)]
                p2 = [lst[(t + k) % n] for k in range(0, n - d + 1)]
                big = (len(p1) > 5) + (len(p2) > 5)
                opts.append((big, abs(len(p1) - len(p2)), -m, s, t, p1, p2))
        # each unordered chord appears twice (s,t) and (t,s) with the same pieces swapped: dedupe
        seen = set(); uniq = []
        for o in sorted(opts, key=lambda o: o[:3]):
            ch = frozenset((lst[o[3]], lst[o[4]]))
            if ch in seen:
                continue
            seen.add(ch); uniq.append(o)
        ok = False
        for o in uniq[:self.topk]:
            if self._certify(o[5], LB, UB, DL, memo, ctr) and self._certify(o[6], LB, UB, DL, memo, ctr):
                ok = True; break
        memo[key] = ok
        return ok

    def chord_valid(self, ib, Q, c, h):
        """True if F_P <= area(conv P) is certified on the box by the fan from a vertex, or by chord cuts into pieces
        of <= 5 vertices / fan-valid pieces."""
        if len(ib) < 3:
            return False
        LB, UB, DL = self._det_bounds(np.asarray(ib, dtype=np.int64), np.asarray(Q, float), c, h)
        ctr = [0, 0]
        ok = self._certify(list(range(len(ib))), LB, UB, DL, {}, ctr)
        return ok

    # ---------- candidate lists ----------
    def _near_order(self, c, h):
        """near-boundary vertex lists (as in PolyFamily.near_lists) WITHOUT the fan check: all vertices within the box's
        movement of the hull boundary in angular order about the centroid, and variants without one non-hull vertex."""
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
        dist = np.min(np.sum(N * H, axis=1)[None, :] - P @ N.T, axis=1)
        near = np.nonzero(dist <= 2.0 * (mv + mv.max()))[0]
        a2 = H[:, 0] * np.roll(H[:, 1], -1) - np.roll(H[:, 0], -1) * H[:, 1]
        z0 = np.array([((H[:, 0] + np.roll(H[:, 0], -1)) * a2).sum(), ((H[:, 1] + np.roll(H[:, 1], -1)) * a2).sum()]) / (3 * a2.sum())
        ang = np.arctan2(P[near, 1] - z0[1], P[near, 0] - z0[0])
        order = near[np.argsort(ang)]
        base = [order]
        hs = set(S.tolist())
        for k in [k for k in order if k not in hs][:8]:
            base.append(np.array([j for j in order if j != k]))
        return [(ib[l], Q[l]) for l in base if len(l) >= 3]

    def chord_cands(self, c, h, tau_s):
        out = []
        seen = set()
        lists = []
        if self.use_full:
            self.mask = None
            ib, Q = self.witnesses(c)
            lists.append(('full', ib, Q))
        if self.use_near:
            for ib, Q in self._near_order(c, h):
                lists.append(('near', ib, Q))
        if self.use_sub:
            cand = sorted((((self.subarea(c, m) - tau_s) / np.sqrt(len(m)), m) for m in self.masks), reverse=True)
            for s, m in cand[:4]:
                if s <= 0:
                    continue
                self.mask = m
                ib, Q = self.witnesses(c)
                self.mask = None
                lists.append(('sub', ib, Q))
        self.mask = None
        for kind, ib, Q in lists:
            key = (tuple(ib.tolist()), tuple(np.round(Q, 12).ravel().tolist()))
            if key in seen:
                continue
            seen.add(key)
            self.stats['try_' + kind] += 1
            if self.chord_valid(ib, Q, c, h):
                self.stats['ok_' + kind] += 1
                r = self._eval(ib, Q, c, h)
                r[1]['chord'] = kind
                out.append(r)
        return out

    # ---------- bound_best: PolyFamily.bound_best + chord candidates ----------
    def bound_best(self, c, h, tau_s, ntry=4):
        self.stats['boxes'] += 1
        self.mask = None
        cands = [self.bound(c, h)]
        if cands[0][0] >= tau_s:
            self.stats['win_fan'] += 1
            return cands[0]
        ch = self.chord_cands(c, h, tau_s)
        for r in ch:
            if r[0] >= tau_s:
                self.stats['win_chord_' + r[1]['chord']] += 1
                return r
        cand = sorted((((self.subarea(c, m) - tau_s) / np.sqrt(len(m)), m) for m in self.masks), reverse=True)
        tries = [None] + [m for s, m in cand[:ntry] if s > 0]
        for m in tries[1:]:
            self.mask = m
            r = self.bound(c, h)
            self.mask = None
            if r[0] >= tau_s:
                self.stats['win_subfan'] += 1
                return r
            cands.append(r)
        for m in tries:
            for ib, Q in self.small_lists(c, m):
                r = self.bound_list(ib, Q, c, h)
                if r[0] >= tau_s:
                    self.stats['win_small'] += 1
                    return r
                cands.append(r)
        for rule in ('first', 'least'):
            st = self.fan_variant(c, h, rule)
            if st is not None:
                cands.append(self._eval(st[0], st[1], c, h, z=st[2]))
        for ibn, Qn, zn in self.near_lists(c, h):
            cands.append(self._eval(ibn, Qn, c, h, z=zn))
        cands += ch
        comb = self.combine(c, h, [r for r in cands if r[1] is not None])
        if comb[0] >= tau_s:
            self.stats['win_comb' + ('_withchord' if ch else '')] += 1
            return comb
        self.stats['fail' + ('_withchord' if ch else '')] += 1
        L, info = max(cands + [comb], key=lambda r: r[0])
        good = [r for r in cands if r[1] is not None and r[1]['F'] > tau_s]
        full = cands[0][1]
        chfull = any(r[1].get('chord') == 'full' for r in ch)
        if self.base_split:
            good = [r for r in good if 'chord' not in r[1]]
            chfull = False
        if good:
            gL, ginfo = max(good, key=lambda r: (r[1]['F'] - tau_s) / max(r[1]['F'] - r[0], 1e-300))
            info = dict(info) if info is not None else dict(F=ginfo['F'], e2=ginfo['e2'], contrib=ginfo['contrib'])
            info['split'] = ginfo['contrib']
            # a chord-certified full list has no drop loss: the drop-based split applies only without one
            if not chfull and full is not None and full.get('drop_loss', 0.0) > ginfo['F'] - gL:
                info['split'] = full['contrib_drop']
        elif not chfull and full is not None and 'contrib_drop' in full and info is not None:
            info = dict(info); info['split'] = full['contrib_drop']
        return L, info
