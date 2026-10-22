"""Arc families for the worm (Moser 13a) certificates: exact construction data (written into every certificate header and
re-evaluated by the checker in interval arithmetic) and float vertex arrays for the search.

An arc is a polyline: start point s, segment lengths l_k (exact rationals) and absolute directions d_k in degrees
(exact rationals): v_0 = s, v_{k+1} = v_k + l_k (cos d_k, sin d_k). Its length is sum l_k (exact). Body 0 is the fixed
segment L with vertices (-1/2, 0), (1/2, 0).
"""
from fractions import Fraction as Fr
import math
import numpy as np


def polyline(start, lengths, dirs_deg):
    return {"start": [str(Fr(s)) for s in start], "lengths": [str(Fr(l)) for l in lengths],
            "dirs_deg": [str(Fr(d)) for d in dirs_deg]}


def zarc(a, th_deg, sign):
    """centrally symmetric Z: ends a, middle 1 - 2a, directions 0, sign*th, 0."""
    a = Fr(a); th = Fr(th_deg)
    return polyline([0, 0], [a, 1 - 2 * a, a], [0, sign * th, 0])


def uarc(beta_deg):
    b = Fr(beta_deg)
    return polyline([0, 0], [Fr(1, 3)] * 3, [0, b, 2 * b])


FAMILIES = {
    # rotation-only (M+) family: Keller's L, T plus U(84 deg), C = Z(3/20, 70 deg, -1), S = mirror Z(41/250, 75 deg, +1)
    "polished1": {
        "arcs": [polyline([Fr(-1, 2), 0], [1], [0]),
                 polyline([Fr(-1, 4), 0], [Fr(1, 2), Fr(1, 2)], [60, -60]),
                 uarc(84), zarc(Fr(3, 20), 70, -1), zarc(Fr(41, 250), 75, +1)],
        "periods": ["2/3", "2", "1", "1"],          # rotation periods of the placed arcs in units of pi (T, U, C, S)
        "min_width_T": "sqrt(3)/4",
        "convention": "rotations and translations only (M+)",
    },
    # reflections allowed (M+-) family: Keller's L, T, U(82.5 deg) and a Z of Keller's proportions (109/1024, 72.5 deg)
    # plus an achiral broadworm-like 6-segment arc B (min width 0.4387 > sqrt(3)/4); T, U, B are
    # mirror-symmetric and C's mirror is absorbed by the global reflection in the x-axis (fixes L), so the M+- minimum
    # equals the proper-motion minimum with C as given
    "mpm1": {
        "arcs": [polyline([Fr(-1, 2), 0], [1], [0]),
                 polyline([Fr(-1, 4), 0], [Fr(1, 2), Fr(1, 2)], [60, -60]),
                 uarc(Fr(165, 2)), zarc(Fr(109, 1024), Fr(145, 2), -1),
                 polyline([0, 0], [Fr('0.1726'), Fr('0.0648'), Fr('0.2626'), Fr('0.2626'), Fr('0.0648'), Fr('0.1726')],
                          [Fr('72.27'), Fr('63.84'), Fr('55.39'), Fr('-55.39'), Fr('-63.84'), Fr('-72.27')])],
        "periods": ["2/3", "2", "1", "2"],
        "min_width_T": "sqrt(3)/4",
        "reflections": True,
        "mirror_absorbed_by_global_reflection": 3,
        "convention": "rotations, translations and reflections (M+-)",
    },
}


def float_vertices(arc):
    s = np.array([float(Fr(x)) for x in arc["start"]])
    pts = [s]
    for l, d in zip(arc["lengths"], arc["dirs_deg"]):
        ang = math.radians(float(Fr(d)))
        pts.append(pts[-1] + float(Fr(l)) * np.array([math.cos(ang), math.sin(ang)]))
    return np.array(pts)


def arc_length(arc):
    return sum(Fr(l) for l in arc["lengths"])
