# Provenance of the third-party Lean files

`MoserWorm/` contains 15 files of Ethan Keller's Lean development for Moser's worm problem:

- upstream: https://github.com/ethan-keller/moser-worm-improved-bounds, commit 9a339413 ("Add arxiv link and cff");
- licence: Apache License 2.0, by Ethan Keller; paper "Improved bounds for universal convex covers of unit arcs",
  arXiv:2609.21968. `third_party/moser-worm-improved-bounds/LICENSE` is upstream's licence verbatim (sha256
  e74b5d16da388425...), with upstream's `CITATION.cff` and the upstream checksums of these files.

Upstream used Lean/Mathlib v4.33.1; this package uses Lean 4 v4.35.0-rc3 and Mathlib v4.35.0-rc3. One file was changed
for the newer toolchain and carries a "Modified 2026-10-21" notice below upstream's header; the others are
byte-identical to upstream.

| file | lines | upstream sha256 (16) | this package sha256 (16) | status |
|---|---|---|---|---|
| MoserWorm/Common/Area.lean | 422 | 85600b138af47069 | 85600b138af47069 | unchanged |
| MoserWorm/Common/Box/Basic.lean | 57 | 6d963fb61c183aea | 6d963fb61c183aea | unchanged |
| MoserWorm/Common/Box/Sound.lean | 72 | 6acaacddde68514f | 6acaacddde68514f | unchanged |
| MoserWorm/Common/Defs.lean | 54 | 5b4091672f2bf586 | 5b4091672f2bf586 | unchanged |
| MoserWorm/Common/Interval/Basic.lean | 179 | 02005324087d1e25 | 02005324087d1e25 | unchanged |
| MoserWorm/Common/Interval/Rational.lean | 27 | d48e9942071b5292 | d48e9942071b5292 | unchanged |
| MoserWorm/Common/Interval/RationalBasic.lean | 10 | 62ecf994bb92ab3b | 62ecf994bb92ab3b | unchanged |
| MoserWorm/Common/Interval/Sound.lean | 993 | c4df6ef21023ffc0 | c4df6ef21023ffc0 | unchanged |
| MoserWorm/Common/Isometry.lean | 194 | ac6b26b4cf6a8f17 | ac6b26b4cf6a8f17 | unchanged |
| MoserWorm/Common/Multiaffine.lean | 538 | 46413a1899716278 | 21c653985ccbe3d7 | modified: `Finset.prod_le_one` -> `Finset.prod_le_one₀` (2 places) |
| MoserWorm/Common/Polyline.lean | 317 | d19f35deaf39ab66 | d19f35deaf39ab66 | unchanged |
| MoserWorm/LowerBound/Corner.lean | 363 | 063e257796fc0462 | 063e257796fc0462 | unchanged |
| MoserWorm/LowerBound/Family.lean | 499 | d029fa539c321ab2 | d029fa539c321ab2 | unchanged |
| MoserWorm/LowerBound/Fan.lean | 231 | 60314623eaf01b93 | 60314623eaf01b93 | unchanged |
| MoserWorm/LowerBound/Placement.lean | 406 | 9e41d0e39b1560cd | 9e41d0e39b1560cd | unchanged |

The proof uses 8 of these files: the interval layer `MoserWorm/Common/Interval/{Basic, RationalBasic, Rational, Sound}`
(the certificate checker and its soundness), `Common/Defs`, `Common/Area` and `LowerBound/Fan` (the geometric
interface) and `Common/Isometry` (rigid motions). The other 7 (`Common/Box/{Basic, Sound}`, `Common/Multiaffine`,
`Common/Polyline`, `LowerBound/{Corner, Family, Placement}`) are included as ported but are not imported by the proof.
All other directories are new work of this package.

## Credit

The mathematics and the Lean development of `MoserWorm/` are Ethan Keller's. This package changes one file for the
newer toolchain and adds new files elsewhere.
