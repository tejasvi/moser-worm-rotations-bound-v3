# Lean proof of the lower bound 0.2410 for Moser's worm problem with rotations and translations only (M+)

Statement (`Worm13a/Statement.lean`): every convex set `K ⊆ ℂ` that contains, for every arc `γ` of length 1, an image of
`γ` under a proper rigid motion `z ↦ e^{iθ}z + t`, has Lebesgue measure at least `0.2410`
(`Worm.WormLowerAt (2410 / 10000)`, `Worm13a/StatementAt.lean`); hence the infimum of these areas is at least `0.2410`
(`Worm.OptimalAreaLowerAt (2410 / 10000)`). Toolchain: Lean 4 v4.35.0-rc3, Mathlib v4.35.0-rc3
(see `lake-manifest.json`).

The final theorems are `Worm.worm_lower_2410 : WormLowerAt (2410 / 10000)` and
`Worm.optimalAreaM_lower_2410 : OptimalAreaLowerAt (2410 / 10000)` in `WormN/Final.lean` (native track: the certificate
checks use `native_decide`). The certificate is `cert_w2410a`.

## Structure of the proof

1. **Reduction to a box of placements** (`WormSound/W1Gen.lean`, proofs in `WormSound/W1Proof/`). For every `τ > 0`, a
   convex cover of area below `τ` contains, after a proper motion, the 17 vertices of five fixed arcs
   (`WormCore/Family.lean`, the arcs L, T, U, C, S of the paper) placed at a point of the domain `D_τ`; `D_τ` lies in the
   root box of the certificate for `τ = 0.2410` (`WormSound/RootAt.lean`).
2. **The certificate checker** (`WormCore/`, core Lean plus Keller's dyadic intervals, no Mathlib): the root box is cut
   into cells, each part's skeleton splits its cells into units (`Tree.lean`), and every leaf box of a unit must pass
   `leafOK` (`Bound.lean`): every structure (a list of placed vertices with a fan, vertex-fan, chord-tree or small-list
   certificate) is valid on the box (`Check.lean`), and a convex combination of their shoelace areas is bounded below
   by more than `τ` (a second-order Taylor bound with a Gershgorin penalty, in interval arithmetic).
3. **Soundness of the checker** (`WormSound/`):
   - tree coverage: `Tree.lean` (the cells cover the root box, the units cover the cells, a checked unit and a checked
     chunk are covered by boxes that pass `leafOK`; proofs in `TreeProof/`);
   - validity of the structures and the winding of fans: `Valid.lean` (proofs in `IvSound/`, using the geometric
     lemmas of `Worm13a/GeomInterface.lean`: the shoelace area of a valid structure is at most the area of any convex
     set containing its vertices);
   - the area model and the bound: `ModelDefs.lean`, `Model.lean` (the shoelace area is exactly a quadratic in the box
     variables), `Quad.lean` (the Gershgorin box bound and the combination bound), `BoundSound.lean` (the interval
     computations enclose the real coefficients and bounds), `LeafSound.lean` (`leafOK_sound`);
   - assembly: `AssemblyAt.lean`, `wormLowerAt_of_certificate`: `WormLowerAt τ` follows from three facts about the
     certificate data (every skeleton walk succeeds, the units of all parts are the units listed by the chunks, every
     chunk check succeeds), for `τ` below the checker's `τ` with `D_τ` in the root box (`FinalAt.lean` for
     `τ = 0.2410`). These theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
4. **The certificate data and its checks** (`data/`, `WormN/`, generated): the skeletons and chunks (text, parsed in
   Lean) and one module per chunk proving `chunkCheck … txt = some units` by `native_decide`; `WormN/Cover.lean`
   proves the cover list and the skeleton walks, `WormN/All.lean` collects the chunks.

## Building and checking

The certificate data (`data/`: the skeletons, the 6,688 chunk files, `manifest.json` and `SHA256SUMS`; 10.7 GB) is
distributed as archives. Extract them inside this directory and check the files:

```
for a in worm_data_2410_*.tar.zst; do zstd -dc "$a" | tar -xf -; done
(cd data && sha256sum -c --quiet SHA256SUMS)
```

The toolchain (Lean 4 v4.35.0-rc3) and Mathlib (v4.35.0-rc3) are pinned by `lean-toolchain` and `lake-manifest.json`.

```
lake exe cache get
lake build WormSound.FinalAt     # the soundness chain and the instance tau = 0.2410 (a few minutes)
lake build WormN.Final           # the 6,688 chunk modules (native_decide) and the final theorems
tools/check_native.sh "$(lake env printenv LEAN_PATH)" data 6688
```

`tools/check_native.sh` ends with the line `ALL CHECKS PASSED`. `#print axioms Worm.worm_lower_2410` (for example in a file
run with `lake env lean`) lists `propext`, `Classical.choice`, `Quot.sound` and 6,690 axioms
`…._native.native_decide.ax_1_1`, one for each chunk theorem and one each for `WormN.cover` and `WormN.skel_ok`, and no
other axiom.

Resources: the chunk modules took about 443 thread-hours in total, at most 0.6 GB of memory per module, and `WormN.Final`
needs about 4.2 GB. The chunk modules are independent of each other. We built them in parallel on several machines with
`lean --setup` (the command that Lake runs), which gives the same `.olean` files as `lake build`.

## Trusted base

Lean's kernel and, for the native track, Lean's compiler: in this Lean version `native_decide` adds one axiom per
theorem, `X._native.native_decide.ax_1_1 : decide P = true`, for the decidable proposition `P` of that theorem
(`tools/check_native.lean` checks every such axiom's type against its theorem statement). The data is not trusted: the
checker recomputes every box from the root cells and re-verifies every leaf.

## Third-party code

`MoserWorm/` contains files of Ethan Keller's `moser-worm-improved-bounds` (Apache License 2.0; see
`third_party/moser-worm-improved-bounds/` for the licence, citation and upstream checksums), ported to this toolchain.
Changed files carry a "Modified" notice below the upstream header.
