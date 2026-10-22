# Worm certificate data for the Lean checker: format and module layout (spec, 2026-10-21)

Interface between the converter (tools/wconvert.py), the Lean parser and checker (WormCore/Tree.lean,
WormCore/Check.lean) and the native-track shard modules. The data is untrusted. The checker recomputes every box from the
root cells, re-verifies every leaf, and the assembly checks that the units checked cover all cells.

## Source

The input is the frozen certificate cert_w2410a: 16,384 parts with 264,084,910 leaves (the format was first
used for cert_w2400a, 189,594,732 leaves).

- `partNNNN.json`: the header (famspec, gid_map, lo, hi, split0, nparts, maxsmall, tau).
- `partNNNN.npy`: DFS codes per node. 0–11 split that coordinate, lower half first; 254 is a one-structure leaf;
  253 is a Lemma K leaf.
- `partNNNN.leaves.jsonl.gz`: one record per leaf in DFS order: `{"S": [{"v": ids, "m": small|fan|chord, "z": [x, y],
  "t": tree}], "w": weights}`.

## Root and cells (WormCore.Family, WormCore.Tree)

- `rootW.lo`, `rootW.hi`: the root box; per coordinate, the exact value of the header float times 2^120. The
  coordinates per body b = 1..4 are 3(b−1) (angle θ), 3(b−1)+1 (x), 3(b−1)+2 (y).
- `rootW.split0` = [4,2,2,16,2,2,8,2,2,8,2,2]. Cell c (0 ≤ c < 1,048,576) is the row-major grid cell
  (`cellBox rootW c`). Part p owns cells p, p + 16384, …, p + 63·16384, in this order (the `cells[part::nparts]` of the
  certificate).
- Boxes are pairs `(lo hi : Array Int)` of mantissas at scale 2^-120. Splitting coordinate k at the exact midpoint is
  `halves`; a midpoint that is not exact is an error.

## Skeleton of a part: `skel/sNNNNN.txt`

The skeleton is one line over the alphabet `0-9 a b U`. It is the DFS of the part's 64 cells in order, down to
the units:

- `0`–`9`, `a`, `b`: split coordinate 0–11, then the lower half's subtree, then the upper half's;
- `U`: a unit, i.e. a subtree of the certificate with at most UNIT = 50,000 leaves. Units are numbered 0, 1, … in DFS
  order within the part.

`unitBoxes rootW p skel` returns the unit boxes in order, or `none` if the skeleton is malformed (fuel, inexact
midpoint, bad character, leftover characters).

## Chunk: `chunks/cNNNNN.txt`

A chunk is a single line of tokens separated by single spaces, grouping consecutive units (over all parts, in order)
with about CHUNK = 50,000 leaves:

```
T<n> <st_0> … <st_{n-1}>                 structure table
U<p>.<u> C<codes> <rec> … <rec>           one block per unit: part p, unit u, subtree codes, one record per leaf
```

- `<st>` takes one of three forms:
  - `s<ids>`: small list;
  - `f<ids>|<zx>|<zy>`: fan around z = (zx, zy)·2^-56, with decimal integers;
  - `c<ids>|<tree>`: chord tree.
  - `ids` has one letter per global vertex (`a` + id, 17 vertices), and the order is the list order.
- `<tree>` is one of `s`, `f<r>`, `c<s><t><left><right>`, where r, s, t are one character each (`0-9 a-z`).
- `<codes>` uses the alphabet `0-9 a b L K`. It is the DFS of the unit's subtree from the unit box; `L` and `K` are
  leaves, and the checker treats them alike.
- `<rec>` is either `<i>` (table index in base 36, weight 2^56 = 1) or `<i>,<w>;<i>,<w>;…` (Lemma K: base-36 indices
  and decimal weight mantissas at 2^-56, exact floors of w_i/Σw times 2^56, so Σ ≤ 2^56).
- Every unit block must have exactly as many records as `L`/`K` in its codes.

`chunkOK famF rootW maxsmallW tauHiW rdepth skel txt : Bool` parses the table, then for every unit block takes the box
`(unitBoxes rootW p (skel p))[u]` and walks the codes. Every leaf must pass `leafOKR … rdepth lo hi rec`, and all records
must be used. `chunkUnits txt` lists the `(p, u)` of the chunk in order.

## Native-track modules (to be generated)

- `WormN/SkelNNN.lean`: `def skelNNN : Array String` holds the skeletons of a range of parts, via `include_str`.
  `def skelOf (p : Nat) : String` is the lookup.
- `WormN/ChunkNNNNN.lean`:
  `theorem chunk_NNNNN : chunkOK famF rootW maxsmallW tauHiW 6 skelOf (include_str "../data/chunks/cNNNNN.txt") = true
  := by native_decide`.
  The chunk text should be a separate `def` so that `chunkUnits` can be evaluated on the same term.
- `WormN/Cover.lean`: the list of all `(p, u)` with `u < (unitBoxes rootW p (skelOf p)).size`, equal to the
  concatenation of `chunkUnits` over all chunks (`decide`, or `native_decide` on the native track).
- Soundness (WormCore/*Sound.lean) proves three things:
  - `unitBoxes` covers the cells of the part;
  - `unitWalk` covers the unit box by leaf boxes that pass `leafOKR`;
  - `leafOKR` is sound for the area bound.

## Sizes (pilot, parts 0–39)

- 57,067 leaves: 2 chunks of 848,960 and 113,735 bytes, about 17 bytes per leaf. The full certificate is about
  3.2 GB of text.
- Native speed is 2.4–2.5 ms per leaf on a loaded 88-thread server. Both chunks pass, with 0 failing units.
