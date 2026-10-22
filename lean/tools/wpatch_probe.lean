import WormCore.Family

/-!
# Patch probe for failing leaves (used by tools/wpatch.py)

usage: `lean --load-dynlib=<WormInterval .so> --load-dynlib=<WormCore .so> --run tools/wpatch_probe.lean DATADIR CHUNK
[MAXEXTRA]` with the WormCore oleans on `LEAN_PATH` (the dynlibs make `leafOKR` run as native code).

For every leaf of the chunk `DATADIR/chunks/CHUNK.txt` that fails `leafOKR famW maxsmallW tauHiW rdepthW` on its box, it
searches a subdivision of the leaf box by exact midpoint splits (`halves`), with the leaf's record on every piece:
first the 12 single splits (one where both halves pass is taken), else best-first (the split maximizing the smaller
`leafBound - tauHiW` of the two halves) with recursion into the failing halves, up to MAXEXTRA (default 4) extra levels.
It prints one JSON line per failing leaf: chunk, unit, leaf index (DFS order within the unit), the leaf letter, the
record token, the margin `leafBound - tauHiW` before (mantissa at 2^-56), the replacement codes (DFS preorder, alphabet
`0-9 a b` plus the leaf letter) or null, and the margin and `leafOKR` result of every new leaf. WormCore is unchanged.
-/

open WormCore MoserWorm

def pad5 (n : Nat) : String := let s := toString n; String.ofList (List.replicate (5 - s.length) '0') ++ s

def codeChar (k : Nat) : Char := if k < 10 then Char.ofNat ('0'.toNat + k) else Char.ofNat ('a'.toNat + k - 10)

/-- The leaf boxes of a unit's codes from its box, in DFS order, with their letters. -/
partial def leafBoxes : List Char → List (Array Int × Array Int) → Array (Array Int × Array Int × Char) →
    Option (Array (Array Int × Array Int × Char))
  | [], [], acc => some acc
  | c :: cs, (lo, hi) :: st, acc =>
    if c = 'L' ∨ c = 'K' then leafBoxes cs st (acc.push (lo, hi, c))
    else match codeDim c with
      | some k => match halves lo hi k with
        | some (l, u) => leafBoxes cs (l :: u :: st) acc
        | none => none
      | none => none
  | _, _, _ => none

def margin (lo hi : Array Int) (r : Rec) : Int := leafBound (mkCtx famW lo hi) r.sts - tauHiW

def ok6 (lo hi : Array Int) (r : Rec) : Bool := leafOKR famW maxsmallW tauHiW rdepthW lo hi r

/-- Codes (DFS preorder) of a subdivision of `[lo, hi]` whose pieces all pass `ok6`, with at most `d` extra levels. -/
partial def fix (c : Char) (r : Rec) (lo hi : Array Int) : Nat → Option String
  | 0 => if ok6 lo hi r then some (String.singleton c) else none
  | d + 1 =>
    if ok6 lo hi r then some (String.singleton c) else
    let cands := (List.range lo.size).filterMap fun k => (halves lo hi k).map fun (l, u) => (k, l, u)
    match cands.find? (fun (_, l, u) => ok6 l.1 l.2 r && ok6 u.1 u.2 r) with
    | some (k, _, _) => some (String.ofList [codeChar k, c, c])
    | none =>
      let scored := cands.map fun (k, l, u) => (min (margin l.1 l.2 r) (margin u.1 u.2 r), k, l, u)
      match scored.foldl (fun acc x => match acc with
          | none => some x
          | some y => if x.1 > y.1 then some x else acc)
          (none : Option (Int × Nat × (Array Int × Array Int) × (Array Int × Array Int))) with
      | some (_, k, l, u) => do
        let fl ← fix c r l.1 l.2 d
        let fu ← fix c r u.1 u.2 d
        some (String.singleton (codeChar k) ++ fl ++ fu)
      | none => none

def jstr (s : String) : String := "\"" ++ s ++ "\""

def main (args : List String) : IO Unit := do
  let dir := args[0]!
  let name := args[1]!
  let maxExtra := (args[2]?.bind String.toNat?).getD 4
  let txt ← IO.FS.readFile s!"{dir}/chunks/{name}.txt"
  let toks := (txt.splitOn " ").toArray
  let n := (String.ofList (toks[0]!.toList.drop 1)).toNat!
  let table := (toks.extract 1 (n + 1)).map fun t => (parseSt t).getD default
  let mut i := n + 1
  let mut nfail := 0
  let mut nleaves := 0
  while i < toks.size do
    let some (p, u) := parseUnitHead toks[i]! | throw (IO.userError s!"bad unit head at token {i}")
    let cs := String.ofList (toks[i + 1]!.toList.drop 1)
    let nl := countLeaves cs
    let skel ← IO.FS.readFile s!"{dir}/skel/s{pad5 p}.txt"
    let some boxes := unitBoxes rootW p skel | throw (IO.userError s!"skeleton walk failed for part {p}")
    let some lbs := leafBoxes cs.toList [boxes[u]!] #[] | throw (IO.userError s!"codes walk failed for unit {p}.{u}")
    for j in [0:nl] do
      let tok := toks[i + 2 + j]!
      let some r := parseRec table tok | throw (IO.userError s!"bad record {tok}")
      let (lo, hi, c) := lbs[j]!
      if !ok6 lo hi r then
        nfail := nfail + 1
        let m0 := margin lo hi r
        match fix c r lo hi maxExtra with
        | some code =>
          let some sub := leafBoxes code.toList [(lo, hi)] #[] | throw (IO.userError "internal: replacement walk failed")
          let ms := sub.toList.map fun (l, h, _) => toString (margin l h r)
          let oks := sub.toList.map fun (l, h, _) => if ok6 l h r then "true" else "false"
          IO.println ("{\"chunk\": " ++ jstr name ++ ", \"unit\": " ++ jstr s!"{p}.{u}" ++ s!", \"leaf\": {j}, " ++
            "\"letter\": " ++ jstr (String.singleton c) ++ ", \"record\": " ++ jstr tok ++ s!", \"margin_before\": {m0}, " ++
            "\"code_before\": " ++ jstr (String.singleton c) ++ ", \"code_after\": " ++ jstr code ++
            s!", \"extra_leaves\": {sub.size - 1}, \"margins_after\": [{", ".intercalate ms}], " ++
            s!"\"ok_after\": [{", ".intercalate oks}]}")
        | none =>
          IO.println ("{\"chunk\": " ++ jstr name ++ ", \"unit\": " ++ jstr s!"{p}.{u}" ++ s!", \"leaf\": {j}, " ++
            "\"letter\": " ++ jstr (String.singleton c) ++ ", \"record\": " ++ jstr tok ++ s!", \"margin_before\": {m0}, " ++
            "\"code_before\": " ++ jstr (String.singleton c) ++ ", \"code_after\": null}")
    nleaves := nleaves + nl
    i := i + 2 + nl
  IO.eprintln s!"{name}: leaves {nleaves}, failing leaves {nfail}"
