import WormCore.Family

open WormCore MoserWorm

def pad5 (n : Nat) : String := let s := toString n; String.ofList (List.replicate (5 - s.length) '0') ++ s

/-- Diagnostic walk of a unit: number of leaves, failing leaf indices (first few) with reasons. -/
partial def diagWalk (F : Fam) (cs : List Char) (st : List (Array Int × Array Int)) (recs : List Rec) (idx : Nat)
    (acc : Array String) (nleaf : Nat) : Array String × Nat × List Rec :=
  match cs, st with
  | [], _ => (acc, nleaf, recs)
  | c :: cs', (lo, hi) :: st' =>
    if c = 'L' ∨ c = 'K' then
      match recs with
      | r :: rs =>
        let ok := leafOKR F maxsmallW tauHiW 6 lo hi r
        let acc' := if ok || acc.size ≥ 5 then acc else
          let C := mkCtx F lo hi
          let v := r.sts.map fun (s, lam) =>
            let detail := match s with
              | .fan vs zx zy =>
                let z : V2 := (DIval.pt zx, DIval.pt zy)
                let m := vs.length
                let dets := (List.range m).map fun j => fanDetLo C z (at' vs j) (at' vs (j + 1))
                let va := vs.toArray
                let PD := (List.range m).map fun i => (List.range m).map fun d =>
                  (decide (0 < fanDetLo C z va[i]! va[(i + d) % m]!), decide (0 < fanDotLo C z va[i]! va[(i + d) % m]!))
                let cents := va.toList.map fun g => (let x : V2 := C.X0[g]!; (Float.ofInt x.1.lo / Float.ofInt dfxOne, Float.ofInt x.2.lo / Float.ofInt dfxOne))
                s!"fan {vs} z {(Float.ofInt zx / Float.ofInt dfxOne, Float.ofInt zy / Float.ofInt dfxOne)} pts {cents} dets {dets.map (fun d => Float.ofInt d / Float.ofInt dfxOne)} PD {PD}"
              | .chord vs t => s!"chord {vs} {repr t}"
              | .small vs => s!"small {vs}"
            (stOK C maxsmallW s, detail, lam)
          let lb := leafBound C r.sts
          acc.push s!"leaf {idx}: valid/weights {v} sumw-1 {((r.sts.map (·.2)).foldl (· + ·) 0) - dfxOne} bound-tau {Float.ofInt (lb - tauHiW) / Float.ofInt dfxOne}"
        diagWalk F cs' st' rs (idx + 1) acc' (nleaf + 1)
      | [] => (acc.push "records exhausted", nleaf, [])
    else match codeDim c with
      | some k => match halves lo hi k with
        | some (l, u) => diagWalk F cs' (l :: u :: st') recs idx acc nleaf
        | none => (acc.push s!"inexact midpoint at leaf {idx}", nleaf, recs)
      | none => (acc.push s!"bad code {c}", nleaf, recs)
  | _ :: _, [] => (acc.push "stack empty", nleaf, recs)

def main (args : List String) : IO Unit := do
  let dir := args[0]!
  let F := mkFam famArcs famGid
  for cf in args.drop 1 do
    let txt ← IO.FS.readFile cf
    let toks := (txt.splitOn " ").toArray
    let n := (String.ofList (toks[0]!.toList.drop 1)).toNat!
    let table := ((toks.extract 1 (n + 1)).map parseSt)
    IO.println s!"{cf}: table {n}, parsed {(table.filter Option.isSome).size}"
    let table := table.map fun o => o.getD default
    let t0 ← IO.monoMsNow
    let mut i := n + 1
    let mut nunits := 0
    let mut nleaves := 0
    let mut nfailunits := 0
    while i < toks.size do
      let t := toks[i]!
      let pu := (String.ofList (t.toList.drop 1)).splitOn "."
      let p := pu[0]!.toNat!
      let u := pu[1]!.toNat!
      let cs := String.ofList (toks[i + 1]!.toList.drop 1)
      let skelTxt ← IO.FS.readFile s!"{dir}/skel/s{pad5 p}.txt"
      let skel := String.ofList (skelTxt.toList.filter (fun c => c ≠ (Char.ofNat 10)))
      let nl := cs.foldl (fun a c => if c = 'L' ∨ c = 'K' then a + 1 else a) 0
      let recs := ((toks.extract (i + 2) (i + 2 + nl)).toList.map (parseRec table))
      match unitBoxes rootW p skel with
      | none => IO.println s!"unit {p}.{u}: skeleton walk failed"
      | some boxes =>
        if u ≥ boxes.size then IO.println s!"unit {p}.{u}: index {u} >= {boxes.size}"
        else
          if !(recs.all Option.isSome) then IO.println s!"unit {p}.{u}: record parse failure"
          let (fails, nlf, rest) := diagWalk F cs.toList [boxes[u]!] (recs.filterMap id) 0 #[] 0
          nleaves := nleaves + nlf
          if fails.size > 0 || rest.length > 0 then
            nfailunits := nfailunits + 1
            if nfailunits ≤ 4 then
              IO.println s!"unit {p}.{u} (leaves {nlf}, rest {rest.length}):"
              for f in fails do IO.println s!"   {f}"
      nunits := nunits + 1
      i := i + 2 + nl
    let t1 ← IO.monoMsNow
    IO.println s!"{cf}: units {nunits} leaves {nleaves} failing units {nfailunits} ms {t1 - t0}"
    -- the production check (chunkCheck) on the same data
    let parts := ((toks.toList.filterMap parseUnitHead).map (·.1)).eraseDups
    let mut skels : Array (Nat × String) := #[]
    for p in parts do
      let s ← IO.FS.readFile s!"{dir}/skel/s{pad5 p}.txt"
      skels := skels.push (p, String.ofList (s.toList.filter (fun c => c ≠ (Char.ofNat 10))))
    let sk := skels
    let skelF := fun p => ((sk.find? (·.1 = p)).map (·.2)).getD ""
    let t2 ← IO.monoMsNow
    let res := chunkCheck F rootW maxsmallW tauHiW 6 skelF txt
    let t3 ← IO.monoMsNow
    IO.println s!"{cf}: chunkCheck {match res with | some l => s!"some ({l.length} units)" | none => "none"} ms {t3 - t2}"
