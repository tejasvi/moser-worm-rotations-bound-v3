import Lean
import WormN.Final

/-!
# Check of the native-track theorems (WormN)

Run with the olean tree of the build on `LEAN_PATH` (see tools/check_native.sh). For the `N` chunk theorems
(`WORMN_NCHUNKS`, default 4625), `WormN.cover`, `WormN.skel_ok` and `WormN.chunks_ok` it checks:

* each statement is exactly the intended one: `chunk_cNNNNN : chunkCheck famW rootW maxsmallW tauHiW rdepthW skelOf
  txt_cNNNNN = some units_cNNNNN`, the `cover` and `skel_ok` statements, the `chunks_ok` statement, and the definition of
  `allUnits` as `WormCore.Sound.allUnitsOf skelOf` (`WormSound/AssemblyBase.lean`);
* the axioms of each `native_decide` theorem are `propext`, `Classical.choice`, `Quot.sound` and exactly one axiom named
  under the theorem, of type `decide P = true` where `P` is the theorem's own statement (this is the axiom that
  `native_decide` adds in Lean v4.35.0-rc3);
* the axioms of `chunks_ok` are the standard ones and exactly the axioms of the `N` chunk theorems;
* if `WORMN_DATA` is set to the data directory: each `txt_cNNNNN` is a string literal equal to `chunks/cNNNNN.txt`;
* the final theorems of `WormN.Final` (certificate cert_w2410a): `Worm.worm_lower_2410 : Worm.WormLowerAt (2410 / 10000)`
  and `Worm.optimalAreaM_lower_2410 : Worm.OptimalAreaLowerAt (2410 / 10000)`, each with exactly the standard axioms, the
  `N` chunk axioms and the axioms of `cover` and `skel_ok` (in particular no `sorryAx`).

`LEAN_PATH` must include the Mathlib packages (`WormN.Final` imports `WormSound.FinalAt`).

The output ends with `ALL CHECKS PASSED`; any failure is listed and makes `lean` exit with an error.
-/

open Lean Elab Command Term Meta

namespace WormNCheck

def stdAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

def pad5 (n : Nat) : String := let s := toString n; String.ofList (List.replicate (5 - s.length) '0') ++ s

def wn (s : String) : Name := Name.mkStr `WormN s

/-- The extra axiom of a `native_decide` theorem, after checking that its type is `decide (statement) = true`. -/
def nativeAxiom (env : Environment) (thm : Name) (axs : Array Name) : Except String Name := do
  let some ci := env.find? thm | throw s!"{thm}: missing"
  let .thmInfo _ := ci | throw s!"{thm}: not a theorem"
  let extra := axs.filter (fun a => !stdAxioms.contains a)
  unless extra.size = 1 do throw s!"{thm}: axioms {axs}"
  let ax := extra[0]!
  unless thm.isPrefixOf ax do throw s!"{thm}: axiom {ax} is not named under the theorem"
  let some (.axiomInfo ai) := env.find? ax | throw s!"{thm}: {ax} is not an axiom"
  unless ai.levelParams.isEmpty && ci.levelParams.isEmpty do throw s!"{thm}: universe parameters"
  let some (_, lhs, rhs) := ai.type.eq? | throw s!"{thm}: the type of {ax} is not an equation"
  unless rhs.isConstOf ``Bool.true do throw s!"{thm}: the right side of {ax} is not `true`"
  unless lhs.isAppOfArity ``Decidable.decide 2 do throw s!"{thm}: the left side of {ax} is not `decide _`"
  unless lhs.appFn!.appArg! == ci.type do throw s!"{thm}: the proposition decided in {ax} is not the statement"
  return ax

/-- The statement of chunk theorem `k`. -/
def chunkStmt (env : Environment) (k : Nat) : Except String Unit := do
  let c := "c" ++ pad5 k
  let thm := wn s!"chunk_{c}"
  let some ci := env.find? thm | throw s!"{thm}: missing"
  let some (_, lhs, rhs) := ci.type.eq? | throw s!"{thm}: not an equation"
  let lhs' := mkAppN (Lean.mkConst ``WormCore.chunkCheck) #[Lean.mkConst ``WormCore.famW, Lean.mkConst ``WormCore.rootW,
    Lean.mkConst ``WormCore.maxsmallW, Lean.mkConst ``WormCore.tauHiW, Lean.mkConst ``WormCore.rdepthW, Lean.mkConst `WormN.skelOf,
    Lean.mkConst (wn s!"txt_{c}")]
  unless lhs == lhs' do throw s!"{thm}: left side differs"
  unless rhs.isAppOfArity ``Option.some 2 && rhs.appArg! == Lean.mkConst (wn s!"units_{c}") do
    throw s!"{thm}: right side differs"
  let some (.defnInfo ti) := env.find? (wn s!"txt_{c}") | throw s!"{thm}: txt_{c} is not a definition"
  unless ti.value matches .lit (.strVal _) do throw s!"{thm}: txt_{c} is not a string literal"

/-- Elaborate `stx` (a proposition or term) and compare it with `e` (up to binder names). -/
def sameAs (stx : Term) (e : Expr) : CommandElabM Bool := liftTermElabM do
  let t ← elabTerm stx none
  synthesizeSyntheticMVarsNoPostponing
  let t ← instantiateMVars t
  return t == e

def main : CommandElabM Unit := do
  let env ← getEnv
  let n := ((← IO.getEnv "WORMN_NCHUNKS").bind String.toNat?).getD 4625
  let data? ← IO.getEnv "WORMN_DATA"
  let mut errs : Array String := #[]
  let mut chunkAxs : NameSet := {}
  let mut ndata := 0
  for k in [0:n] do
    let thm := wn s!"chunk_c{pad5 k}"
    if let .error e := chunkStmt env k then errs := errs.push e
    let axs ← if env.contains thm then liftCoreM (collectAxioms thm) else pure #[]
    match nativeAxiom env thm axs with
    | .ok ax => chunkAxs := chunkAxs.insert ax
    | .error e => errs := errs.push e
    if let some dir := data? then
      if let some (.defnInfo ti) := env.find? (wn s!"txt_c{pad5 k}") then
        if let .lit (.strVal s) := ti.value then
          let f ← IO.FS.readFile s!"{dir}/chunks/c{pad5 k}.txt"
          if s == f then ndata := ndata + 1 else errs := errs.push s!"{thm}: txt differs from {dir}/chunks/c{pad5 k}.txt"
  -- no other chunk theorems
  let extraChunks : Nat := env.constants.fold (init := 0) fun acc nm _ =>
    match nm with
    | .str (.str .anonymous "WormN") s =>
      if s.startsWith "chunk_c" && ((s.drop 7).toNat?.map (fun x => decide (x ≥ n))).getD true then acc + 1 else acc
    | _ => acc
  if extraChunks > 0 then errs := errs.push s!"{extraChunks} constants WormN.chunk_c* beyond the expected {n}"
  -- cover and skel_ok
  let mut certAxs : NameSet := {}
  for thm in [`WormN.cover, `WormN.skel_ok] do
    if env.contains thm then
      let axs ← liftCoreM (collectAxioms thm)
      match nativeAxiom env thm axs with
      | .ok ax => certAxs := certAxs.insert ax
      | .error e => errs := errs.push e
  match env.find? `WormN.cover with
  | some cov =>
    unless ← sameAs (← `(WormN.allUnits = List.flatten WormN.unitLists)) cov.type do
      errs := errs.push "WormN.cover: statement differs"
  | none => errs := errs.push "WormN.cover: missing"
  match env.find? `WormN.skel_ok with
  | some sk =>
    unless ← sameAs (← `((List.range WormCore.rootW.nparts).all
        (fun p => (WormCore.unitBoxes WormCore.rootW p (WormN.skelOf p)).isSome) = true)) sk.type do
      errs := errs.push "WormN.skel_ok: statement differs"
  | none => errs := errs.push "WormN.skel_ok: missing"
  match env.find? `WormN.allUnits with
  | some (.defnInfo au) =>
    unless ← sameAs (← `((List.range WormCore.rootW.nparts).flatMap fun p =>
        (List.range ((WormCore.unitBoxes WormCore.rootW p (WormN.skelOf p)).getD #[]).size).map (p, ·))) au.value do
      errs := errs.push "WormN.allUnits: definition differs from the brief"
  | _ => errs := errs.push "WormN.allUnits: missing or not a definition"
  -- chunks_ok
  match env.find? `WormN.chunks_ok with
  | some ok =>
    unless ← sameAs (← `(∀ L ∈ WormN.unitLists, ∃ txt, WormCore.chunkCheck WormCore.famW WormCore.rootW
        WormCore.maxsmallW WormCore.tauHiW WormCore.rdepthW WormN.skelOf txt = some L)) ok.type do
      errs := errs.push "WormN.chunks_ok: statement differs"
  | none => errs := errs.push "WormN.chunks_ok: missing"
  let axs ← if env.contains `WormN.chunks_ok then liftCoreM (collectAxioms `WormN.chunks_ok) else pure #[]
  let extra := axs.filter (fun a => !stdAxioms.contains a)
  unless extra.size = n && extra.all chunkAxs.contains && chunkAxs.size = n do
    errs := errs.push s!"WormN.chunks_ok: {extra.size} non-standard axioms, {(extra.filter (!chunkAxs.contains ·)).size} not chunk axioms, {chunkAxs.size} chunk axioms"
  let std := axs.filter (fun a => stdAxioms.contains a)
  logInfo m!"chunk theorems checked: {n}; native axioms: {chunkAxs.size}; chunks_ok axioms: {axs.size} = standard {std.toList} + {extra.size} chunk axioms; txt literals equal to the data files: {if data?.isSome then toString ndata else "not checked"}"
  -- the final theorems (cert_w2410a)
  let stmtW ← `(Worm.WormLowerAt (2410 / 10000))
  let stmtO ← `(Worm.OptimalAreaLowerAt (2410 / 10000))
  let finals : List (Name × Term) := [(`Worm.worm_lower_2410, stmtW), (`Worm.optimalAreaM_lower_2410, stmtO)]
  for (thm, stmt) in finals do
    match env.find? thm with
    | some ci =>
      unless ← sameAs stmt ci.type do errs := errs.push s!"{thm}: statement differs"
      let axs ← liftCoreM (collectAxioms thm)
      let ex := axs.filter (fun a => !stdAxioms.contains a)
      let expected := chunkAxs.size + certAxs.size
      unless ex.size = expected && ex.all (fun a => chunkAxs.contains a || certAxs.contains a) && certAxs.size = 2 do
        errs := errs.push s!"{thm}: {ex.size} non-standard axioms, expected {expected} (chunk axioms + cover + skel_ok)"
      if axs.contains ``sorryAx then errs := errs.push s!"{thm}: depends on sorryAx"
      logInfo m!"{thm}: axioms {axs.size} = standard {(axs.filter (fun a => stdAxioms.contains a)).toList} + {ex.size} native_decide axioms ({(ex.filter chunkAxs.contains).size} chunk, {(ex.filter certAxs.contains).size} cover/skel_ok)"
    | none => errs := errs.push s!"{thm}: missing"
  if errs.isEmpty then
    logInfo "ALL CHECKS PASSED"
  else
    for e in errs[:min errs.size 50] do logError e
    throwError s!"{errs.size} CHECKS FAILED"

end WormNCheck

#eval WormNCheck.main
