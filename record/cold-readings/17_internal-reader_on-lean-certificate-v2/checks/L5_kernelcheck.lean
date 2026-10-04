import Lean

-- L5_kernelcheck.lean — Grepy Sello (cold reader, mission LEAN_2), 4 Oct 2026.
-- Run from material/project:  lake env lean ../../checks/L5_kernelcheck.lean   (under vigia.sh)
-- Second design (L4 = Environment.replay on a Mathlib-only base was killed at 4.8 GB: two copies of
-- Mathlib in one process). Here ONE environment is loaded inside the evaluation command: the compiled
-- project (EvenAll.PartBC + OddEquality.PartD, Mathlib included). For every project theorem /
-- definition / opaque in the cone of the five root theorems, its compiled (type, value) pair is
-- re-submitted to the Lean kernel under a FRESH name (`Kernel.Environment.addDecl`): the kernel
-- re-type-checks the compiled proof term against the compiled statement. Inductive types,
-- constructors and recursors are counted, not re-checked. A negative control (a wrong proof) must be
-- rejected. Parameters: gsStart (index into the sorted list) and gsBudgetMs (time budget).

open Lean Elab Command

def gsStart : Nat := 0
def gsBudgetMs : Nat := 560000

partial def gsCollect (env : Environment) (n : Name) (acc : NameSet) : NameSet := Id.run do
  if acc.contains n then return acc
  let mut acc := acc.insert n
  match env.find? n with
  | none => return acc
  | some ci =>
    for c in ci.getUsedConstantsAsSet.toList do
      acc := gsCollect env c acc
    return acc

def gsFresh (n : Name) : Name := Name.str n "_gsSelloRecheck"

/-- the declaration to re-submit for a compiled constant, if it is a theorem / definition / opaque -/
def gsDecl (ci : ConstantInfo) : Option Declaration :=
  match ci with
  | ConstantInfo.thmInfo v =>
    let t : TheoremVal := {
      name := gsFresh v.name
      levelParams := v.levelParams
      type := v.type
      value := v.value
      all := [gsFresh v.name] }
    some (Declaration.thmDecl t)
  | ConstantInfo.defnInfo v =>
    let d : DefinitionVal := {
      name := gsFresh v.name
      levelParams := v.levelParams
      type := v.type
      value := v.value
      hints := v.hints
      safety := v.safety
      all := [gsFresh v.name] }
    some (Declaration.defnDecl d)
  | ConstantInfo.opaqueInfo v =>
    let o : OpaqueVal := {
      name := gsFresh v.name
      levelParams := v.levelParams
      type := v.type
      value := v.value
      isUnsafe := v.isUnsafe
      all := [gsFresh v.name] }
    some (Declaration.opaqueDecl o)
  | _ => none

def gsIsAxiom (ci : ConstantInfo) : Bool :=
  match ci with
  | ConstantInfo.axiomInfo _ => true
  | _ => false

#eval show CommandElabM Unit from do
  let full ← importModules #[{ module := `RequestProject.EvenAll.PartBC },
    { module := `RequestProject.OddEquality.PartD }] {}
  let kenv := full.toKernelEnv
  let roots : List Name := [`EvenAll.mainTheorem', `OddEquality.D1, `OddEquality.D2_DJ,
    `OddEquality.D2_M, `OddTheorem.theoremO]
  let mut acc : NameSet := {}
  for r in roots do
    acc := gsCollect full r acc
  -- project constants of the cone, sorted by (module index, name)
  let mut items : Array (Nat × String × Name) := #[]
  for n in acc.toList do
    if let some idx := full.getModuleIdxFor? n then
      let m := full.header.moduleNames[idx.toNat]!
      if (`RequestProject).isPrefixOf m then
        items := items.push (idx.toNat, n.toString, n)
  items := items.qsort (fun a b => a.1 < b.1 || (a.1 == b.1 && a.2.1 < b.2.1))
  logInfo m!"project constants in the cone of the five roots: {items.size}"
  -- negative control: the statement of EvenAll.mainTheorem' with the proof of OddTheorem.theoremO
  match full.find? `EvenAll.mainTheorem', full.find? `OddTheorem.theoremO with
  | some (ConstantInfo.thmInfo a), some (ConstantInfo.thmInfo b) =>
    let badVal : TheoremVal := {
      name := `gsSelloControl
      levelParams := a.levelParams
      type := a.type
      value := b.value
      all := [`gsSelloControl] }
    match kenv.addDecl {} (Declaration.thmDecl badVal) with
    | Except.ok _ => logInfo m!"NEGATIVE CONTROL: accepted (BAD: the check cannot fire)"
    | Except.error _ => logInfo m!"NEGATIVE CONTROL: rejected by the kernel, as it must be"
  | _, _ => logInfo m!"NEGATIVE CONTROL: roots not found"
  let t0 ← IO.monoMsNow
  let mut nOk := 0
  let mut nFail := 0
  let mut nSkip := 0
  let mut nAxiom := 0
  let mut lastIdx := gsStart
  let mut fails : Array Name := #[]
  let mut stopped := false
  for i in [gsStart:items.size] do
    if (← IO.monoMsNow) - t0 > gsBudgetMs then
      stopped := true
      break
    let n := items[i]!.2.2
    lastIdx := i
    match full.find? n with
    | none =>
      nFail := nFail + 1
      fails := fails.push n
    | some ci =>
      if gsIsAxiom ci then nAxiom := nAxiom + 1
      match gsDecl ci with
      | none => nSkip := nSkip + 1
      | some d =>
        match kenv.addDecl {} d with
        | Except.ok _ => nOk := nOk + 1
        | Except.error _ =>
          nFail := nFail + 1
          fails := fails.push n
  let t1 ← IO.monoMsNow
  logInfo m!"checked items {gsStart}..{lastIdx} of {items.size} in {t1 - t0} ms (stopped by budget: {stopped}): re-checked OK {nOk}, FAILED {nFail}, skipped (inductive/ctor/rec/quot) {nSkip}, axioms {nAxiom}"
  if fails.size > 0 then
    logInfo m!"FAILED: {fails.toList.take 50}"
