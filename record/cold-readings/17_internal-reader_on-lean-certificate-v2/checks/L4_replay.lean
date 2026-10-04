import Mathlib

-- L4_replay.lean — Grepy Sello (cold reader, mission LEAN_2), 4 Oct 2026.
-- Run from material/project:  lake env lean ../../checks/L4_replay.lean   (under vigia.sh, Lean cap)
-- The current environment contains Mathlib only (the project imports nothing else).
-- Inside #eval: load the COMPILED project modules of the final theorem and of Theorem O, collect
-- every declaration of the project that the five root theorems use (types and proofs, transitively),
-- and replay them all through the Lean kernel (`Lean.Environment.replay`, core Lean) on top of the
-- Mathlib-only environment. If a compiled .olean held a declaration that does not type-check
-- (e.g. a forged or unchecked proof), the replay fails. Nothing is written to disk.

open Lean Elab Command

partial def gsCollect (env : Environment) (n : Name) (acc : NameSet) : NameSet := Id.run do
  if acc.contains n then return acc
  let mut acc := acc.insert n
  match env.find? n with
  | none => return acc
  | some ci =>
    for c in ci.getUsedConstantsAsSet.toList do
      acc := gsCollect env c acc
    return acc

#eval show CommandElabM Unit from do
  let base ← getEnv
  let full ← importModules #[{ module := `RequestProject.EvenAll.PartBC },
    { module := `RequestProject.OddEquality.PartD }] {}
  let roots : List Name := [`EvenAll.mainTheorem', `OddEquality.D1, `OddEquality.D2_DJ,
    `OddEquality.D2_M, `OddTheorem.theoremO]
  for r in roots do
    logInfo m!"root {r} present in the compiled project: {full.contains r}"
  let mut acc : NameSet := {}
  for r in roots do
    acc := gsCollect full r acc
  let mut newC : Std.HashMap Name ConstantInfo := {}
  let mut nThm := 0
  let mut nDef := 0
  let mut nAx := 0
  let mut nInd := 0
  let mut nOther := 0
  let mut noValue := 0
  for n in acc.toList do
    match full.getModuleIdxFor? n with
    | some idx =>
      let m := full.header.moduleNames[idx.toNat]!
      if (`RequestProject).isPrefixOf m then
        if let some ci := full.find? n then
          newC := newC.insert n ci
          match ci with
          | .thmInfo _ => nThm := nThm + 1
          | .defnInfo _ => nDef := nDef + 1
          | .axiomInfo _ => nAx := nAx + 1
          | .inductInfo _ => nInd := nInd + 1
          | _ => nOther := nOther + 1
          if ci.value?.isNone && !(ci matches .inductInfo _) && !(ci matches .ctorInfo _) &&
              !(ci matches .recInfo _) then
            noValue := noValue + 1
    | none => pure ()
  logInfo m!"project constants in the cone of the five roots: {newC.size} (theorems {nThm}, definitions {nDef}, axioms {nAx}, inductives {nInd}, other {nOther}); without a value (not inductive/ctor/rec): {noValue}"
  let clash := newC.toList.filter (fun (n, _) => base.contains n)
  logInfo m!"of them already present in the Mathlib-only environment: {clash.length}"
  let t0 ← IO.monoMsNow
  let env' ← base.replay newC
  let t1 ← IO.monoMsNow
  logInfo m!"KERNEL REPLAY FINISHED in {t1 - t0} ms"
  for r in roots do
    logInfo m!"after replay, {r} is in the replayed environment: {env'.contains r}"
