import RequestProject.EvenAll.PartBC
import RequestProject.OddEquality.PartD

-- L6_inductives_finite.lean — Grepy Sello (cold reader, mission LEAN_2), 4 Oct 2026.
-- Run from material/project:  lake env lean ../../checks/L6_inductives_finite.lean  (under vigia.sh)
-- 1. The finiteness example that failed twice by my own slips (L1, L2), corrected.
-- 2. The 19 constants that L5 skipped (inductive types, constructors, recursors of the project in
--    the cone of the five root theorems): each inductive block is re-submitted to the kernel under
--    fresh names, and the recursor the kernel generates is compared with the compiled one (type,
--    rules, counters), after renaming.

set_option synthInstance.maxHeartbeats 200000

open ColSplit ColUpper ColAssembly in
theorem gs6_Qall61 : EvenAll.Qall 6 1 = 61 := by
  unfold EvenAll.Qall; rw [if_pos (by decide)]; exact EvenCount.QkEven_values.2.2

open ColSplit ColUpper ColAssembly in
example : Module.Finite ℤ (RZ 3 6 ⧸ IZ 6 1) ∧ Module.finrank ℤ (RZ 3 6 ⧸ IZ 6 1) = 155 := by
  have h := (EvenAll.mainTheorem'.{0} (m := 6) (by norm_num) 1).1
  haveI := h.1
  have h155 : Module.finrank ℤ (RZ 3 6 ⧸ IZ 6 1) = 155 := by
    rw [h.2, gs6_Qall61] <;> norm_num
  exact ⟨Module.finite_of_finrank_pos (by rw [h155]; norm_num), h155⟩

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

def gsFresh (n : Name) : Name := Name.str n "_gsSelloRecheck"

def gsRename (ρ : Name → Option Name) (e : Expr) : Expr :=
  e.replace fun x => match x with
    | Expr.const n us => (ρ n).map fun n' => Expr.const n' us
    | _ => none

def gsKind (ci : ConstantInfo) : String :=
  match ci with
  | ConstantInfo.inductInfo _ => "inductive"
  | ConstantInfo.ctorInfo _ => "constructor"
  | ConstantInfo.recInfo _ => "recursor"
  | ConstantInfo.quotInfo _ => "quot"
  | ConstantInfo.axiomInfo _ => "axiom"
  | ConstantInfo.thmInfo _ => "theorem"
  | ConstantInfo.defnInfo _ => "definition"
  | ConstantInfo.opaqueInfo _ => "opaque"

#eval show CommandElabM Unit from do
  let env ← getEnv
  let kenv := env.toKernelEnv
  let roots : List Name := [`EvenAll.mainTheorem', `OddEquality.D1, `OddEquality.D2_DJ,
    `OddEquality.D2_M, `OddTheorem.theoremO]
  let mut acc : NameSet := {}
  for r in roots do
    acc := gsCollect env r acc
  let mut skipped : Array (Name × String) := #[]
  let mut inds : Array InductiveVal := #[]
  for n in acc.toList do
    if let some idx := env.getModuleIdxFor? n then
      let m := env.header.moduleNames[idx.toNat]!
      if (`RequestProject).isPrefixOf m then
        if let some ci := env.find? n then
          let k := gsKind ci
          if k != "theorem" && k != "definition" && k != "opaque" then
            skipped := skipped.push (n, k)
          if let ConstantInfo.inductInfo v := ci then
            inds := inds.push v
  logInfo m!"project constants of the cone that L5 skipped: {skipped.size}: {skipped.toList}"
  for v in inds do
    -- names of the block: the types, their constructors, their recursors
    let mut ctorsOf : List (Name × List Name) := []
    for t in v.all do
      match env.find? t with
      | some (ConstantInfo.inductInfo w) => ctorsOf := ctorsOf ++ [(t, w.ctors)]
      | _ => pure ()
    let blockNames : List Name := ctorsOf.foldl (fun l p => l ++ (p.1 :: p.2)) []
    let recNames : List Name := v.all.map (fun t => Name.str t "rec")
    let ρ : Name → Option Name := fun n =>
      if blockNames.contains n then some (gsFresh n)
      else if recNames.contains n then some (Name.str (gsFresh n.getPrefix) "rec")
      else none
    let mut types : List InductiveType := []
    let mut ok := true
    for (t, cs) in ctorsOf do
      let some tci := env.find? t | do ok := false; continue
      let mut ctors : List Constructor := []
      for c in cs do
        match env.find? c with
        | some cci => ctors := ctors ++ [{ name := gsFresh c, type := gsRename ρ cci.type }]
        | none => ok := false
      types := types ++ [{ name := gsFresh t, type := gsRename ρ tci.type, ctors := ctors }]
    if !ok then
      logInfo m!"{v.name}: block incomplete, not re-checked"
      continue
    let decl := Declaration.inductDecl v.levelParams v.numParams types v.isUnsafe
    match kenv.addDecl {} decl with
    | Except.error _ => logInfo m!"{v.name}: REJECTED by the kernel when re-submitted"
    | Except.ok kenv' =>
      for t in v.all do
        let r := Name.str t "rec"
        let r' := Name.str (gsFresh t) "rec"
        match env.find? r, kenv'.find? r' with
        | some (ConstantInfo.recInfo a), some (ConstantInfo.recInfo b) =>
          let sameType := b.type == gsRename ρ a.type
          let sameRules := (b.rules.map (·.rhs)) == (a.rules.map (fun x => gsRename ρ x.rhs))
          let sameNums := a.numParams == b.numParams && a.numIndices == b.numIndices &&
            a.numMotives == b.numMotives && a.numMinors == b.numMinors && a.k == b.k
          logInfo m!"{t}: re-submitted and accepted; generated recursor equals the compiled one: type {sameType}, rules {sameRules}, counters {sameNums}"
        | _, _ => logInfo m!"{t}: recursor not found for comparison"
