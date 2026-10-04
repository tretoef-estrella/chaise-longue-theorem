module

public import RequestProject.EvenOne.Phi

/-!
# Part B of `q_even_block_one.md`: the case `0 ∈ 𝒞_1`

Throughout `S.p = 2`, `0 ∈ 𝒞_1` and `|𝒞_1| = 2j + 2`, so `W = WS S c 1 = 𝒞_1 ∖ {0}` has
`2j + 1` elements.

* `EvenOne.gPS_conj`: `g_P` for `P = ē ∘ J ∘ ē⁻¹`, written over the pairs of `J`.
* `EvenOne.eIn`, `EvenOne.ebarIn`: the increasing bijections `Fin (2j+1) ≃o W` and
  `ē : Fin (2j+2) ≃o 𝒞_1` (`ē 0 = 0`), as in `EvenMinus.lemmaM5`.
* (B1) `EvenOne.PhiE_psiG` (the generators match EXACTLY), `EvenOne.IcS_eq_map_IK`,
  `EvenOne.B1`.
* (B2) `EvenOne.B2`; (B3) `EvenOne.B3`.
-/

@[expose] public section

open MvPolynomial

namespace EvenOne

open ColSplit ColSurv ColComp ColTensor ColDecomp EvenBlocks ColUpper

open scoped Classical

variable {F : Type*} [Field F] (S : ColSetting F) {k : ℕ}

/-- **Part B, (B1)** and **Part C, (C4)** of `q_even_block_one.md` (proof; model
`EvenMinus.Psi_fpolyM`): for an increasing bijection `ē : ι ≃o 𝒞_1` and a perfect matching `J` of
`ι`, the block generator of `P = ē ∘ J ∘ ē⁻¹` is the product of the pair factors
`f_{ē a, ē (J a)}` over the pairs `{a < J a}` of `J`. -/
theorem gPS_conj {ι : Type*} [Fintype ι] [LinearOrder ι] (c : Fin (2 * k + 1) → S.μ)
    (ē : ι ≃o cls (cExt c) 1) (J : PerfMatch ι) :
    gPS S c 1 (EvenMinus.conjPMT ē.toEquiv J) =
      ∏ a ∈ Finset.univ.filter (fun a => a < J.1 a),
        pairF S.q (tB S c (WS S c 1)) (ē a).1 (ē (J.1 a)).1 := by
  rw [gPS]
  symm
  refine Finset.prod_equiv ē.toEquiv ?_ ?_
  · intro a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    change _ ↔ (ē a).1 < (ē (J.1 (ē.symm (ē a)))).1
    rw [Subtype.coe_lt_coe, ē.symm_apply_apply, ē.lt_iff_lt]
  · intro a _
    simp [EvenMinus.conjPMT]

/-- **Part B** of `q_even_block_one.md` (setting): the increasing bijection
`e : Fin (2j+1) ≃o W`, `W = WS S c 1`, when `0 ∈ 𝒞_1` and `|𝒞_1| = 2j + 2`. -/
noncomputable def eIn (c : Fin (2 * k + 1) → S.μ) {j : ℕ}
    (h0 : (0 : Fin (2 * k + 2)) ∈ cls (cExt c) 1) (hs : (cls (cExt c) 1).card = 2 * j + 2) :
    Fin (2 * j + 1) ≃o WS S c 1 :=
  (WS S c 1).orderIsoOfFin (by have := EvenMinus.card_WS_of_mem S c 1 h0; omega)

/-- **Part B** of `q_even_block_one.md` (setting): the increasing relabelling
`ē : Fin (2j+2) ≃o 𝒞_1`, `ē 0 = 0`, `ē (i+1) = e i + 1` (as in `EvenMinus.lemmaM5`). -/
noncomputable def ebarIn (c : Fin (2 * k + 1) → S.μ) {j : ℕ}
    (h0 : (0 : Fin (2 * k + 2)) ∈ cls (cExt c) 1) (hs : (cls (cExt c) 1).card = 2 * j + 2) :
    Fin (2 * j + 2) ≃o cls (cExt c) 1 :=
  StrictMono.orderIsoOfSurjective (EvenMinus.ebarS S c 1 h0 (eIn S c h0 hs))
    (EvenMinus.ebarS_strictMono S c 1 h0 (eIn S c h0 hs))
    (EvenMinus.ebarS_surjective S c 1 h0 (eIn S c h0 hs))

/-- **Part B** of `q_even_block_one.md` (setting): `ē a = 0` iff `a = 0`. -/
theorem ebarIn_eq_zero_iff (c : Fin (2 * k + 1) → S.μ) {j : ℕ}
    (h0 : (0 : Fin (2 * k + 2)) ∈ cls (cExt c) 1) (hs : (cls (cExt c) 1).card = 2 * j + 2)
    (a : Fin (2 * j + 2)) : (ebarIn S c h0 hs a).1 = 0 ↔ a = 0 := by
  change (EvenMinus.ebarS S c 1 h0 (eIn S c h0 hs) a).1 = 0 ↔ a = 0
  induction a using Fin.cases with
  | zero => simp [EvenMinus.ebarS]
  | succ i => simp [EvenMinus.ebarS, EvenMinus.succWS, Fin.succ_ne_zero]

/-- **Part B, (B1)** of `q_even_block_one.md` (proof): `Φ_e (t_a) = t_{ē a}` for every vertex `a`
(for `a = 0` both sides are the dummy value `0`). -/
theorem PhiE_tU (hp : S.p = 2) (c : Fin (2 * k + 1) → S.μ) {j : ℕ}
    (h0 : (0 : Fin (2 * k + 2)) ∈ cls (cExt c) 1) (hs : (cls (cExt c) 1).card = 2 * j + 2)
    (a : Fin (2 * j + 2)) :
    PhiE S hp c (eIn S c h0 hs).toEquiv (tU F S.q j a) =
      tB S c (WS S c 1) (ebarIn S c h0 hs a).1 := by
  change _ = tB S c (WS S c 1) (EvenMinus.ebarS S c 1 h0 (eIn S c h0 hs) a).1
  induction a using Fin.cases with
  | zero => simp [tU, tB, EvenMinus.ebarS]
  | succ i =>
    simp only [tU, Fin.cases_succ, PhiE_X, EvenMinus.ebarS, EvenMinus.succWS]
    rw [ColOne.tB_succ S c _ (eIn S c h0 hs i).2]
    rfl

/-- **Part B, (B1)** of `q_even_block_one.md` (proof): `ψ_J` is the product over the pairs
`{a < J a}` of `t_{J a} − 1` (if `a = 0`) and `(t_{J a} − 1)·phi q (t_a t_{J a})` (if `a > 0`). -/
theorem psiG_eq_prod (q : ℕ) {j : ℕ} (J : BallotBound.Matching j) :
    psiG F q J = ∏ a ∈ Finset.univ.filter (fun a => a < J.1 a),
      (if a = 0 then tU F q j (J.1 a) - 1 else
        (tU F q j (J.1 a) - 1) * phi q (tU F q j a * tU F q j (J.1 a))) := by
  rw [psiG, Finset.prod_filter, Finset.prod_filter, Finset.prod_filter, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun a _ => ?_
  by_cases h : a < J.1 a
  · by_cases ha : a = 0
    · subst ha; simp [h]
    · have hpos : 0 < a := Fin.pos_iff_ne_zero.2 ha
      simp [h, ha, hpos]
  · simp [h]

/-- **Part B, (B1)** of `q_even_block_one.md`: if `S.p = 2`, `0 ∈ 𝒞_1` and `|𝒞_1| = 2j + 2`, then
for every matching `J ∈ BallotBound.Matching j`, `Φ_e (psiG F S.q J) = gPS S c 1 P` EXACTLY (no
unit), where `e : Fin (2j+1) ≃o W` and `ē : Fin (2j+2) ≃o 𝒞_1` are the increasing bijections and
`P = ē ∘ J ∘ ē⁻¹`. -/
theorem PhiE_psiG (hp : S.p = 2) (c : Fin (2 * k + 1) → S.μ) {j : ℕ}
    (h0 : (0 : Fin (2 * k + 2)) ∈ cls (cExt c) 1) (hs : (cls (cExt c) 1).card = 2 * j + 2)
    (J : BallotBound.Matching j) :
    PhiE S hp c (eIn S c h0 hs).toEquiv (psiG F S.q J) =
      gPS S c 1 (EvenMinus.conjPMT (ebarIn S c h0 hs).toEquiv J) := by
  rw [gPS_conj, psiG_eq_prod, map_prod]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [pairF]
  by_cases ha : a = 0
  · rw [if_pos ha, if_pos ((ebarIn_eq_zero_iff S c h0 hs a).2 ha), map_sub, map_one,
      PhiE_tU]
  · rw [if_neg ha, if_neg (fun h => ha ((ebarIn_eq_zero_iff S c h0 hs a).1 h)), map_mul,
      map_sub, map_one, ColSurv.map_phi, map_mul, PhiE_tU, PhiE_tU, ← (A1_S S hp _).1]

/-- **Part B, (B1)** of `q_even_block_one.md` (proof): `I_{c,1} = Φ_e (I_K)`, `I_K = IK F S.q j`
(the generators agree exactly by `EvenOne.PhiE_psiG`, and every perfect matching of `𝒞_1` is
`ē ∘ J ∘ ē⁻¹`). -/
theorem IcS_eq_map_IK (hp : S.p = 2) (c : Fin (2 * k + 1) → S.μ) {j : ℕ}
    (h0 : (0 : Fin (2 * k + 2)) ∈ cls (cExt c) 1) (hs : (cls (cExt c) 1).card = 2 * j + 2) :
    IcS S c 1 = (IK F S.q j).map (PhiE S hp c (eIn S c h0 hs).toEquiv) := by
  rw [IK, Ideal.map_span, IcS, ← Set.range_comp]
  congr 1
  ext g
  constructor
  · rintro ⟨P, rfl⟩
    obtain ⟨J, rfl⟩ := EvenMinus.conjPMT_surjective (ebarIn S c h0 hs).toEquiv P
    exact ⟨J, PhiE_psiG S hp c h0 hs J⟩
  · rintro ⟨J, rfl⟩
    exact ⟨_, (PhiE_psiG S hp c h0 hs J).symm⟩

/-- **Part B, (B1)** of `q_even_block_one.md`: if `S.p = 2`, `0 ∈ 𝒞_1` and `|𝒞_1| = 2j + 2`, then
`finrank F (IcS S c 1) = finrank F ((ColUpper.IK F S.q j).restrictScalars F)`. -/
theorem B1 (hp : S.p = 2) (c : Fin (2 * k + 1) → S.μ) {j : ℕ}
    (h0 : (0 : Fin (2 * k + 2)) ∈ cls (cExt c) 1) (hs : (cls (cExt c) 1).card = 2 * j + 2) :
    Module.finrank F (IcS S c 1) = Module.finrank F ((IK F S.q j).restrictScalars F) := by
  rw [IcS_eq_map_IK S hp c h0 hs, ColPairs.finrank_map_algEquiv]

/-- **Part B, (B2)** of `q_even_block_one.md`: if `S.p = 2`, then
`EvenCount.QkEven j S.q ≤ finrank F ((ColUpper.IK F S.q j).restrictScalars F)` for every `j`
(`S.v ≥ 2`: `OddTheorem.theoremO` with `h = 2^{v−1} − 1 = (q − 2)/2 ≥ 1`, then `Pow2.prop92_ge`;
`S.v = 1`: `Pow2.q_two`). -/
theorem B2 (hp : S.p = 2) (j : ℕ) :
    EvenCount.QkEven j S.q ≤ Module.finrank F ((IK F S.q j).restrictScalars F) := by
  haveI := charP_two S hp
  rw [q_eq_two_pow S hp]
  by_cases hv : S.v = 1
  · rw [hv, pow_one, (Pow2.q_two F j).2.1, (Pow2.q_two F j).2.2]
  · have hv2 : 2 ≤ S.v := by have := S.one_le_v; omega
    have e1 : 2 ^ S.v = 2 * 2 ^ (S.v - 1) := by
      rw [← pow_succ']; congr 1; omega
    have e2 : 2 ≤ 2 ^ (S.v - 1) :=
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (S.v - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    refine (EvenMinus.theoremO_of_eq (F := F) (h := 2 ^ (S.v - 1) - 1) (by omega) j (by omega)).trans ?_
    exact Pow2.prop92_ge F S.one_le_v j

/-- **Part B, (B3)** of `q_even_block_one.md`: if `S.p = 2`, `0 ∈ 𝒞_1` and `|𝒞_1| = 2j + 2`, then
`EvenCount.QkEven j S.q ≤ finrank F (IcS S c 1)`. -/
theorem B3 (hp : S.p = 2) (c : Fin (2 * k + 1) → S.μ) {j : ℕ}
    (h0 : (0 : Fin (2 * k + 2)) ∈ cls (cExt c) 1) (hs : (cls (cExt c) 1).card = 2 * j + 2) :
    EvenCount.QkEven j S.q ≤ Module.finrank F (IcS S c 1) := by
  rw [B1 S hp c h0 hs]
  exact B2 S hp j

end EvenOne

end
