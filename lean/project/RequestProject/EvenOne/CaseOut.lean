module

public import RequestProject.EvenOne.CaseIn

/-!
# Part C, (C4)–(C5) of `q_even_block_one.md`: the case `0 ∉ 𝒞_1`

Throughout `S.p = 2`, `0 ∉ 𝒞_1` and `|𝒞_1| = 2j + 2`, so `W = WS S c 1` has `2j + 2` elements.

* `EvenOne.eOut`, `EvenOne.ebarOut`: the increasing bijections `e : Fin (2j+2) ≃o W` and
  `ē : Fin (2j+2) ≃o 𝒞_1` (`ē a = e a + 1`; `ē 0 = i_1 = min 𝒞_1`).
* (C4) `EvenOne.C4`: `θ (Φ_e⁻¹ (g_P)) = ψ_J` for `P = ē ∘ J ∘ ē⁻¹`.
* (C5) `EvenOne.C5`: `finrank (IK F S.q j) ≤ finrank (IcS S c 1)` and
  `QkEven j S.q ≤ finrank (IcS S c 1)`. (Injectivity of `θ` on `ℳ` is not proved; it is not needed.)
-/

@[expose] public section

open MvPolynomial

namespace EvenOne

open ColSplit ColSurv ColComp ColTensor ColDecomp EvenBlocks ColUpper

open scoped Classical

variable {F : Type*} [Field F] (S : ColSetting F) {k : ℕ}

/-- **Part C, (C4)** of `q_even_block_one.md` (setting): the increasing bijection
`e : Fin (2j+2) ≃o W`, `W = WS S c 1`, when `0 ∉ 𝒞_1` and `|𝒞_1| = 2j + 2`. -/
noncomputable def eOut (c : Fin (2 * k + 1) → S.μ) {j : ℕ}
    (h0 : (0 : Fin (2 * k + 2)) ∉ cls (cExt c) 1) (hs : (cls (cExt c) 1).card = 2 * j + 2) :
    Fin (2 * j + 2) ≃o WS S c 1 :=
  (WS S c 1).orderIsoOfFin (by rw [EvenMinus.card_WS_of_notMem S c 1 h0, hs])

/-- **Part C, (C4)** of `q_even_block_one.md` (setting): the increasing relabelling
`ē : Fin (2j+2) ≃o 𝒞_1`, `ē a = e a + 1` (so `ē 0 = i_1 = min 𝒞_1`). -/
noncomputable def ebarOut (c : Fin (2 * k + 1) → S.μ) {j : ℕ}
    (h0 : (0 : Fin (2 * k + 2)) ∉ cls (cExt c) 1) (hs : (cls (cExt c) 1).card = 2 * j + 2) :
    Fin (2 * j + 2) ≃o cls (cExt c) 1 :=
  (eOut S c h0 hs).trans (StrictMono.orderIsoOfSurjective (EvenMinus.succWS S c 1)
    (EvenMinus.succWS_strictMono S c 1) (EvenMinus.succWS_surjective S c 1 h0))

/-- **Part C, (C4)** of `q_even_block_one.md` (proof): `Φ_e⁻¹ (t_{ē a}) = X a`. -/
theorem PhiE_symm_tB (hp : S.p = 2) (c : Fin (2 * k + 1) → S.μ) {j : ℕ}
    (h0 : (0 : Fin (2 * k + 2)) ∉ cls (cExt c) 1) (hs : (cls (cExt c) 1).card = 2 * j + 2)
    (a : Fin (2 * j + 2)) :
    (PhiE S hp c (eOut S c h0 hs).toEquiv).symm (tB S c (WS S c 1) (ebarOut S c h0 hs a).1) =
      Ideal.Quotient.mk _ (X a) := by
  change (PhiE S hp c (eOut S c h0 hs).toEquiv).symm
    (tB S c (WS S c 1) (eOut S c h0 hs a).1.succ) = _
  rw [ColOne.tB_succ S c _ (eOut S c h0 hs a).2]
  simp

/-- **Part C, (C4)** of `q_even_block_one.md` (proof): `ē a ≠ 0` for every `a`. -/
theorem ebarOut_ne_zero (c : Fin (2 * k + 1) → S.μ) {j : ℕ}
    (h0 : (0 : Fin (2 * k + 2)) ∉ cls (cExt c) 1) (hs : (cls (cExt c) 1).card = 2 * j + 2)
    (a : Fin (2 * j + 2)) : (ebarOut S c h0 hs a).1 ≠ 0 :=
  Fin.succ_ne_zero _

/-- **Part C, (C4)** of `q_even_block_one.md` (proof): `Φ_e⁻¹ (g_P)` for `P = ē ∘ J ∘ ē⁻¹` is
`Π_{a < J a} (X_{J a} − 1)·phi q (X_a X_{J a})` (by (A1); no pair contains `0`). -/
theorem PhiE_symm_gPS (hp : S.p = 2) (c : Fin (2 * k + 1) → S.μ) {j : ℕ}
    (h0 : (0 : Fin (2 * k + 2)) ∉ cls (cExt c) 1) (hs : (cls (cExt c) 1).card = 2 * j + 2)
    (J : BallotBound.Matching j) :
    (PhiE S hp c (eOut S c h0 hs).toEquiv).symm
        (gPS S c 1 (EvenMinus.conjPMT (ebarOut S c h0 hs).toEquiv J)) =
      ∏ a ∈ Finset.univ.filter (fun a => a < J.1 a),
        ((Ideal.Quotient.mk (gaIdeal F (2 * j + 2) S.q) (X (J.1 a)) - 1) *
          phi S.q (Ideal.Quotient.mk _ (X a) * Ideal.Quotient.mk _ (X (J.1 a)))) := by
  rw [gPS_conj, map_prod]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [pairF, if_neg (ebarOut_ne_zero S c h0 hs a), map_mul, map_pow, map_sub, map_one, map_sub,
    map_one, map_mul, PhiE_symm_tB, PhiE_symm_tB, (A1_S S hp _).1]

/-- **Part C, (C4)** of `q_even_block_one.md` (proof): for `a ≠ 0`, `ι (t_a) = X a` in
`GA F (2j+2) q` (`t_a = tU`, the variable `X (a − 1)` of `GA F (2j+1) q`). -/
theorem iotaGA_tU (q : ℕ) {j : ℕ} {a : Fin (2 * j + 2)} (ha : a ≠ 0) :
    iotaGA q (2 * j + 1) (tU F q j a) = Ideal.Quotient.mk _ (X a) := by
  obtain ⟨i, rfl⟩ := Fin.exists_succ_eq.2 ha
  simp [tU]

/-- **Part C, (C4)** of `q_even_block_one.md` (proof, pure form): in `GA F (2j+2) q`, `q ≥ 1`,
`θ (Π_{a < J a} (X_{J a} − 1)·phi q (X_a X_{J a})) = ψ_J` for every matching
`J ∈ BallotBound.Matching j`: the pair `{0, J 0}` gives `t_{J 0} − 1` by (C3), the other pairs
pass through `θ` by (C2). -/
theorem theta_prod_eq_psiG (q : ℕ) (hq : 1 ≤ q) {j : ℕ} (J : BallotBound.Matching j) :
    theta q (2 * j + 1) (∏ a ∈ Finset.univ.filter (fun a => a < J.1 a),
        ((Ideal.Quotient.mk (gaIdeal F (2 * j + 2) q) (X (J.1 a)) - 1) *
          phi q (Ideal.Quotient.mk _ (X a) * Ideal.Quotient.mk _ (X (J.1 a))))) =
      psiG F q J := by
  set s := Finset.univ.filter (fun a : Fin (2 * j + 2) => a < J.1 a)
  have h0s : (0 : Fin (2 * j + 2)) ∈ s := by
    simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Fin.pos_iff_ne_zero.2 (J.2 0).1
  have hJ0 : J.1 0 ≠ 0 := (J.2 0).1
  have hrest : ∀ a ∈ s.erase 0, a ≠ 0 ∧ J.1 a ≠ 0 := by
    intro a ha
    rw [Finset.mem_erase] at ha
    refine ⟨ha.1, ?_⟩
    have : a < J.1 a := by simpa [s] using ha.2
    exact ne_of_gt (lt_of_le_of_lt (Fin.zero_le _) this)
  set H : Fin (2 * j + 2) → GA F (2 * j + 1) q :=
    fun a => (tU F q j (J.1 a) - 1) * phi q (tU F q j a * tU F q j (J.1 a))
  have hprod : ∏ a ∈ s.erase 0,
      ((Ideal.Quotient.mk (gaIdeal F (2 * j + 2) q) (X (J.1 a)) - 1) *
        phi q (Ideal.Quotient.mk _ (X a) * Ideal.Quotient.mk _ (X (J.1 a)))) =
      iotaGA q (2 * j + 1) (∏ a ∈ s.erase 0, H a) := by
    rw [map_prod]
    refine Finset.prod_congr rfl fun a ha => ?_
    obtain ⟨h1, h2⟩ := hrest a ha
    simp only [H, map_mul, map_sub, map_one, ColSurv.map_phi, iotaGA_tU q h1, iotaGA_tU q h2]
  rw [← Finset.mul_prod_erase s _ h0s, hprod, ← iotaGA_tU (F := F) q hJ0, theta_pair q _ hq,
    psiG_eq_prod, ← Finset.mul_prod_erase s _ h0s, if_pos rfl]
  congr 1
  refine Finset.prod_congr rfl fun a ha => ?_
  rw [if_neg (hrest a ha).1]

/-- **Part C, (C4)** of `q_even_block_one.md`: if `S.p = 2`, `0 ∉ 𝒞_1` and `|𝒞_1| = 2j + 2`, then
with `ē : Fin (2j+2) ≃o 𝒞_1` and `e : Fin (2j+2) ≃ W` increasing, for every matching
`J ∈ BallotBound.Matching j` and `P := ē ∘ J ∘ ē⁻¹` (every perfect matching of `𝒞_1` is of this
form, `EvenMinus.conjPMT_surjective`): `θ (Φ_e⁻¹ (gPS S c 1 P)) = psiG F S.q J`. (Stated from `J`
rather than from `P`; `J = ē⁻¹ ∘ P ∘ ē` is equivalent.) -/
theorem C4 (hp : S.p = 2) (c : Fin (2 * k + 1) → S.μ) {j : ℕ}
    (h0 : (0 : Fin (2 * k + 2)) ∉ cls (cExt c) 1) (hs : (cls (cExt c) 1).card = 2 * j + 2)
    (J : BallotBound.Matching j) :
    theta S.q (2 * j + 1) ((PhiE S hp c (eOut S c h0 hs).toEquiv).symm
        (gPS S c 1 (EvenMinus.conjPMT (ebarOut S c h0 hs).toEquiv J))) = psiG F S.q J := by
  rw [PhiE_symm_gPS]
  exact theta_prod_eq_psiG S.q (Setting.one_le_q S) J

/-- **Part C, (C5)** of `q_even_block_one.md`: if `S.p = 2`, `0 ∉ 𝒞_1` and `|𝒞_1| = 2j + 2`, then
`finrank F ((ColUpper.IK F S.q j).restrictScalars F) ≤ finrank F (IcS S c 1)` and
`EvenCount.QkEven j S.q ≤ finrank F (IcS S c 1)`. (With `ℳ := Φ_e⁻¹(IcS S c 1)`, `θ(ℳ)` is a
`GA F (2j+1) q`-submodule by (C2) containing every `ψ_J` by (C4), so `θ(ℳ) ⊇ IK F S.q j`; the
injectivity of `θ` on `ℳ` is not needed and not proved.) -/
theorem C5 (hp : S.p = 2) (c : Fin (2 * k + 1) → S.μ) {j : ℕ}
    (h0 : (0 : Fin (2 * k + 2)) ∉ cls (cExt c) 1) (hs : (cls (cExt c) 1).card = 2 * j + 2) :
    Module.finrank F ((IK F S.q j).restrictScalars F) ≤ Module.finrank F (IcS S c 1) ∧
      EvenCount.QkEven j S.q ≤ Module.finrank F (IcS S c 1) := by
  have hq : 0 < S.q := Setting.one_le_q S
  haveI := finite_GA (F := F) (2 * j + 1) S.q hq
  haveI := finite_GA (F := F) (2 * j + 2) S.q hq
  set Φ := PhiE S hp c (eOut S c h0 hs).toEquiv
  set M : Ideal (GA F (2 * j + 2) S.q) := (IcS S c 1).map Φ.symm
  set N : Submodule F (GA F (2 * j + 1) S.q) := (M.restrictScalars F).map (theta S.q (2 * j + 1))
  have hle : (IK F S.q j).restrictScalars F ≤ N := by
    intro x hx
    rw [Submodule.restrictScalars_mem] at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨J, rfl⟩ := hx
      refine ⟨_, ?_, C4 S hp c h0 hs J⟩
      exact Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨_, rfl⟩)
    | zero => exact N.zero_mem
    | add x y _ _ hx hy => exact N.add_mem hx hy
    | smul a x _ hx =>
      obtain ⟨m, hm, rfl⟩ := hx
      refine ⟨iotaGA S.q (2 * j + 1) a * m, ?_, theta_iota_mul _ _ a m⟩
      exact M.mul_mem_left _ hm
  have h1 : Module.finrank F ((IK F S.q j).restrictScalars F) ≤ Module.finrank F (IcS S c 1) := by
    calc Module.finrank F ((IK F S.q j).restrictScalars F) ≤ Module.finrank F N :=
          Submodule.finrank_mono hle
      _ ≤ Module.finrank F (M.restrictScalars F) := Submodule.finrank_map_le _ _
      _ = Module.finrank F (IcS S c 1) := by
          exact ColPairs.finrank_map_algEquiv Φ.symm (IcS S c 1)
  exact ⟨h1, (B2 S hp j).trans h1⟩

end EvenOne

end
