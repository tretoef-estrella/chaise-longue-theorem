module

public import RequestProject.OddEquality.PartB
public import RequestProject.EvenMinus.Main
public import RequestProject.Lifts.Algebra

/-!
# Part A of `q_oddbox_equality.md`: the ideal `ℳ` and the map `θ`

This file formalizes **Part A** of `q_oddbox_equality.md` (Lemma 8.12, one direction): the
identification of `ℳ` with `OddPatterns.VSAll F h N {(∅, false)}` (A1), the lower bound
`Q^e_k(q) ≤ dim ℳ` (A2), the map `θ` (A3), `θ(D_{P_J}) = D_J` (A4) and
`dim (D_J) ≤ dim ℳ` (A5). Throughout `q = 2h + 2` (box `r = 2h + 1`) and `N = 2k + 2`.
-/

@[expose] public section

open Polynomial

namespace OddEquality

open Peel hiding C

set_option synthInstance.maxHeartbeats 200000

variable {F : Type*} [Field F]

/-! ### (A1), (A2) -/

/-- **(A1)** of `q_oddbox_equality.md`: `ℳ = Σ_P D_P·C_n` equals
`OddPatterns.VSAll F h n {(OddShapes.emptyPart, false)}` (the patterns of the empty unmarked shape
are the perfect matchings, `OddPatterns.B5_no_marked`; via `EvenMinus.VSAll_root_even_eq` and
`ColOne.VLamAll_empty_eq`). Stated for every number `n` of variables. -/
theorem A1 (h n : ℕ) :
    Mideal F (2 * h + 2) n = OddPatterns.VSAll F h n {(OddShapes.emptyPart, false)} := by
  rw [EvenMinus.VSAll_root_even_eq, ColOne.VLamAll_empty_eq]
  rfl

/-- **(A2)** of `q_oddbox_equality.md`: for every field `F`, `h ≥ 1` and `k`,
`Q^e_k(2h + 2) ≤ dim_F ℳ` (Theorem 8.11 with `OddShapes.isInterlaced_root_even` and
`OddLayers.card_ZS_root_even`, as in `EvenMinus.lemmaM6`). -/
theorem A2 {h : ℕ} (hh : 1 ≤ h) (k : ℕ) :
    EvenCount.QkEven k (2 * h + 2) ≤
      Module.finrank F ((Mideal F (2 * h + 2) (2 * k + 2)).restrictScalars F) := by
  rw [A1, ← OddLayers.card_ZS_root_even (OddTheorem.stdOddSetting h hh) k]
  exact OddTheorem.theorem811 F (OddTheorem.stdOddSetting h hh) (2 * k + 2) _
    (OddShapes.isInterlaced_root_even h (2 * k + 2) ⟨k + 1, by ring⟩)

/-! ### (A3) The map `θ` -/

/-- **(A3)** of `q_oddbox_equality.md`: `θ : Peel.C F q (2k+2) → Peel.C F q (2k+1)`, the coefficient
of `y_0^{r−1} = y_0^{2h}` (`Peel.coeffY1` with `j = 2h`), the variables `y_{i.succ}` of the source
being the variables `y_i` of the target. -/
noncomputable def theta (h k : ℕ) :
    Peel.C F (2 * h + 2) (2 * k + 2) →ₗ[F] Peel.C F (2 * h + 2) (2 * k + 1) :=
  coeffY1 (m := 2 * k + 2) (by omega) (2 * h)

/-- **(A3)** of `q_oddbox_equality.md`: the inclusion `ι : Peel.C F q (2k+1) → Peel.C F q (2k+2)`,
`y_i ↦ y_{i.succ}` (`Peel.incl`). -/
noncomputable abbrev iota (h k : ℕ) : Peel.C F (2 * h + 2) (2 * k + 1) →+* Peel.C F (2 * h + 2) (2 * k + 2) :=
  incl F (2 * h + 2) (2 * k + 1)

/-- **(A3)** of `q_oddbox_equality.md`: `ι(y_i) = y_{i.succ}`. -/
theorem iota_y (h k : ℕ) (i : Fin (2 * k + 1)) :
    iota (F := F) h k (Tight.y F (2 * h + 2) i) = Tight.y F (2 * h + 2) i.succ :=
  Lifts.incl_y i

/-- **(A3)** of `q_oddbox_equality.md`: `θ` is `Peel.C F q (2k+1)`-linear through `ι`:
`θ(ι(g)·f) = g·θ(f)`. -/
theorem A3 (h k : ℕ) (g : Peel.C F (2 * h + 2) (2 * k + 1)) (f : Peel.C F (2 * h + 2) (2 * k + 2)) :
    theta h k (iota h k g * f) = g * theta h k f := by
  change (expandGen F (2 * h + 2) _ (peelEquiv' F (2 * h + 2) (2 * k + 1) (iota h k g * f))).coeff
      (2 * h) = g * (expandGen F (2 * h + 2) _ (peelEquiv' F (2 * h + 2) (2 * k + 1) f)).coeff (2 * h)
  rw [map_mul, Lifts.phi_incl, expandGen_of_mul, coeff_C_mul]

/-- **(A4)** of `q_oddbox_equality.md` (the factor containing `y_0`): the coefficient of
`y_0^{r−1}` in `D(y_0, y_b)` is `(−1)^{r−1} = 1` (`r` odd). -/
theorem theta_D0 (h k : ℕ) (b : Fin (2 * k + 1)) :
    theta (F := F) h k (Tight.D F (2 * h + 2) 0 b.succ) = 1 := by
  haveI := Degeneration.nontrivial_C (F := F) (q := 2 * h + 2) (by omega) (2 * k + 1)
  have hdeg : (Lifts.dpoly (2 * h + 2) (Tight.y F (2 * h + 2) b)).degree <
      (X ^ (2 * h + 2 - 1) : (Peel.C F (2 * h + 2) (2 * k + 1))[X]).degree := by
    rw [degree_X_pow, degree_lt_iff_coeff_zero]
    intro m hm
    rw [Lifts.coeff_dpoly, if_neg]
    exact not_lt.2 (by exact_mod_cast hm)
  change (expandGen F (2 * h + 2) _ (peelEquiv' F (2 * h + 2) (2 * k + 1)
      (Tight.D F (2 * h + 2) 0 b.succ))).coeff (2 * h) = 1
  rw [Lifts.phi_D]
  change (AdjoinRoot.modByMonicHom (monic_X_pow_q (2 * h + 2) _) _).coeff (2 * h) = 1
  rw [AdjoinRoot.modByMonicHom_mk, (modByMonic_eq_self_iff (monic_X_pow_q _ _)).2 hdeg,
    Lifts.coeff_dpoly, if_pos (by omega), show 2 * h + 2 - 2 - 2 * h = 0 by omega, pow_zero,
    mul_one, (Even.neg_one_pow ⟨h, by ring⟩)]

/-! ### (A4) -/

/-- **(A4)** of `q_oddbox_equality.md`: a matching `J ∈ BallotBound.Matching k` read as a perfect
matching `P_J` of `Fin N`. -/
def PJ {k : ℕ} (J : BallotBound.Matching k) : ColComp.PerfMatch (Fin (2 * k + 2)) := ⟨J.1, J.2⟩

/-- **(A4)** of `q_oddbox_equality.md` (proof): `ι(D(y_a, y_b)) = D(y_{a+1}, y_{b+1})`. -/
theorem iota_D (h k : ℕ) (a b : Fin (2 * k + 1)) :
    iota (F := F) h k (Tight.D F (2 * h + 2) a b) = Tight.D F (2 * h + 2) a.succ b.succ := by
  simp only [Tight.D, map_sum, map_mul, map_pow, map_neg, map_one, iota_y]

/-- **(A4)** of `q_oddbox_equality.md` (proof): `D_{P_J} = D(y_0, y_{J(0)})·ι(D_J)`. -/
theorem DPn_PJ (h : ℕ) {k : ℕ} (J : BallotBound.Matching k) :
    ColOne.DPn F (2 * h + 2) (PJ J) =
      Tight.D F (2 * h + 2) 0 (J.1 0) * iota h k (TheoremB.DJ F (2 * h + 2) J) := by
  classical
  have h0 : (0 : Fin (2 * k + 2)) < J.1 0 := by
    rcases Fin.pos_iff_ne_zero.2 (J.2 0).1 with h
    exact h
  rw [ColOne.DPn, ← Finset.prod_filter_mul_prod_filter_not _ (fun a => a = 0)]
  congr 1
  · have : (Finset.univ.filter (fun a => a < (PJ J).1 a)).filter (fun a => a = 0) = {0} := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · exact fun h => h.2
      · rintro rfl; exact ⟨h0, rfl⟩
    rw [this, Finset.prod_singleton]
    rfl
  · rw [TheoremB.DJ, map_prod, Finset.filter_filter]
    refine Finset.prod_congr ?_ fun a ha => ?_
    · ext a
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨h2, ?_, h1⟩
        intro h3
        change a < J.1 a at h1
        rw [h3] at h1
        exact absurd h1 (Fin.not_lt_zero _)
      · rintro ⟨h1, -, h3⟩
        exact ⟨h3, h1⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
      rw [iota_D]
      have e1 : (TheoremB.idx a).succ = a := by
        ext; simp [TheoremB.idx]; have := Fin.pos_iff_ne_zero.2 ha.1; omega
      have e2 : (TheoremB.idx (J.1 a)).succ = J.1 a := by
        ext; simp [TheoremB.idx]; have := Fin.pos_iff_ne_zero.2 ha.2.1; omega
      rw [e1, e2]
      rfl

/-- **(A4)** of `q_oddbox_equality.md`: for every matching `J ∈ BallotBound.Matching k`,
`θ(D_{P_J}) = D_J = TheoremB.DJ F (2h+2) J`. -/
theorem A4 (h : ℕ) {k : ℕ} (J : BallotBound.Matching k) :
    theta h k (ColOne.DPn F (2 * h + 2) (PJ J)) = TheoremB.DJ F (2 * h + 2) J := by
  have hJ0 : (TheoremB.idx (J.1 0)).succ = J.1 0 := by
    ext; simp [TheoremB.idx]; have := Fin.pos_iff_ne_zero.2 (J.2 0).1; omega
  rw [DPn_PJ, mul_comm (Tight.D F (2 * h + 2) 0 (J.1 0)), A3, ← hJ0, theta_D0, mul_one]

/-! ### (A5) -/

/-- **(A5)** of `q_oddbox_equality.md` (proof): `(D_J : J) ⊆ θ(ℳ)` (`θ(ℳ)` is a
`Peel.C F q (2k+1)`-submodule by (A3) and contains every `D_J` by (A4)). -/
theorem DIdeal_le_map_theta (h k : ℕ) :
    (TheoremB.DIdeal F (2 * h + 2) k).restrictScalars F ≤
      ((Mideal F (2 * h + 2) (2 * k + 2)).restrictScalars F).map (theta h k) := by
  intro x hx
  rw [Submodule.restrictScalars_mem] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨J, rfl⟩ := hx
    exact ⟨_, Ideal.subset_span ⟨PJ J, rfl⟩, A4 h J⟩
  | zero => exact zero_mem _
  | add x z _ _ hx hz => exact add_mem hx hz
  | smul c x _ hx =>
    obtain ⟨m, hm, rfl⟩ := hx
    exact ⟨iota h k c * m, Ideal.mul_mem_left _ _ hm, A3 h k c m⟩

/-- **(A5)** of `q_oddbox_equality.md`: for every field `F`, every `h` and `k`,
`dim_F (D_J : J) ≤ dim_F ℳ` (the injectivity of `θ` is not needed). -/
theorem A5 (h k : ℕ) :
    Module.finrank F ((TheoremB.DIdeal F (2 * h + 2) k).restrictScalars F) ≤
      Module.finrank F ((Mideal F (2 * h + 2) (2 * k + 2)).restrictScalars F) := by
  haveI := finiteDimensional_C (F := F) (q := 2 * h + 2) (n := 2 * k + 1)
  exact (Submodule.finrank_mono (DIdeal_le_map_theta h k)).trans (Submodule.finrank_map_le _ _)

end OddEquality

end
