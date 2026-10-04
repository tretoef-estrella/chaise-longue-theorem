module

public import RequestProject.EvenMinus.MinusCoord
public import RequestProject.EvenColours.Main

/-!
# Part M, (M1), (M2), (M4) of `q_even_block_minus.md`: the block of colour `−1`

Throughout, `(−1 : F) ≠ 1` (hence `p ≠ 2`, `EvenColours.p_ne_two_of_neg_one_ne_one`), and
`W := EvenBlocks.WS S c (−1)` (the indices of `𝒞_{−1}` other than `0`); on `B(W)` every point is
`−1` (`EvenMinus.boxS_c_WS`).

* (M1) `EvenMinus.lemmaM1`, (M2) `EvenMinus.lemmaM2`: the local forms of `MinusCoord.lean` for
  `B(W)`.
* (M4) `EvenMinus.lemmaM4`: `g_P = (unit)·D_P` with `D_P = Π D(y_i, y_l)` over the pairs `{i < l}`
  of `P` with `i ≠ 0`, `D = ColOne.Dab (q + 1)` and `y = u − u^{−1}`, `u = −t`.
* The transport to the coordinates: `EvenMinus.IcS_eq_map`, `EvenMinus.finrank_IcS_eq`
  (model: `ColOne.Ic1_eq_map`, `ColOne.finrank_Ic1_eq`).
-/

@[expose] public section

open MvPolynomial

namespace EvenMinus

open ColSplit ColSurv ColComp ColTensor ColDecomp EvenBlocks Peel

open scoped Classical

variable {F : Type*} [Field F] (S : ColSetting F) {k : ℕ}

/-! ### The block `W = 𝒞_ζ ∖ {0}` -/

/-- **Part M** of `q_even_block_minus.md` (setting): `j ∈ W_ζ^S` iff `j + 1 ∈ 𝒞_ζ`. -/
theorem mem_WS {c : Fin (2 * k + 1) → S.μ} {ζ : F} {j : Fin (2 * k + 1)} :
    j ∈ WS S c ζ ↔ j.succ ∈ cls (cExt c) ζ := by
  simp [WS, varSet]

/-- **Part M** of `q_even_block_minus.md` (setting): on `W_ζ^S` every point `c_s` is `ζ`; for
`ζ = −1`, `B(W)` is a box at the point `−1`, i.e. `(t_s + 1)^q = 0`. -/
theorem boxS_c_WS (c : Fin (2 * k + 1) → S.μ) (ζ : F) : ∀ s : WS S c ζ, (boxS S c).c s = ζ := by
  intro s
  have := (mem_WS S).1 s.2
  rw [mem_cls] at this
  simpa [boxS, cExt] using this

/-! ### (M1) and (M2) for the block of colour `−1` -/

/-- **Part M, (M1)** of `q_even_block_minus.md`: the isomorphism
`Ψ : F[y_1, …, y_n]/(y_i^q) ≃ B(W)`, `W = W_{−1}^S`, for a bijection `e : [n] → W`. -/
noncomputable def PsiMW (hneg : (-1 : F) ≠ 1) (c : Fin (2 * k + 1) → S.μ) {n : ℕ}
    (e : Fin n ≃ WS S c (-1)) : C F (S.q + 1) n ≃ₐ[F] (boxS S c).Box (WS S c (-1)) :=
  PsiM S (EvenColours.p_ne_two_of_neg_one_ne_one S hneg) rfl (boxS_c_WS S c (-1)) e

/-- **Part M, (M1)** of `q_even_block_minus.md`: `Ψ(y_i) = u − u^{−1}`, `u = −t_{e(i)}`. -/
theorem PsiMW_X (hneg : (-1 : F) ≠ 1) (c : Fin (2 * k + 1) → S.μ) {n : ℕ}
    (e : Fin n ≃ WS S c (-1)) (i : Fin n) :
    PsiMW S hneg c e (Ideal.Quotient.mk _ (X i)) = yM (boxS S c) (WS S c (-1)) (e i) :=
  PsiM_X S _ rfl (boxS_c_WS S c (-1)) e i

/-- **Part M, (M1)** of `q_even_block_minus.md`: **Coordinates.** If `(−1 : F) ≠ 1`, for every
bijection `e : [n] → W` (`W = W_{−1}^S`; for instance the order bijection with `n = |W|`) there
is an `F`-algebra isomorphism `Ψ : Peel.C F (q + 1) n ≃ₐ[F] B(W)` with `Ψ(y_i) = u − u^{−1}`,
`u = −t_{e(i)}`. (More general than the file: any bijection `e`.) -/
theorem lemmaM1 (hneg : (-1 : F) ≠ 1) (c : Fin (2 * k + 1) → S.μ) {n : ℕ}
    (e : Fin n ≃ WS S c (-1)) :
    ∃ Ψ : C F (S.q + 1) n ≃ₐ[F] (boxS S c).Box (WS S c (-1)), ∀ i,
      Ψ (Ideal.Quotient.mk _ (X i)) =
        -(boxS S c).t _ (e i) - Ring.inverse (-(boxS S c).t _ (e i)) :=
  ⟨PsiMW S hneg c e, PsiMW_X S hneg c e⟩

/-- **Part M, (M2)** of `q_even_block_minus.md`: **Units and the pair factor.** If
`(−1 : F) ≠ 1`: for `s ∈ W`, `t_s − 1` is a unit of `B(W)`; for `i, l ∈ W`,
`t_i t_l − 1 = (unit)·(y_i + y_l)` with `y = u − u^{−1}`, `u = −t` (`= Ψ(y)` by (M1)). (The file
assumes `i ≠ l`; the statement holds for all `i, l`.) -/
theorem lemmaM2 (hneg : (-1 : F) ≠ 1) (c : Fin (2 * k + 1) → S.μ) :
    (∀ s : WS S c (-1), IsUnit ((boxS S c).t _ s - 1)) ∧
    ∀ i l : WS S c (-1), ∃ u : ((boxS S c).Box (WS S c (-1)))ˣ,
      (boxS S c).t _ i * (boxS S c).t _ l - 1 =
        u * (yM (boxS S c) (WS S c (-1)) i + yM (boxS S c) (WS S c (-1)) l) :=
  lemmaM2_box S (EvenColours.p_ne_two_of_neg_one_ne_one S hneg) (boxS_c_WS S c (-1))

/-! ### (M4) The generators -/

/-- **Part M, (M4)** of `q_even_block_minus.md`: `y_a := u_a − u_a^{−1}`, `u_a := −t_a`, for an
index `a ∈ V` (for `a = 0` an unused dummy value). -/
noncomputable def yMB (c : Fin (2 * k + 1) → S.μ) (a : Fin (2 * k + 2)) :
    (boxS S c).Box (WS S c (-1)) :=
  -tB S c (WS S c (-1)) a - Ring.inverse (-tB S c (WS S c (-1)) a)

/-- **Part M, (M4)** of `q_even_block_minus.md`: `y_{j+1} = y_j` for `j ∈ W`. -/
theorem yMB_succ (c : Fin (2 * k + 1) → S.μ) {j : Fin (2 * k + 1)} (h : j ∈ WS S c (-1)) :
    yMB S c j.succ = yM (boxS S c) (WS S c (-1)) ⟨j, h⟩ := by
  simp only [yMB, ColOne.tB_succ S c _ h, yM]

/-- **Part M, (M4)** of `q_even_block_minus.md`: `D_P := Π D(y_i, y_l)` over the pairs `{i < l}`
of the perfect matching `P` of `𝒞_{−1}` with `i ≠ 0`, `D = ColOne.Dab (q + 1)`. -/
noncomputable def DPM (c : Fin (2 * k + 1) → S.μ) (P : PerfMatch (cls (cExt c) (-1))) :
    (boxS S c).Box (WS S c (-1)) :=
  ∏ x ∈ Finset.univ.filter (fun x => x.1 ≠ 0 ∧ x.1 < (P.1 x).1),
    ColOne.Dab (S.q + 1) (yMB S c x.1) (yMB S c (P.1 x).1)

/-- **Part M, (M4)** of `q_even_block_minus.md` (proof): for a pair `{a < b}` of `𝒞_{−1}`,
`f_{0,b} = t_b − 1` is a unit and, for `a ≠ 0`, `f_{a,b} = (unit)·D(y_a, y_b)` (by (M2) and (M3)). -/
theorem pairF_eq_unit_mulM (hneg : (-1 : F) ≠ 1) (c : Fin (2 * k + 1) → S.μ)
    {a b : Fin (2 * k + 2)} (ha : a ∈ cls (cExt c) (-1)) (hb : b ∈ cls (cExt c) (-1))
    (hb0 : b ≠ 0) :
    ∃ u : ((boxS S c).Box (WS S c (-1)))ˣ, pairF S.q (tB S c (WS S c (-1))) a b =
      u * (if a = 0 then 1 else ColOne.Dab (S.q + 1) (yMB S c a) (yMB S c b)) := by
  obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.2 hb0
  have hj : j ∈ WS S c (-1) := (mem_WS S).2 hb
  obtain ⟨hU, hP⟩ := lemmaM2 S hneg c
  have hu := hU ⟨j, hj⟩
  by_cases ha0 : a = 0
  · subst ha0
    refine ⟨hu.unit, ?_⟩
    rw [pairF, if_pos rfl, if_pos rfl, mul_one, IsUnit.unit_spec, ColOne.tB_succ S c _ hj]
  · obtain ⟨i, rfl⟩ := Fin.exists_succ_eq.2 ha0
    have hi : i ∈ WS S c (-1) := (mem_WS S).2 ha
    obtain ⟨u2, hu2⟩ := hP ⟨i, hi⟩ ⟨j, hj⟩
    refine ⟨hu.unit * u2 ^ (S.q - 1), ?_⟩
    rw [pairF, if_neg (Fin.succ_ne_zero i), if_neg (Fin.succ_ne_zero i),
      ColOne.tB_succ S c _ hj, ColOne.tB_succ S c _ hi, yMB_succ S c hi, yMB_succ S c hj, hu2,
      mul_pow, add_pow_eq_Dab S, Units.val_mul, Units.val_pow_eq_pow_val, IsUnit.unit_spec]
    ring

/-- **Part M, (M4)** of `q_even_block_minus.md`: **The generators.** If `(−1 : F) ≠ 1`, for a
perfect matching `P` of `𝒞_{−1}`: `gPS S c (−1) P = (unit)·D_P`, `D_P = Π D(y_i, y_l)` over the
pairs `{i < l}` of `P` with `i ≠ 0` (the pair `{0, k_0}`, if any, contributes the unit
`t_{k_0} − 1`). Together with `EvenMinus.Psi_fpolyM`, `D_P = Ψ(Π D(y_i, y_l))`. -/
theorem lemmaM4 (hneg : (-1 : F) ≠ 1) (c : Fin (2 * k + 1) → S.μ)
    (P : PerfMatch (cls (cExt c) (-1))) :
    ∃ u : ((boxS S c).Box (WS S c (-1)))ˣ, gPS S c (-1) P = u * DPM S c P := by
  set Fs := Finset.univ.filter (fun x : cls (cExt c) (-1) => x.1 < (P.1 x).1)
  have H : ∀ x : cls (cExt c) (-1), x.1 < (P.1 x).1 →
      ∃ u : ((boxS S c).Box (WS S c (-1)))ˣ,
        pairF S.q (tB S c (WS S c (-1))) x.1 (P.1 x).1 =
          u * (if x.1 = 0 then 1 else
            ColOne.Dab (S.q + 1) (yMB S c x.1) (yMB S c (P.1 x).1)) := fun x hx =>
    pairF_eq_unit_mulM S hneg c x.2 (P.1 x).2 (ne_of_gt (lt_of_le_of_lt (Fin.zero_le _) hx))
  set U : cls (cExt c) (-1) → ((boxS S c).Box (WS S c (-1)))ˣ := fun x =>
    if h : x.1 < (P.1 x).1 then (H x h).choose else 1
  refine ⟨∏ x ∈ Fs, U x, ?_⟩
  have e1 : gPS S c (-1) P = ∏ x ∈ Fs, ((U x : (boxS S c).Box (WS S c (-1))) *
      (if x.1 = 0 then 1 else
        ColOne.Dab (S.q + 1) (yMB S c x.1) (yMB S c (P.1 x).1))) := by
    refine Finset.prod_congr rfl fun x hx => ?_
    have hx' : x.1 < (P.1 x).1 := (Finset.mem_filter.1 hx).2
    simp only [U, dif_pos hx']
    exact (H x hx').choose_spec
  rw [e1, Finset.prod_mul_distrib, Units.coe_prod]
  congr 1
  have e2 : Finset.univ.filter (fun x : cls (cExt c) (-1) => x.1 ≠ 0 ∧ x.1 < (P.1 x).1) =
      Fs.filter (fun x => x.1 ≠ 0) := by
    ext x
    simp only [Fs, Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  rw [DPM, e2, Finset.prod_filter (s := Fs)]
  refine Finset.prod_congr rfl fun x _ => ?_
  by_cases h : x.1 = 0 <;> simp [h]

/-! ### Transport to the coordinates -/

variable {ι : Type*} [Fintype ι] [LinearOrder ι] {c : Fin (2 * k + 1) → S.μ}

omit S in
/-- **Part M, (M5), (M6)** of `q_even_block_minus.md` (proof; model `ColOne.conjPM`): the perfect
matching `ē ∘ P' ∘ ē^{−1}` of `α` obtained from a perfect matching `P'` of `ι` and a bijection
`ē : ι → α`. -/
def conjPMT {α : Type*} (ē : ι ≃ α) (P : PerfMatch ι) : PerfMatch α :=
  ⟨fun x => ē (P.1 (ē.symm x)), fun x => by
    refine ⟨fun h => (P.2 (ē.symm x)).1 ?_, ?_⟩
    · have := congrArg ē.symm h
      simpa using this
    · simp [(P.2 _).2]⟩

omit S [Fintype ι] [LinearOrder ι] in
/-- **Part M, (M5), (M6)** of `q_even_block_minus.md` (proof; model `ColOne.conjPM_surjective`):
every perfect matching of `α` is of the form `ē ∘ P' ∘ ē^{−1}`. -/
theorem conjPMT_surjective {α : Type*} (ē : ι ≃ α) : Function.Surjective (conjPMT ē) := by
  intro P
  refine ⟨⟨fun a => ē.symm (P.1 (ē a)), fun a => ?_⟩, ?_⟩
  · refine ⟨fun h => (P.2 (ē a)).1 ?_, ?_⟩
    · have := congrArg ē h
      simpa using this
    · simp [(P.2 _).2]
  · exact PerfMatch.ext fun x => by simp [conjPMT]

/-- **Part M, (M5), (M6)** of `q_even_block_minus.md` (proof; model `ColOne.fpoly`): the polynomial
`Π D(y_{κ(a)}, y_{κ(b)}) ∈ F[y_1, …, y_n]` over the pairs `{a < b}` of a perfect matching `P'` of
`ι` with `ē(a) ≠ 0`, `D = ColOne.Dab (q + 1)`. -/
noncomputable def fpolyM (ē : ι ≃o cls (cExt c) (-1)) {n : ℕ} (κ : ι → Fin n)
    (P : PerfMatch ι) : MvPolynomial (Fin n) F :=
  ∏ a ∈ Finset.univ.filter (fun a => (ē a).1 ≠ 0 ∧ a < P.1 a),
    ColOne.Dab (S.q + 1) (X (κ a)) (X (κ (P.1 a)))

/-- **Part M, (M4)** of `q_even_block_minus.md` (in the coordinates): for `ē` increasing and
compatible with `e`, `Ψ(Π D(y_{κ(a)}, y_{κ(b)})) = D_P` for `P = ē ∘ P' ∘ ē^{−1}`. -/
theorem Psi_fpolyM (hneg : (-1 : F) ≠ 1) (ē : ι ≃o cls (cExt c) (-1)) {n : ℕ}
    (e : Fin n ≃ WS S c (-1)) (κ : ι → Fin n)
    (hκ : ∀ a, (ē a).1 ≠ 0 → (e (κ a)).1.succ = (ē a).1) (P : PerfMatch ι) :
    PsiMW S hneg c e (Ideal.Quotient.mk _ (fpolyM S ē κ P)) =
      DPM S c (conjPMT ē.toEquiv P) := by
  have hy : ∀ a, (ē a).1 ≠ 0 →
      PsiMW S hneg c e (Ideal.Quotient.mk _ (X (κ a))) = yMB S c (ē a).1 := by
    intro a ha
    rw [PsiMW_X, ← hκ a ha, yMB_succ S c (e (κ a)).2]
  rw [fpolyM, map_prod, map_prod, DPM]
  refine Finset.prod_equiv ē.toEquiv ?_ ?_
  · intro a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    change _ ↔ (ē a).1 ≠ 0 ∧ (ē a).1 < (ē (P.1 (ē.symm (ē a)))).1
    rw [Subtype.coe_lt_coe, ē.symm_apply_apply, ē.lt_iff_lt]
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    have hPa : (ē (P.1 a)).1 ≠ 0 := by
      have : (ē a).1 < (ē (P.1 a)).1 := by rw [Subtype.coe_lt_coe, ē.lt_iff_lt]; exact ha.2
      exact ne_of_gt (lt_of_le_of_lt (Fin.zero_le _) this)
    rw [ColOne.map_Dab, ColOne.map_Dab, hy a ha.1, hy _ hPa]
    simp [conjPMT]

/-- **Part M, (M4)** of `q_even_block_minus.md`, in the coordinates of (M1): for a perfect matching
`P = ē ∘ P' ∘ ē^{−1}` of `𝒞_{−1}` (`ē : ι ≃o 𝒞_{−1}` increasing, compatible with
`e : [n] → W` through `κ`), `gPS S c (−1) P = (unit)·Ψ(Π D(y_{κ(a)}, y_{κ(b)}))`, the product
over the pairs `{a < b}` of `P'` with `ē(a) ≠ 0`. -/
theorem lemmaM4_coord (hneg : (-1 : F) ≠ 1) (ē : ι ≃o cls (cExt c) (-1)) {n : ℕ}
    (e : Fin n ≃ WS S c (-1)) (κ : ι → Fin n)
    (hκ : ∀ a, (ē a).1 ≠ 0 → (e (κ a)).1.succ = (ē a).1) (P : PerfMatch ι) :
    ∃ u : ((boxS S c).Box (WS S c (-1)))ˣ, gPS S c (-1) (conjPMT ē.toEquiv P) =
      u * PsiMW S hneg c e (Ideal.Quotient.mk _ (fpolyM S ē κ P)) := by
  rw [Psi_fpolyM S hneg ē e κ hκ]
  exact lemmaM4 S hneg c _

/-- **Part M, (M5), (M6)** of `q_even_block_minus.md` (proof; model `ColOne.Ic1_eq_map`):
`I_{c,−1} = Ψ((Π D(y_{κ(a)}, y_{κ(b)}) : P'))` — the generators agree up to units by (M4). -/
theorem IcS_eq_map (hneg : (-1 : F) ≠ 1) (ē : ι ≃o cls (cExt c) (-1)) {n : ℕ}
    (e : Fin n ≃ WS S c (-1)) (κ : ι → Fin n)
    (hκ : ∀ a, (ē a).1 ≠ 0 → (e (κ a)).1.succ = (ē a).1) :
    IcS S c (-1) = (Ideal.span (Set.range fun P : PerfMatch ι =>
      (Ideal.Quotient.mk (powIdeal F (S.q + 1) n) (fpolyM S ē κ P)))).map (PsiMW S hneg c e) := by
  rw [Ideal.map_span, ← Set.range_comp, IcS]
  apply ColPairs.span_eq_of_units
  · rintro _ ⟨P, rfl⟩
    obtain ⟨P', rfl⟩ := conjPMT_surjective ē.toEquiv P
    obtain ⟨u, hu⟩ := lemmaM4 S hneg c (conjPMT ē.toEquiv P')
    exact ⟨_, ⟨P', rfl⟩, u, by rw [hu, Function.comp_apply, Psi_fpolyM S hneg ē e κ hκ]⟩
  · rintro _ ⟨P', rfl⟩
    obtain ⟨u, hu⟩ := lemmaM4 S hneg c (conjPMT ē.toEquiv P')
    exact ⟨_, ⟨conjPMT ē.toEquiv P', rfl⟩, u,
      by rw [hu, Function.comp_apply, Psi_fpolyM S hneg ē e κ hκ]⟩

/-- **Part M, (M5), (M6)** of `q_even_block_minus.md` (proof; model `ColOne.finrank_Ic1_eq`):
`dim_F I_{c,−1} = dim_F (Π D(y_{κ(a)}, y_{κ(b)}) : P')·C_n`, in `C_n = F[y]/(y_i^q)`
(`= Peel.C F (q + 1) n`). -/
theorem finrank_IcS_eq (hneg : (-1 : F) ≠ 1) (ē : ι ≃o cls (cExt c) (-1)) {n : ℕ}
    (e : Fin n ≃ WS S c (-1)) (κ : ι → Fin n)
    (hκ : ∀ a, (ē a).1 ≠ 0 → (e (κ a)).1.succ = (ē a).1) :
    Module.finrank F (IcS S c (-1)) =
      Module.finrank F ((Ideal.span (Set.range fun P : PerfMatch ι =>
        Ideal.Quotient.mk (powIdeal F (S.q + 1) n) (fpolyM S ē κ P))).restrictScalars F) := by
  rw [IcS_eq_map S hneg ē e κ hκ, ColPairs.finrank_map_algEquiv]

end EvenMinus

end
