module

public import RequestProject.OddEquality.PartC
public import RequestProject.OddShapes.Identities
public import RequestProject.EveryField.Integral

/-!
# Part B of `q_oddbox_equality.md`: the pairing bound

This file formalizes **Part B** of `q_oddbox_equality.md`: the perfect pairing of the box ring
`C = Peel.C F q n` given by the coefficient of the top monomial (for every box `q ≥ 2`, a more
general statement than the odd box), the annihilator inclusion `⋂_P I_P·C ⊆ Ann(ℳ)` at the odd box
`q = 2h + 2`, and the bound `dim ℳ ≤ dim C/⋂_P I_P·C`.
-/

@[expose] public section

open MvPolynomial

namespace OddEquality

set_option synthInstance.maxHeartbeats 200000

variable {F : Type*} [Field F] {q n : ℕ}

/-! ### (B1) The pairing -/

/-- **(B1)** of `q_oddbox_equality.md`: the exponent `(q − 2, …, q − 2)` of the top monomial
`Π_i y_i^{q−2}` of the box ring (`q − 2 = r − 1`). -/
noncomputable def topExp (q n : ℕ) : Fin n →₀ ℕ := Finsupp.equivFunOnFinite.symm fun _ => q - 2

/-- **(B1)** of `q_oddbox_equality.md` (proof): the coefficient of the top monomial vanishes on the
box ideal. -/
theorem topCoeff_le (hq : 2 ≤ q) :
    (Peel.powIdeal F q n).restrictScalars F ≤ LinearMap.ker (lcoeff F (topExp q n)) := by
  intro p hp
  rw [Submodule.restrictScalars_mem, mem_powIdeal_iff] at hp
  rw [LinearMap.mem_ker, lcoeff_apply]
  by_contra h0
  obtain ⟨i, hi⟩ := hp _ (mem_support_iff.2 h0)
  simp [topExp] at hi
  omega

/-- **(B1)** of `q_oddbox_equality.md`: the linear form `f ↦` the coefficient of the top monomial
`Π_i y_i^{q−2}` of `f ∈ C = Peel.C F q n` (well defined for `q ≥ 2`). -/
noncomputable def topCoeff (hq : 2 ≤ q) : Peel.C F q n →ₗ[F] F :=
  (((Peel.powIdeal F q n).restrictScalars F).liftQ (lcoeff F (topExp q n)) (topCoeff_le hq)).comp
    (Submodule.Quotient.restrictScalarsEquiv F (Peel.powIdeal F q n)).symm.toLinearMap

/-- **(B1)** of `q_oddbox_equality.md` (proof): `⟨mk p⟩_top` is the top coefficient of `p`. -/
theorem topCoeff_mk (hq : 2 ≤ q) (p : MvPolynomial (Fin n) F) :
    topCoeff hq (Ideal.Quotient.mk (Peel.powIdeal F q n) p) = coeff (topExp q n) p := rfl

/-- **(B1)** of `q_oddbox_equality.md`: the pairing `⟨f, g⟩ :=` the coefficient of the top monomial
in `f·g`, as the map `g ↦ ⟨·, g⟩` from `C` to its dual. -/
noncomputable def pairing (hq : 2 ≤ q) : Peel.C F q n →ₗ[F] Module.Dual F (Peel.C F q n) :=
  LinearMap.mk₂ F (fun g f => topCoeff hq (f * g))
    (fun g g' f => by dsimp only; rw [mul_add, map_add])
    (fun c g f => by dsimp only; rw [mul_smul_comm, map_smul])
    (fun g f f' => by dsimp only; rw [add_mul, map_add])
    (fun c g f => by dsimp only; rw [smul_mul_assoc, map_smul])

/-- **(B1)** of `q_oddbox_equality.md`: the value of the pairing. -/
theorem pairing_apply (hq : 2 ≤ q) (g f : Peel.C F q n) :
    pairing hq g f = topCoeff hq (f * g) := rfl

/-- **(B1)** of `q_oddbox_equality.md`: the pairing is perfect (nondegenerate): if
`⟨f, g⟩ = 0` for every `f`, then `g = 0` (the monomial `y^α`, `α` in the box, pairs to `1` with
`y^{(r−1) − α}`). -/
theorem pairing_injective (hq : 2 ≤ q) : Function.Injective (pairing (F := F) (n := n) hq) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro g hg
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective g
  by_contra hne
  have hp : p ∉ Peel.powIdeal F q n := fun h => hne (Ideal.Quotient.eq_zero_iff_mem.2 h)
  rw [mem_powIdeal_iff] at hp
  push_neg at hp
  obtain ⟨s, hs, hlt⟩ := hp
  have hst : s ≤ topExp q n := fun i => by simp [topExp]; have := hlt i; omega
  have h := LinearMap.congr_fun hg (Ideal.Quotient.mk _ (monomial (topExp q n - s) 1))
  rw [pairing_apply, ← map_mul, topCoeff_mk, coeff_monomial_mul', if_pos tsub_le_self,
    tsub_tsub_cancel_of_le hst, one_mul, LinearMap.zero_apply] at h
  exact (mem_support_iff.1 hs) h

/-- **(B1)** of `q_oddbox_equality.md`: the orthogonal `V^⊥ := {g : ⟨f, g⟩ = 0 for all f ∈ V}` of an
`F`-subspace `V ⊆ C`. -/
noncomputable def perp (hq : 2 ≤ q) (V : Submodule F (Peel.C F q n)) :
    Submodule F (Peel.C F q n) :=
  V.dualAnnihilator.comap (pairing hq)

/-- **(B1)** of `q_oddbox_equality.md`: the annihilator `Ann(V) := {g : g·V = 0}` of an
`F`-subspace `V ⊆ C`, as an `F`-subspace. -/
def annF (V : Submodule F (Peel.C F q n)) : Submodule F (Peel.C F q n) where
  carrier := {g | ∀ f ∈ V, g * f = 0}
  add_mem' ha hb f hf := by rw [add_mul, ha f hf, hb f hf, add_zero]
  zero_mem' f _ := zero_mul f
  smul_mem' c g hg f hf := by rw [smul_mul_assoc, hg f hf, smul_zero]

/-- **(B1)** of `q_oddbox_equality.md` (auxiliary): `C` is finite-dimensional. -/
theorem finiteDimensional_C : FiniteDimensional F (Peel.C F q n) :=
  Module.Finite.of_surjective _ (EveryField.boxToC_surjective (F := F) (q := q) n)

/-- **(B1)** of `q_oddbox_equality.md`: for every `F`-subspace `V ⊆ C` (any box `q ≥ 2`):
`dim V + dim V^⊥ = dim C`, `Ann(V) ⊆ V^⊥`, hence `dim V + dim Ann(V) ≤ dim C`. (The file states the
last two for an ideal `V`; they hold for every subspace.) -/
theorem B1 (hq : 2 ≤ q) (V : Submodule F (Peel.C F q n)) :
    Module.finrank F V + Module.finrank F (perp hq V) = Module.finrank F (Peel.C F q n) ∧
      annF V ≤ perp hq V ∧
      Module.finrank F V + Module.finrank F (annF V) ≤ Module.finrank F (Peel.C F q n) := by
  haveI := finiteDimensional_C (F := F) (q := q) (n := n)
  have hsurj : Function.Surjective (pairing (F := F) (n := n) hq) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (Subspace.dual_finrank_eq).symm).1 (pairing_injective hq)
  let e := LinearEquiv.ofBijective (pairing (F := F) (n := n) hq) ⟨pairing_injective hq, hsurj⟩
  have h1 : Module.finrank F V + Module.finrank F (perp hq V) =
      Module.finrank F (Peel.C F q n) := by
    have hp : perp hq V = V.dualAnnihilator.map e.symm.toLinearMap := by
      rw [perp, ← Submodule.comap_equiv_eq_map_symm]
      rfl
    rw [hp, LinearEquiv.finrank_map_eq]
    exact Subspace.finrank_add_finrank_dualAnnihilator_eq V
  have h2 : annF V ≤ perp hq V := by
    intro g hg
    change pairing hq g ∈ V.dualAnnihilator
    rw [Submodule.mem_dualAnnihilator]
    intro f hf
    rw [pairing_apply, mul_comm, hg f hf, map_zero]
  exact ⟨h1, h2, by have := Submodule.finrank_mono h2; omega⟩

/-! ### (B2) -/

/-- **(B2)** of `q_oddbox_equality.md`: `(y_a + y_b)·D(y_a, y_b) = y_a^r + y_b^r = 0` in
`C = Peel.C F (2h+2) n` (`r = 2h + 1` odd, `OddShapes.A3_D`). -/
theorem B2_pair (h : ℕ) (a b : Fin n) :
    (Tight.y F (2 * h + 2) a + Tight.y F (2 * h + 2) b) * Tight.D F (2 * h + 2) a b = 0 := by
  have e := OddShapes.A3_D (2 * h + 1) ⟨h, rfl⟩ (Tight.y F (2 * h + 2) a) (Tight.y F (2 * h + 2) b)
  have hy : ∀ c : Fin n, Tight.y F (2 * h + 2) c ^ (2 * h + 1) = 0 := fun c =>
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨c, rfl⟩)
  rw [hy, hy, add_zero] at e
  exact e

/-- **(B2)** of `q_oddbox_equality.md`: for a perfect matching `P` and every `a`,
`(y_a + y_{P(a)})·D_P = 0`. -/
theorem B2_DP (h : ℕ) (P : ColComp.PerfMatch (Fin n)) (a : Fin n) :
    (Tight.y F (2 * h + 2) a + Tight.y F (2 * h + 2) (P.1 a)) * ColOne.DPn F (2 * h + 2) P = 0 := by
  have key : ∀ b, b < P.1 b →
      (Tight.y F (2 * h + 2) b + Tight.y F (2 * h + 2) (P.1 b)) * ColOne.DPn F (2 * h + 2) P = 0 := by
    intro b hb
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun a => Tight.D F (2 * h + 2) a (P.1 a))
      (s := Finset.univ.filter (fun a => a < P.1 a))
      (Finset.mem_filter.2 ⟨Finset.mem_univ b, hb⟩)
    rw [ColOne.DPn, hc, ← mul_assoc, B2_pair, zero_mul]
  by_cases ha : a < P.1 a
  · exact key a ha
  · have hlt : P.1 a < a := lt_of_le_of_ne (not_lt.1 ha) (P.2 a).1
    have h2 := key (P.1 a) (by rwa [(P.2 a).2])
    rwa [(P.2 a).2, add_comm (Tight.y F (2 * h + 2) (P.1 a))] at h2

/-- **(B2)** of `q_oddbox_equality.md`: `I_P·C ⊆ Ann(D_P)`. -/
theorem B2_IPC (h : ℕ) (P : ColComp.PerfMatch (Fin n)) {g : Peel.C F (2 * h + 2) n}
    (hg : g ∈ IPC F (2 * h + 2) P) : g * ColOne.DPn F (2 * h + 2) P = 0 := by
  induction hg using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    exact B2_DP h P a
  | zero => exact zero_mul _
  | add x z _ _ hx hz => rw [add_mul, hx, hz, add_zero]
  | smul c x _ hx => rw [smul_eq_mul, mul_assoc, hx, mul_zero]

/-- **(B2)** of `q_oddbox_equality.md`: `⋂_P I_P·C ⊆ Ann(ℳ)` in `C = Peel.C F (2h+2) n`. -/
theorem B2 (h : ℕ) :
    (Kint F (2 * h + 2) n).restrictScalars F ≤
      annF ((Mideal F (2 * h + 2) n).restrictScalars F) := by
  intro g hg f hf
  rw [Submodule.restrictScalars_mem, Kint, Submodule.mem_iInf] at hg
  rw [Submodule.restrictScalars_mem] at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨P, rfl⟩ := hx
    exact B2_IPC h P (hg P)
  | zero => exact mul_zero _
  | add x z _ _ hx hz => rw [mul_add, hx, hz, add_zero]
  | smul c x _ hx => rw [smul_eq_mul, mul_left_comm, hx, mul_zero]

/-! ### (B3) -/

/-- **(B3)** of `q_oddbox_equality.md`: `dim ℳ ≤ dim C/⋂_P I_P·C` in `C = Peel.C F (2h+2) n`, for
every field `F`, every `h` and every `n`. -/
theorem B3 (h : ℕ) :
    Module.finrank F ((Mideal F (2 * h + 2) n).restrictScalars F) ≤
      Module.finrank F (Peel.C F (2 * h + 2) n ⧸ Kint F (2 * h + 2) n) := by
  haveI := finiteDimensional_C (F := F) (q := 2 * h + 2) (n := n)
  have h1 := (B1 (by omega) ((Mideal F (2 * h + 2) n).restrictScalars F)).2.2
  have h2 := Submodule.finrank_mono (B2 (F := F) (n := n) h)
  have h3 := Submodule.finrank_quotient_add_finrank ((Kint F (2 * h + 2) n).restrictScalars F)
  rw [(Submodule.Quotient.restrictScalarsEquiv F (Kint F (2 * h + 2) n)).finrank_eq] at h3
  omega

end OddEquality

end
