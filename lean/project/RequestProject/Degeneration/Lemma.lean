module

public import RequestProject.Degeneration.Defs

/-!
# The Lemma of `q_degeneration.md`: top-degree forms

This file proves parts (i) and (ii) of the **Lemma** of `q_degeneration.md`, together with the
descriptions of `gr(I)` given in its **Setting**.

The proof of (ii) follows the **Proof** of the source: writing `S_{≤d}` for the polynomials of total
degree `≤ d` and `gr(I)_d := {f_d : f ∈ I ∩ S_{≤d}}` (the degree-`d` components), the map
"degree-`d` component" `I ∩ S_{≤d} → gr(I)_d` is onto with kernel `I ∩ S_{≤d−1}`, so
`dim (I ∩ S_{≤d}) = Σ_{e ≤ d} dim gr(I)_e`.  The same holds for `gr(I)` in place of `I`, with the same
spaces `gr(I)_e`; hence `S_{≤d}/(I ∩ S_{≤d})` and `S_{≤d}/(gr(I) ∩ S_{≤d})` have the same dimension
for every `d`, and letting `d → ∞` gives `dim S/gr(I) = dim S/I`.
-/

@[expose] public section

open MvPolynomial

namespace Degeneration

variable {F : Type*} [Field F] {m : ℕ}

/-- Proof of part (ii) of the Lemma of `q_degeneration.md`: the degree-`d` part
`gr(K)_d := {f_d : f ∈ K, deg f ≤ d}` of an `F`-subspace `K ⊆ S`. -/
noncomputable def grPart (K : Submodule F (MvPolynomial (Fin m) F)) (d : ℕ) :
    Submodule F (MvPolynomial (Fin m) F) :=
  (K ⊓ restrictTotalDegree (Fin m) F d).map (homogeneousComponent d)

/-- Proof of part (ii) of the Lemma of `q_degeneration.md`: the degree-`d` component of
`monomial a c * p` is `monomial a c` times the degree-`(d - |a|)` component of `p`. -/
theorem homogeneousComponent_monomial_mul (d : ℕ) (a : Fin m →₀ ℕ) (c : F)
    (p : MvPolynomial (Fin m) F) :
    homogeneousComponent d (monomial a c * p) =
      if a.degree ≤ d then monomial a c * homogeneousComponent (d - a.degree) p else 0 := by
  ext n
  have key : ∀ n : Fin m →₀ ℕ, a ≤ n → (n - a).degree + a.degree = n.degree := by
    intro n h
    rw [← map_add, tsub_add_cancel_of_le h]
  rw [coeff_homogeneousComponent, coeff_monomial_mul']
  split_ifs with h1 h2 h3 <;> simp_all [coeff_monomial_mul', coeff_homogeneousComponent]
  · intro h; have := key n h2; omega
  · have := key n h2; omega
  · intro h h'; have := key n h; omega

/-- Proof of part (ii) of the Lemma of `q_degeneration.md`: membership in the degree-`d` part. -/
theorem mem_grPart {K : Submodule F (MvPolynomial (Fin m) F)} {d : ℕ}
    {φ : MvPolynomial (Fin m) F} :
    φ ∈ grPart K d ↔ ∃ f ∈ K, f.totalDegree ≤ d ∧ homogeneousComponent d f = φ := by
  simp only [grPart, Submodule.mem_map, Submodule.mem_inf, mem_restrictTotalDegree, and_assoc]

/-- Proof of part (ii) of the Lemma of `q_degeneration.md`: the total degree of
`monomial a c * f` is at most `|a| + deg f`. -/
theorem totalDegree_monomial_mul_le (a : Fin m →₀ ℕ) (c : F) (f : MvPolynomial (Fin m) F) :
    (monomial a c * f).totalDegree ≤ a.degree + f.totalDegree :=
  (totalDegree_mul _ _).trans (Nat.add_le_add_right (totalDegree_monomial_le a c) _)

/-- **Setting** of `q_degeneration.md`: every homogeneous component of an element of `gr(I)` lies
in the degree-`d` part `{f_d : f ∈ I, deg f ≤ d}`. -/
theorem homogeneousComponent_mem_grPart_of_mem_gr {I : Ideal (MvPolynomial (Fin m) F)}
    {p : MvPolynomial (Fin m) F} (hp : p ∈ gr I) (d : ℕ) :
    homogeneousComponent d p ∈ grPart (I.restrictScalars F) d := by
  let G : Ideal (MvPolynomial (Fin m) F) :=
    { carrier := {p | ∀ d, homogeneousComponent d p ∈ grPart (I.restrictScalars F) d}
      add_mem' := fun ha hb d => by rw [map_add]; exact add_mem (ha d) (hb d)
      zero_mem' := fun d => by rw [map_zero]; exact zero_mem _
      smul_mem' := fun r p hp => by
        induction r using MvPolynomial.induction_on' with
        | monomial u a =>
          intro d
          rw [smul_eq_mul, homogeneousComponent_monomial_mul]
          split_ifs with hu
          · obtain ⟨f, hfI, hfd, hf⟩ := mem_grPart.1 (hp (d - u.degree))
            refine mem_grPart.2 ⟨monomial u a * f, I.mul_mem_left _ hfI,
              (totalDegree_monomial_mul_le u a f).trans (by omega), ?_⟩
            rw [homogeneousComponent_monomial_mul, if_pos hu, hf]
          · exact zero_mem _
        | add r₁ r₂ h₁ h₂ =>
          intro d
          rw [add_smul, map_add]
          exact add_mem (h₁ d) (h₂ d) }
  have hle : gr I ≤ G := by
    rw [gr, Ideal.span_le]
    rintro _ ⟨f, hfI, -, rfl⟩ d
    show homogeneousComponent d (top f) ∈ _
    rw [top, homogeneousComponent_of_mem (homogeneousComponent_mem _ _)]
    split_ifs with hd
    · exact mem_grPart.2 ⟨f, hfI, hd.ge, by rw [hd]⟩
    · exact zero_mem _
  exact hle hp d

/-- **Setting** of `q_degeneration.md`: the degree-`d` part of `I` consists of `0` and top forms. -/
theorem grPart_le_span (I : Ideal (MvPolynomial (Fin m) F)) (d : ℕ) :
    grPart (I.restrictScalars F) d ≤ Submodule.span F (topForms I) := by
  intro φ hφ
  obtain ⟨f, hfI, hfd, rfl⟩ := mem_grPart.1 hφ
  by_cases hf : f = 0
  · rw [hf, map_zero]; exact zero_mem _
  rcases hfd.lt_or_eq with h | h
  · rw [homogeneousComponent_eq_zero _ _ h]; exact zero_mem _
  · exact Submodule.subset_span ⟨f, hfI, hf, by rw [top, h]⟩

/-- **Setting** of `q_degeneration.md`: `gr(I)` is the set of `0` and of all `f^{top}`,
`f ∈ I ∖ {0}`, together with their sums, i.e. the `F`-span of the top forms. -/
theorem gr_restrictScalars_eq_span (I : Ideal (MvPolynomial (Fin m) F)) :
    (gr I).restrictScalars F = Submodule.span F (topForms I) := by
  refine le_antisymm (fun p hp => ?_) (Submodule.span_le.2 fun x hx => Ideal.subset_span hx)
  rw [← sum_homogeneousComponent p]
  exact Submodule.sum_mem _ fun d _ =>
    grPart_le_span I d (homogeneousComponent_mem_grPart_of_mem_gr hp d)

/-- **Setting** of `q_degeneration.md`: `gr(I)` is a homogeneous ideal (it contains the homogeneous
components of its elements). -/
theorem homogeneousComponent_mem_gr {I : Ideal (MvPolynomial (Fin m) F)}
    {p : MvPolynomial (Fin m) F} (hp : p ∈ gr I) (d : ℕ) : homogeneousComponent d p ∈ gr I := by
  have h := grPart_le_span I d (homogeneousComponent_mem_grPart_of_mem_gr hp d)
  rwa [← gr_restrictScalars_eq_span, Submodule.restrictScalars_mem] at h

/-- **Setting** of `q_degeneration.md`: the degree-`d` part of `gr(I)` is
`{0} ∪ {f^{top} : f ∈ I, deg f = d}`. -/
theorem mem_gr_iff_of_isHomogeneous (I : Ideal (MvPolynomial (Fin m) F)) {d : ℕ}
    {φ : MvPolynomial (Fin m) F} (hφ : φ.IsHomogeneous d) :
    φ ∈ gr I ↔ φ = 0 ∨ ∃ f ∈ I, f.totalDegree = d ∧ top f = φ := by
  constructor
  · intro hp
    have h := homogeneousComponent_mem_grPart_of_mem_gr hp d
    rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule d φ).2 hφ), if_pos rfl] at h
    obtain ⟨f, hfI, hfd, hf⟩ := mem_grPart.1 h
    rcases hfd.lt_or_eq with h' | h'
    · left; rw [← hf, homogeneousComponent_eq_zero _ _ h']
    · right; exact ⟨f, hfI, h', by rw [top, h', hf]⟩
  · rintro (rfl | ⟨f, hfI, -, rfl⟩)
    · exact zero_mem _
    · by_cases hf : f = 0
      · rw [hf, top, map_zero]; exact zero_mem _
      · exact Ideal.subset_span ⟨f, hfI, hf, rfl⟩

/-- **Lemma, part (i)** of `q_degeneration.md`: if `f_1, …, f_s ∈ I` are nonzero, then
`(f_1^{top}, …, f_s^{top}) ⊆ gr(I)`. -/
theorem span_top_le_gr (I : Ideal (MvPolynomial (Fin m) F)) {s : ℕ}
    (f : Fin s → MvPolynomial (Fin m) F) (hfI : ∀ j, f j ∈ I) (hf0 : ∀ j, f j ≠ 0) :
    Ideal.span (Set.range fun j => top (f j)) ≤ gr I := by
  rw [Ideal.span_le]
  rintro _ ⟨j, rfl⟩
  exact Ideal.subset_span ⟨f j, hfI j, hf0 j, rfl⟩

/-- Proof of part (ii) of the Lemma of `q_degeneration.md`: `gr(I)` and `I` have the same
degree-`d` parts. -/
theorem grPart_gr (I : Ideal (MvPolynomial (Fin m) F)) (d : ℕ) :
    grPart ((gr I).restrictScalars F) d = grPart (I.restrictScalars F) d := by
  refine le_antisymm (fun φ hφ => ?_) (fun φ hφ => ?_)
  · obtain ⟨p, hp, -, rfl⟩ := mem_grPart.1 hφ
    exact homogeneousComponent_mem_grPart_of_mem_gr hp d
  · have hmem : φ ∈ gr I := by
      have h := grPart_le_span I d hφ
      rwa [← gr_restrictScalars_eq_span, Submodule.restrictScalars_mem] at h
    obtain ⟨f, -, -, rfl⟩ := mem_grPart.1 hφ
    refine mem_grPart.2 ⟨homogeneousComponent d f, hmem,
      (homogeneousComponent_isHomogeneous d f).totalDegree_le, ?_⟩
    rw [homogeneousComponent_of_mem (homogeneousComponent_mem _ _), if_pos rfl]

/-- Proof of part (ii) of the Lemma of `q_degeneration.md`: a polynomial of degree `≤ d + 1`
with vanishing degree-`(d+1)` component has degree `≤ d`. -/
theorem totalDegree_le_of_homogeneousComponent_eq_zero {f : MvPolynomial (Fin m) F} {d : ℕ}
    (h1 : f.totalDegree ≤ d + 1) (h2 : homogeneousComponent (d + 1) f = 0) :
    f.totalDegree ≤ d := by
  rw [totalDegree, Finset.sup_le_iff]
  intro s hs
  have hle := le_totalDegree hs
  by_contra hlt
  have heq : s.degree = d + 1 := by
    have : s.degree = s.sum fun _ e => e := rfl
    omega
  have := congrArg (coeff s) h2
  rw [coeff_homogeneousComponent, if_pos heq, coeff_zero] at this
  exact (mem_support_iff.1 hs) this

/-- Proof of part (ii) of the Lemma of `q_degeneration.md`:
`dim (K ∩ S_{≤d}) = Σ_{e ≤ d} dim gr(K)_e`. -/
theorem finrank_inf_restrictTotalDegree (K : Submodule F (MvPolynomial (Fin m) F)) (d : ℕ) :
    Module.finrank F (K ⊓ restrictTotalDegree (Fin m) F d : Submodule F _) =
      ∑ e ∈ Finset.range (d + 1), Module.finrank F (grPart K e) := by
  have hrank : ∀ d, Module.finrank F (K ⊓ restrictTotalDegree (Fin m) F d : Submodule F _) =
      Module.finrank F (grPart K d) + Module.finrank F ((K ⊓ restrictTotalDegree (Fin m) F d) ⊓
        LinearMap.ker (homogeneousComponent d) : Submodule F (MvPolynomial (Fin m) F)) := by
    intro d
    have h := LinearMap.finrank_range_add_finrank_ker
      ((homogeneousComponent d).domRestrict (K ⊓ restrictTotalDegree (Fin m) F d))
    rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict] at h
    have e : Submodule.comap (K ⊓ restrictTotalDegree (Fin m) F d).subtype
        (LinearMap.ker (homogeneousComponent d)) =
        Submodule.comap (K ⊓ restrictTotalDegree (Fin m) F d).subtype
          ((K ⊓ restrictTotalDegree (Fin m) F d) ⊓ LinearMap.ker (homogeneousComponent d)) := by
      ext x; simpa using fun _ => (Submodule.mem_inf.1 x.2).1
    rw [e, (Submodule.comapSubtypeEquivOfLe inf_le_left).finrank_eq] at h
    rw [← h]; rfl
  have hker0 : ((K ⊓ restrictTotalDegree (Fin m) F 0) ⊓ LinearMap.ker (homogeneousComponent 0) :
      Submodule F (MvPolynomial (Fin m) F)) = ⊥ := by
    rw [eq_bot_iff]
    intro f hf
    simp only [Submodule.mem_inf, mem_restrictTotalDegree, LinearMap.mem_ker] at hf
    rw [Submodule.mem_bot, ← sum_homogeneousComponent f, Nat.le_zero.1 hf.1.2]
    simpa using hf.2
  have hkerS : ∀ d, ((K ⊓ restrictTotalDegree (Fin m) F (d + 1)) ⊓
      LinearMap.ker (homogeneousComponent (d + 1)) : Submodule F (MvPolynomial (Fin m) F)) =
      K ⊓ restrictTotalDegree (Fin m) F d := by
    intro d
    ext f
    simp only [Submodule.mem_inf, mem_restrictTotalDegree, LinearMap.mem_ker]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨h1, totalDegree_le_of_homogeneousComponent_eq_zero h2 h3⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, by omega⟩, homogeneousComponent_eq_zero _ _ (by omega)⟩
  induction d with
  | zero => rw [hrank, hker0]; simp
  | succ d ih => rw [hrank, hkerS, ih, Finset.sum_range_succ _ (d + 1), add_comm]

/-- Proof of part (ii) of the Lemma of `q_degeneration.md`: an increasing sequence of
finite-dimensional subspaces of bounded dimension whose union is everything is eventually
everything. -/
theorem exists_eq_top_of_finrank_le {Q : Type*} [AddCommGroup Q] [Module F Q]
    (W : ℕ → Submodule F Q) (hW : Monotone W) (hfin : ∀ d, FiniteDimensional F (W d)) (N : ℕ)
    (hN : ∀ d, Module.finrank F (W d) ≤ N) (htop : ⨆ d, W d = ⊤) : ∃ d, W d = ⊤ := by
  have hbdd : BddAbove (Set.range fun d => Module.finrank F (W d)) :=
    ⟨N, by rintro _ ⟨d, rfl⟩; exact hN d⟩
  obtain ⟨D, hD⟩ := Nat.sSup_mem (Set.range_nonempty _) hbdd
  refine ⟨D, ?_⟩
  rw [eq_top_iff, ← htop]
  refine iSup_le fun d => ?_
  haveI := hfin (max D d)
  have heq : W D = W (max D d) := Submodule.eq_of_le_of_finrank_le (hW (le_max_left _ _))
    (by rw [show Module.finrank F (W D) = _ from hD]; exact le_csSup hbdd ⟨_, rfl⟩)
  rw [heq]
  exact hW (le_max_right _ _)

/-- Proof of part (ii) of the Lemma of `q_degeneration.md`: for a linear map `π` out of `S`,
`dim π(S_{≤d}) + dim (ker π ∩ S_{≤d}) = dim S_{≤d}`. -/
theorem finrank_map_add_finrank_ker_inf {Q : Type*} [AddCommGroup Q] [Module F Q]
    (π : MvPolynomial (Fin m) F →ₗ[F] Q) (d : ℕ) :
    Module.finrank F ((restrictTotalDegree (Fin m) F d).map π) +
      Module.finrank F (LinearMap.ker π ⊓ restrictTotalDegree (Fin m) F d : Submodule F _) =
      Module.finrank F (restrictTotalDegree (Fin m) F d) := by
  have h := LinearMap.finrank_range_add_finrank_ker (π.domRestrict (restrictTotalDegree (Fin m) F d))
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict] at h
  have e : Submodule.comap (restrictTotalDegree (Fin m) F d).subtype (LinearMap.ker π) =
      Submodule.comap (restrictTotalDegree (Fin m) F d).subtype
        (LinearMap.ker π ⊓ restrictTotalDegree (Fin m) F d) := by
    ext x; simp
  rw [e, (Submodule.comapSubtypeEquivOfLe inf_le_right).finrank_eq] at h
  exact h

/-- Proof of part (ii) of the Lemma of `q_degeneration.md` ("letting `d → ∞`"): two surjections
from `S` whose kernels meet every `S_{≤d}` in subspaces of the same dimension have targets of the
same dimension, if one of them is finite-dimensional. -/
theorem finrank_eq_of_finrank_ker_inf_eq {Q₁ Q₂ : Type*} [AddCommGroup Q₁] [Module F Q₁]
    [AddCommGroup Q₂] [Module F Q₂] [FiniteDimensional F Q₁]
    (π₁ : MvPolynomial (Fin m) F →ₗ[F] Q₁) (π₂ : MvPolynomial (Fin m) F →ₗ[F] Q₂)
    (h₁ : Function.Surjective π₁) (h₂ : Function.Surjective π₂)
    (h : ∀ d, Module.finrank F (LinearMap.ker π₁ ⊓ restrictTotalDegree (Fin m) F d : Submodule F _)
      = Module.finrank F (LinearMap.ker π₂ ⊓ restrictTotalDegree (Fin m) F d : Submodule F _)) :
    FiniteDimensional F Q₂ ∧ Module.finrank F Q₂ = Module.finrank F Q₁ := by
  have hP : Monotone fun d => restrictTotalDegree (Fin m) F d := fun a b hab p hp => by
    simp only [mem_restrictTotalDegree] at hp ⊢; omega
  have hPtop : ⨆ d, restrictTotalDegree (Fin m) F d = ⊤ := eq_top_iff.2 fun p _ =>
    Submodule.mem_iSup_of_mem p.totalDegree ((mem_restrictTotalDegree _ _ _).2 le_rfl)
  have hW₁ : ⨆ d, (restrictTotalDegree (Fin m) F d).map π₁ = ⊤ := by
    rw [← Submodule.map_iSup, hPtop, Submodule.map_top, LinearMap.range_eq_top.2 h₁]
  have hW₂ : ⨆ d, (restrictTotalDegree (Fin m) F d).map π₂ = ⊤ := by
    rw [← Submodule.map_iSup, hPtop, Submodule.map_top, LinearMap.range_eq_top.2 h₂]
  have hr : ∀ d, Module.finrank F ((restrictTotalDegree (Fin m) F d).map π₂) =
      Module.finrank F ((restrictTotalDegree (Fin m) F d).map π₁) := by
    intro d
    have e₁ := finrank_map_add_finrank_ker_inf π₁ d
    have e₂ := finrank_map_add_finrank_ker_inf π₂ d
    rw [h d] at e₁
    omega
  obtain ⟨D₁, hD₁⟩ := exists_eq_top_of_finrank_le _ (fun a b hab => Submodule.map_mono (hP hab))
    (fun d => inferInstance) (Module.finrank F Q₁) (fun d => Submodule.finrank_le _) hW₁
  obtain ⟨D₂, hD₂⟩ := exists_eq_top_of_finrank_le _ (fun a b hab => Submodule.map_mono (hP hab))
    (fun d => inferInstance) (Module.finrank F Q₁)
    (fun d => (hr d).symm ▸ Submodule.finrank_le _) hW₂
  have hD₁' : (restrictTotalDegree (Fin m) F (max D₁ D₂)).map π₁ = ⊤ :=
    top_le_iff.1 (hD₁ ▸ Submodule.map_mono (hP (le_max_left _ _)))
  have hD₂' : (restrictTotalDegree (Fin m) F (max D₁ D₂)).map π₂ = ⊤ :=
    top_le_iff.1 (hD₂ ▸ Submodule.map_mono (hP (le_max_right _ _)))
  have hfin : FiniteDimensional F (⊤ : Submodule F Q₂) := by rw [← hD₂']; infer_instance
  refine ⟨Module.Finite.equiv Submodule.topEquiv, ?_⟩
  rw [← finrank_top F Q₂, ← finrank_top F Q₁, ← hD₁', ← hD₂', hr]

/-- **Lemma, part (ii)** of `q_degeneration.md`: if `dim_F S/I < ∞`, then
`dim_F S/gr(I) = dim_F S/I`.  The conclusion also records that `S/gr(I)` is finite-dimensional
(so that the equality is one of finite dimensions). -/
theorem finrank_quotient_gr (I : Ideal (MvPolynomial (Fin m) F))
    (hI : FiniteDimensional F (MvPolynomial (Fin m) F ⧸ I)) :
    FiniteDimensional F (MvPolynomial (Fin m) F ⧸ gr I) ∧
      Module.finrank F (MvPolynomial (Fin m) F ⧸ gr I) =
        Module.finrank F (MvPolynomial (Fin m) F ⧸ I) := by
  refine finrank_eq_of_finrank_ker_inf_eq (Ideal.Quotient.mkₐ F I).toLinearMap
    (Ideal.Quotient.mkₐ F (gr I)).toLinearMap (Ideal.Quotient.mkₐ_surjective F I)
    (Ideal.Quotient.mkₐ_surjective F (gr I)) fun d => ?_
  have hk : ∀ J : Ideal (MvPolynomial (Fin m) F),
      LinearMap.ker (Ideal.Quotient.mkₐ F J).toLinearMap = J.restrictScalars F := by
    intro J; ext x
    simp only [LinearMap.mem_ker, AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem, Submodule.restrictScalars_mem]
  rw [hk, hk, finrank_inf_restrictTotalDegree, finrank_inf_restrictTotalDegree]
  exact Finset.sum_congr rfl fun e _ => by rw [grPart_gr]

end Degeneration

end
