module

public import RequestProject.ColOne.Sum
public import RequestProject.Peel.Main

/-!
# The Lemma on lowest forms (`q_pow2_leading.md`, (iv))

This file formalizes part **(iv) (Lemma, lowest forms)** of the **Theorem** of
`q_pow2_leading.md`, following the filtration argument of the **Proof** of (iv):

* `ordGE n` is the `F`-subspace of the polynomials all of whose monomials have total degree
  `≥ n`, and `filN n = (B_e)_{≥n}` is its image in `B_e`;
* `piN n = π_n : B_e → B_e` is induced by taking the homogeneous component of degree `n` (it is
  well defined since `(s_i^e)` is a monomial ideal);
* `gr_n(V) = π_n(V ∩ (B_e)_{≥n})`, and the abstract counting lemma `finrank_iSup_gr_le` gives
  `dim Σ_{n<M} gr_n(V) ≤ dim V` (only this inequality of step (a) is needed);
* step (b): every `x̄·ḡ_α` lies in `gr_{δ_α + j}(I)`.

The ring is `Peel.C F q d = F[s]/(s_i^{q−1})`; the statement of (iv) is the case `q = e + 1`.
-/

@[expose] public section

open MvPolynomial

namespace Pow2

set_option synthInstance.maxHeartbeats 200000

section Poly

variable {σ R : Type*} [CommSemiring R]

variable (σ R) in
/-- **Proof of (iv)** of `q_pow2_leading.md`: the subspace of the polynomials all of whose
monomials have total degree `≥ n` (the polynomials whose class lies in `(B_e)_{≥n}`). -/
noncomputable def ordGE (n : ℕ) : Submodule R (MvPolynomial σ R) :=
  restrictSupport R {s | n ≤ Finsupp.degree s}

/-- **Proof of (iv)** of `q_pow2_leading.md`: membership in `ordGE n`. -/
theorem mem_ordGE {n : ℕ} {p : MvPolynomial σ R} :
    p ∈ ordGE σ R n ↔ ∀ s ∈ p.support, n ≤ Finsupp.degree s := by
  rw [ordGE, mem_restrictSupport_iff]
  exact ⟨fun h s hs => h hs, fun h s hs => h s hs⟩

/-- **Proof of (iv)** of `q_pow2_leading.md`: the subspaces `ordGE n` decrease. -/
theorem ordGE_mono {n n' : ℕ} (h : n ≤ n') : ordGE σ R n' ≤ ordGE σ R n := by
  intro p hp
  rw [mem_ordGE] at *
  exact fun s hs => h.trans (hp s hs)

/-- **Proof of (iv)** of `q_pow2_leading.md`: orders add under multiplication. -/
theorem mul_mem_ordGE {a b : ℕ} {p q : MvPolynomial σ R} (hp : p ∈ ordGE σ R a)
    (hq : q ∈ ordGE σ R b) : p * q ∈ ordGE σ R (a + b) := by
  classical
  rw [mem_ordGE] at *
  intro s hs
  obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.1 (support_mul p q hs)
  rw [map_add]
  exact Nat.add_le_add (hp x hx) (hq y hy)

/-- **Proof of (iv)** of `q_pow2_leading.md`: a homogeneous polynomial of degree `n` has order
`≥ n`. -/
theorem IsHomogeneous.mem_ordGE' {n : ℕ} {g : MvPolynomial σ R} (hg : g.IsHomogeneous n) :
    g ∈ ordGE σ R n := by
  rw [mem_ordGE]
  intro s hs
  have := hg (mem_support_iff.1 hs)
  rw [Finsupp.degree_eq_weight_one]
  exact this.ge

/-- **Proof of (iv)** of `q_pow2_leading.md`: a polynomial of order `≥ n + 1` has zero
homogeneous component of degree `n`. -/
theorem homogeneousComponent_eq_zero_of_mem_ordGE {n : ℕ} {p : MvPolynomial σ R}
    (hp : p ∈ ordGE σ R (n + 1)) : homogeneousComponent n p = 0 := by
  ext s
  rw [coeff_homogeneousComponent, coeff_zero]
  split_ifs with h
  · by_contra hc
    have := (mem_ordGE.1 hp) s (mem_support_iff.2 hc)
    omega
  · rfl

/-- **Proof of (iv)** of `q_pow2_leading.md`, step (b): if `g` is homogeneous of degree `δ` and
`f − g` has order `> δ`, then for every homogeneous `x` of degree `j`, `x f` has order
`≥ δ + j` and its component of degree `δ + j` is `x g`. -/
theorem lowest_mul {R : Type*} [CommRing R] {f g x : MvPolynomial σ R} {δ j : ℕ}
    (hg : g.IsHomogeneous δ) (hfg : f - g ∈ ordGE σ R (δ + 1)) (hx : x.IsHomogeneous j) :
    x * f ∈ ordGE σ R (j + δ) ∧ homogeneousComponent (j + δ) (x * f) = x * g := by
  have hf : f = g + (f - g) := by ring
  have h1 : x * (f - g) ∈ ordGE σ R (j + δ + 1) := by
    have := mul_mem_ordGE (IsHomogeneous.mem_ordGE' hx) hfg
    rwa [← add_assoc] at this
  have hxg : (x * g).IsHomogeneous (j + δ) := hx.mul hg
  constructor
  · rw [hf, mul_add]
    exact Submodule.add_mem _ (IsHomogeneous.mem_ordGE' hxg) (ordGE_mono (by omega) h1)
  · rw [hf, mul_add, map_add, homogeneousComponent_eq_zero_of_mem_ordGE h1, add_zero,
      homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).2 hxg), if_pos rfl]

end Poly

/-! ### The abstract counting lemma (step (a)) -/

section Abstract

variable {F : Type*} [Field F] {W : Type*} [AddCommGroup W] [Module F W] [FiniteDimensional F W]

/-- **Proof of (iv)** of `q_pow2_leading.md`, step (a): for a decreasing filtration `(Fil n)` of a
finite-dimensional space and maps `π_n` killing `Fil (n + 1)`, with
`gr_n(V) := π_n(V ∩ Fil n)`, one has `dim Σ_{n<M} gr_n(V) + dim (V ∩ Fil M) ≤ dim (V ∩ Fil 0)`
(the telescoping count `dim gr_n(V) ≤ dim V_{≥n} − dim V_{≥n+1}`). -/
theorem finrank_iSup_gr_add_le (π : ℕ → W →ₗ[F] W) (Fil : ℕ → Submodule F W)
    (hmono : ∀ n, Fil (n + 1) ≤ Fil n) (hπ : ∀ n, ∀ x ∈ Fil (n + 1), π n x = 0)
    (V : Submodule F W) (M : ℕ) :
    Module.finrank F ↥(⨆ n, ⨆ (_ : n < M), (V ⊓ Fil n).map (π n)) +
      Module.finrank F ↥(V ⊓ Fil M) ≤ Module.finrank F ↥(V ⊓ Fil 0) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Nat.iSup_lt_succ]
    have hsup := Submodule.finrank_add_le_finrank_add_finrank
      (⨆ n, ⨆ (_ : n < M), (V ⊓ Fil n).map (π n)) ((V ⊓ Fil M).map (π M))
    -- rank–nullity for `π_M` restricted to `V ∩ Fil M`
    set U := V ⊓ Fil M
    have hrn := LinearMap.finrank_range_add_finrank_ker ((π M).domRestrict U)
    rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict] at hrn
    have hker : Module.finrank F ↥(V ⊓ Fil (M + 1)) ≤
        Module.finrank F ↥(Submodule.comap U.subtype (LinearMap.ker (π M))) := by
      rw [← Submodule.finrank_map_subtype_eq U, Submodule.map_comap_subtype]
      apply Submodule.finrank_mono
      intro x hx
      refine ⟨⟨hx.1, hmono M hx.2⟩, ?_⟩
      exact (LinearMap.mem_ker).2 (hπ M x hx.2)
    omega

/-- **Proof of (iv)** of `q_pow2_leading.md`, step (a) (the inequality `dim in(V) ≤ dim V`):
`dim Σ_{n<M} gr_n(V) ≤ dim V`. -/
theorem finrank_iSup_gr_le (π : ℕ → W →ₗ[F] W) (Fil : ℕ → Submodule F W)
    (hmono : ∀ n, Fil (n + 1) ≤ Fil n) (hπ : ∀ n, ∀ x ∈ Fil (n + 1), π n x = 0)
    (V : Submodule F W) (M : ℕ) :
    Module.finrank F ↥(⨆ n, ⨆ (_ : n < M), (V ⊓ Fil n).map (π n)) ≤ Module.finrank F V := by
  have h := finrank_iSup_gr_add_le π Fil hmono hπ V M
  have h2 : Module.finrank F ↥(V ⊓ Fil 0) ≤ Module.finrank F V :=
    Submodule.finrank_mono inf_le_left
  omega

end Abstract

/-! ### The grading of `B_e` -/

section Grading

variable {F : Type*} [Field F] (q d : ℕ)

/-- **Proof of (iv)** of `q_pow2_leading.md`: the ideal `(s_i^{q−1})` is stable under taking
homogeneous components (it is a monomial ideal). -/
theorem homogeneousComponent_mem_powIdeal (n : ℕ) {p : MvPolynomial (Fin d) F}
    (hp : p ∈ Peel.powIdeal F q d) : homogeneousComponent n p ∈ Peel.powIdeal F q d := by
  rw [ColOne.powIdeal_eq_span_monomial, mem_ideal_span_monomial_image] at *
  intro s hs
  apply hp
  rw [mem_support_iff, coeff_homogeneousComponent] at hs
  split_ifs at hs
  · exact mem_support_iff.2 hs
  · exact absurd rfl hs

/-- **Proof of (iv)** of `q_pow2_leading.md`: a polynomial all of whose monomials have total
degree `> d(q − 2)` lies in `(s_i^{q−1})` (each such monomial has an exponent `≥ q − 1`). -/
theorem mem_powIdeal_of_mem_ordGE {n : ℕ} (hn : d * (q - 2) < n) {p : MvPolynomial (Fin d) F}
    (hp : p ∈ ordGE (Fin d) F n) : p ∈ Peel.powIdeal F q d := by
  rw [ColOne.powIdeal_eq_span_monomial, mem_ideal_span_monomial_image]
  intro s hs
  have hdeg := (mem_ordGE.1 hp) s hs
  by_contra hcon
  push_neg at hcon
  have hlt : ∀ i, s i ≤ q - 2 := by
    intro i
    have := hcon _ ⟨i, rfl⟩
    rw [Finsupp.single_le_iff] at this
    omega
  rw [Finsupp.degree_eq_sum] at hdeg
  have : ∑ i, s i ≤ ∑ _i : Fin d, (q - 2) := Finset.sum_le_sum fun i _ => hlt i
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at this
  omega

/-- **Proof of (iv)** of `q_pow2_leading.md`: `(B_e)_{≥n}`, the image in `Peel.C F q d` of the
polynomials of order `≥ n`. -/
noncomputable def filN (n : ℕ) : Submodule F (Peel.C F q d) :=
  (ordGE (Fin d) F n).map (Ideal.Quotient.mkₐ F (Peel.powIdeal F q d)).toLinearMap

/-- **Proof of (iv)** of `q_pow2_leading.md`: the projection `π_n : B_e → B_e`, induced by the
homogeneous component of degree `n`. -/
noncomputable def piN (n : ℕ) : Peel.C F q d →ₗ[F] Peel.C F q d :=
  ((Peel.powIdeal F q d).restrictScalars F).liftQ
    ((Ideal.Quotient.mkₐ F (Peel.powIdeal F q d)).toLinearMap ∘ₗ homogeneousComponent n) (by
      intro p hp
      rw [LinearMap.mem_ker, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
        Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
      exact homogeneousComponent_mem_powIdeal q d n hp) ∘ₗ
    (Submodule.Quotient.restrictScalarsEquiv F (Peel.powIdeal F q d)).symm.toLinearMap

variable {q d}

/-- **Proof of (iv)** of `q_pow2_leading.md`: `π_n(p̄)` is the class of the homogeneous component
of degree `n` of `p`. -/
@[simp] theorem piN_mk (n : ℕ) (p : MvPolynomial (Fin d) F) :
    piN q d n (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ (homogeneousComponent n p) := rfl

/-- **Proof of (iv)** of `q_pow2_leading.md`: membership of a class in `(B_e)_{≥n}`. -/
theorem mk_mem_filN {n : ℕ} {p : MvPolynomial (Fin d) F} (hp : p ∈ ordGE (Fin d) F n) :
    (Ideal.Quotient.mk (Peel.powIdeal F q d) p) ∈ filN q d n :=
  ⟨p, hp, rfl⟩

/-- **Proof of (iv)** of `q_pow2_leading.md`: `(B_e)_{≥n+1} ⊆ (B_e)_{≥n}`. -/
theorem filN_succ_le (n : ℕ) : filN (F := F) q d (n + 1) ≤ filN q d n :=
  Submodule.map_mono (ordGE_mono (Nat.le_succ n))

/-- **Proof of (iv)** of `q_pow2_leading.md`: `π_n` vanishes on `(B_e)_{≥n+1}`. -/
theorem piN_filN_succ (n : ℕ) (x : Peel.C F q d) (hx : x ∈ filN q d (n + 1)) : piN q d n x = 0 := by
  obtain ⟨p, hp, rfl⟩ := hx
  change piN q d n (Ideal.Quotient.mk _ p) = 0
  rw [piN_mk, homogeneousComponent_eq_zero_of_mem_ordGE hp, map_zero]

/-- **Proof of (iv)** of `q_pow2_leading.md`: `(B_e)_{≥n} = 0` for `n > d(q − 2)`. -/
theorem filN_eq_bot {n : ℕ} (hn : d * (q - 2) < n) : filN (F := F) q d n = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨p, hp, rfl⟩
  rw [Submodule.mem_bot]
  exact Ideal.Quotient.eq_zero_iff_mem.2 (mem_powIdeal_of_mem_ordGE q d hn hp)

/-- **Lemma, lowest forms** (part **(iv)** of `q_pow2_leading.md`), for the ring
`Peel.C F q d = F[s_1, …, s_d]/(s_i^{q−1})` with any `q` (the file's `B_e` is `q = e + 1`). -/
theorem lowest_forms_aux {ι : Type*} (I : Ideal (Peel.C F q d)) (f g : ι → MvPolynomial (Fin d) F)
    (δ : ι → ℕ) (hf : ∀ α, Ideal.Quotient.mk _ (f α) ∈ I)
    (hg : ∀ α, (g α).IsHomogeneous (δ α))
    (hfg : ∀ α, ∀ s ∈ (f α - g α).support, δ α < Finsupp.degree s) :
    Module.finrank F
        ((Ideal.span (Set.range fun α => Ideal.Quotient.mk (Peel.powIdeal F q d) (g α))).restrictScalars
          F) ≤ Module.finrank F (I.restrictScalars F) := by
  set N := d * (q - 2)
  set inI : Submodule F (Peel.C F q d) :=
    ⨆ n, ⨆ (_ : n < N + 1), ((I.restrictScalars F) ⊓ filN q d n).map (piN q d n) with hinI
  have hgr : ∀ n, ((I.restrictScalars F) ⊓ filN q d n).map (piN q d n) ≤ inI := by
    intro n
    by_cases hn : n < N + 1
    · exact le_iSup₂_of_le (f := fun n (_ : n < N + 1) =>
        ((I.restrictScalars F) ⊓ filN q d n).map (piN q d n)) n hn le_rfl
    · rw [filN_eq_bot (by omega), inf_bot_eq, Submodule.map_bot]
      exact bot_le
  -- step (b): every `b · ḡ_α` lies in `in(I)`
  have hb : ∀ α (p : MvPolynomial (Fin d) F),
      Ideal.Quotient.mk (Peel.powIdeal F q d) (p * g α) ∈ inI := by
    intro α p
    have hfg' : f α - g α ∈ ordGE (Fin d) F (δ α + 1) := mem_ordGE.2 fun s hs => hfg α s hs
    rw [← sum_homogeneousComponent p, Finset.sum_mul, map_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    obtain ⟨h1, h2⟩ := lowest_mul (hg α) hfg' (homogeneousComponent_isHomogeneous j p)
    refine hgr (j + δ α) ⟨Ideal.Quotient.mk _ (homogeneousComponent j p * f α), ⟨?_, ?_⟩, ?_⟩
    · change Ideal.Quotient.mk _ (homogeneousComponent j p * f α) ∈ I
      rw [map_mul]
      exact Ideal.mul_mem_left _ _ (hf α)
    · exact mk_mem_filN h1
    · rw [piN_mk, h2]
  -- the ideal `T = {x | ∀ b, b x ∈ in(I)}` contains the `ḡ_α`
  let T : Ideal (Peel.C F q d) :=
    { carrier := {x | ∀ b, b * x ∈ inI}
      add_mem' := fun {x y} hx hy b => by rw [mul_add]; exact inI.add_mem (hx b) (hy b)
      zero_mem' := fun b => by rw [mul_zero]; exact inI.zero_mem
      smul_mem' := fun c x hx b => by rw [smul_eq_mul, ← mul_assoc]; exact hx _ }
  have hspan : Ideal.span (Set.range fun α => Ideal.Quotient.mk (Peel.powIdeal F q d) (g α)) ≤ T := by
    rw [Ideal.span_le]
    rintro _ ⟨α, rfl⟩ b
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [← map_mul]
    exact hb α p
  have hle : (Ideal.span (Set.range fun α =>
      Ideal.Quotient.mk (Peel.powIdeal F q d) (g α))).restrictScalars F ≤ inI := by
    intro x hx
    have := hspan hx 1
    rwa [one_mul] at this
  exact (Submodule.finrank_mono hle).trans
    (finrank_iSup_gr_le (fun n => piN q d n) (fun n => filN q d n) filN_succ_le piN_filN_succ
      (I.restrictScalars F) (N + 1))

/-- **(iv) (Lemma, lowest forms)** of `q_pow2_leading.md`: let `F` be any field, `e ≥ 0` (the
file assumes `e ≥ 1`, which is not needed), `d ≥ 0`,
`B_e := F[s_1, …, s_d]/(s_1^e, …, s_d^e) = Peel.C F (e + 1) d`, and `I` an ideal of `B_e`. Let
`(f_α)`, `(g_α)` be families of polynomials and `(δ_α)` natural numbers such that, for every `α`,
the class of `f_α` lies in `I`, `g_α` is homogeneous of degree `δ_α`, and every monomial of
`f_α − g_α` has total degree greater than `δ_α`. Then `dim_F (ḡ_α : α)·B_e ≤ dim_F I`. -/
theorem lowest_forms {ι : Type*} (e : ℕ) (I : Ideal (Peel.C F (e + 1) d))
    (f g : ι → MvPolynomial (Fin d) F) (δ : ι → ℕ)
    (hf : ∀ α, Ideal.Quotient.mk _ (f α) ∈ I)
    (hg : ∀ α, (g α).IsHomogeneous (δ α))
    (hfg : ∀ α, ∀ s ∈ (f α - g α).support, δ α < Finsupp.degree s) :
    Module.finrank F
        ((Ideal.span (Set.range fun α =>
          Ideal.Quotient.mk (Peel.powIdeal F (e + 1) d) (g α))).restrictScalars F) ≤
      Module.finrank F (I.restrictScalars F) :=
  lowest_forms_aux I f g δ hf hg hfg

end Grading

end Pow2

end
