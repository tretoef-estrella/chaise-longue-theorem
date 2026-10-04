module

public import RequestProject.Degeneration.Main
public import RequestProject.EvenCount.Main
public import RequestProject.OddEquality.Defs

/-!
# Part C of `q_oddbox_equality.md`: the degeneration bound

This file formalizes **Part C** of `q_oddbox_equality.md` over an arbitrary field `F` and an
arbitrary finite set `T ⊆ F` with `|T| = r = q − 1` and `−T = T` (a more general statement than the
one over `ℚ` with `T = {−h, …, h}`, which is the instance used in Part D).
-/

@[expose] public section

open MvPolynomial

namespace OddEquality

variable {F : Type*} [Field F] {n : ℕ}

/-! ### The ideal `I_P` and the substitution `y_{P(a)} ↦ −y_a` -/

/-- **(C3)** of `q_oddbox_equality.md`: for a perfect matching `P` of `Fin n`, the ideal
`I_P = (y_a + y_b : {a, b} ∈ P) ⊆ F[y_1, …, y_n]`. -/
noncomputable def IPS (P : ColComp.PerfMatch (Fin n)) : Ideal (MvPolynomial (Fin n) F) :=
  Ideal.span (Set.range fun a : Fin n => (X a + X (P.1 a) : MvPolynomial (Fin n) F))

/-- **(C3)** of `q_oddbox_equality.md` (proof): the value of the substitution on `y_i`: `y_i` if
`i < P(i)`, and `−y_{P(i)}` otherwise. -/
noncomputable def sigmaVal (P : ColComp.PerfMatch (Fin n)) (i : Fin n) : MvPolynomial (Fin n) F :=
  if i < P.1 i then X i else -X (P.1 i)

/-- **(C3)** of `q_oddbox_equality.md` (proof): the substitution `σ_P` eliminating the larger
element of every pair, `y_b ↦ −y_a` for `{a < b} ∈ P`. -/
noncomputable def sigmaP (P : ColComp.PerfMatch (Fin n)) :
    MvPolynomial (Fin n) F →ₐ[F] MvPolynomial (Fin n) F :=
  aeval (sigmaVal P)

/-- **(C3)** of `q_oddbox_equality.md` (proof): `p − σ_P(p) ∈ I_P`. -/
theorem sub_sigmaP_mem (P : ColComp.PerfMatch (Fin n)) (p : MvPolynomial (Fin n) F) :
    p - sigmaP P p ∈ IPS P := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [sigmaP]
  | add p p' hp hp' =>
    rw [map_add, add_sub_add_comm]
    exact add_mem hp hp'
  | mul_X p i hp =>
    have hi : (X i : MvPolynomial (Fin n) F) - sigmaP P (X i) ∈ IPS P := by
      simp only [sigmaP, aeval_X, sigmaVal]
      split_ifs
      · rw [sub_self]; exact zero_mem _
      · rw [sub_neg_eq_add]; exact Ideal.subset_span ⟨i, rfl⟩
    have e : p * X i - sigmaP P (p * X i) =
        (p - sigmaP P p) * X i + sigmaP P p * (X i - sigmaP P (X i)) := by
      rw [map_mul]; ring
    rw [e]
    exact add_mem (Ideal.mul_mem_right _ _ hp) (Ideal.mul_mem_left _ _ hi)

/-- **(C3)** of `q_oddbox_equality.md` (proof): `σ_P` sends homogeneous polynomials of degree `d`
to homogeneous polynomials of degree `d`. -/
theorem isHomogeneous_sigmaP (P : ColComp.PerfMatch (Fin n)) {p : MvPolynomial (Fin n) F} {d : ℕ}
    (hp : p.IsHomogeneous d) : (sigmaP P p).IsHomogeneous d := by
  have h := hp.aeval (g := sigmaVal P) (n := 1) (fun i => by
    unfold sigmaVal
    split_ifs
    · exact isHomogeneous_X F i
    · exact (isHomogeneous_X F _).neg)
  simpa using h

/-- **(C3)** of `q_oddbox_equality.md` (proof): `σ_P` commutes with taking homogeneous
components. -/
theorem homogeneousComponent_sigmaP (P : ColComp.PerfMatch (Fin n)) (d : ℕ)
    (p : MvPolynomial (Fin n) F) :
    homogeneousComponent d (sigmaP P p) = sigmaP P (homogeneousComponent d p) := by
  conv_lhs => rw [← sum_homogeneousComponent p]
  rw [map_sum, map_sum]
  rw [Finset.sum_eq_single d]
  · exact homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).2
      (isHomogeneous_sigmaP P (homogeneousComponent_isHomogeneous d p))) |>.trans (if_pos rfl)
  · intro e _ he
    rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).2
      (isHomogeneous_sigmaP P (homogeneousComponent_isHomogeneous e p))), if_neg (Ne.symm he)]
  · intro hd
    rw [Finset.mem_range, not_lt] at hd
    rw [homogeneousComponent_eq_zero d p (by omega), map_zero, map_zero]

/-- **(C3)** of `q_oddbox_equality.md` (proof): the point `M` obtained from `x` by the
substitution: `M_i = x_i` if `i < P(i)`, `M_i = −x_{P(i)}` otherwise. -/
def sigmaPt (P : ColComp.PerfMatch (Fin n)) (x : Fin n → F) (i : Fin n) : F :=
  if i < P.1 i then x i else -x (P.1 i)

/-- **(C3)** of `q_oddbox_equality.md` (proof): `σ_P(p)(x) = p(M)`. -/
theorem eval_sigmaP (P : ColComp.PerfMatch (Fin n)) (x : Fin n → F) (p : MvPolynomial (Fin n) F) :
    eval x (sigmaP P p) = eval (sigmaPt P x) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [sigmaP]
  | add p p' hp hp' => simp only [map_add, hp, hp']
  | mul_X p i hp =>
    simp only [map_mul, hp]
    congr 1
    simp only [sigmaP, aeval_X, sigmaVal, sigmaPt, eval_X]
    split_ifs <;> simp

/-- **(C3)** of `q_oddbox_equality.md` (proof): the point `M` lies in `V(I_P)`:
`M_{P(i)} = −M_i`. -/
theorem sigmaPt_pair (P : ColComp.PerfMatch (Fin n)) (x : Fin n → F) (i : Fin n) :
    sigmaPt P x (P.1 i) = -sigmaPt P x i := by
  have hPP := (P.2 i).2
  have hne := (P.2 i).1
  unfold sigmaPt
  rw [hPP]
  by_cases hi : i < P.1 i
  · rw [if_neg (not_lt.2 hi.le), if_pos hi]
  · have : P.1 i < i := lt_of_le_of_ne (not_lt.1 hi) hne
    rw [if_pos this, if_neg hi, neg_neg]

/-- **(C1)** of `q_oddbox_equality.md` (proof): a polynomial lies in the box ideal `(y_i^{q−1})` iff
each of its monomials has an exponent `≥ q − 1`. -/
theorem mem_powIdeal_iff (q : ℕ) (p : MvPolynomial (Fin n) F) :
    p ∈ Peel.powIdeal F q n ↔ ∀ s ∈ p.support, ∃ i, q - 1 ≤ s i := by
  have e : Peel.powIdeal F q n = Ideal.span ((fun s => monomial s (1 : F)) ''
      Set.range fun i : Fin n => Finsupp.single i (q - 1)) := by
    rw [Peel.powIdeal, ← Set.range_comp]
    congr 1
    ext p
    simp [X_pow_eq_monomial]
  rw [e, mem_ideal_span_monomial_image]
  refine forall₂_congr fun s _ => ?_
  simp only [Set.mem_range, exists_exists_eq_and, Finsupp.single_le_iff]

/-- **(C3)** of `q_oddbox_equality.md` (the inclusion used in (C4)): let `T ⊆ F` be finite with
`|T| = q − 1` and `−T = T`. If `f ∈ F[y]` vanishes on `V(I_P) ∩ T^n` (the points with coordinates
in `T` and `M_{P(i)} = −M_i`), then its top form lies in `I_P + (y_i^{q−1})`.

(The proof uses the substitution `σ_P` and the Combinatorial Nullstellensatz in place of the
computation of the ideal of `V(I_P) ∩ T^n` in the file: `σ_P(f)` vanishes on the grid `T^n`, so
every monomial of its top form has an exponent `≥ |T|`.) -/
theorem top_mem_IPS_sup (q : ℕ) (T : Finset F) (hT : T.card = q - 1)
    (hneg : ∀ u ∈ T, -u ∈ T) (P : ColComp.PerfMatch (Fin n)) (f : MvPolynomial (Fin n) F)
    (hf : ∀ M : Fin n → F, (∀ i, M i ∈ T) → (∀ i, M (P.1 i) = -M i) → eval M f = 0) :
    Degeneration.top f ∈ IPS P ⊔ Peel.powIdeal F q n := by
  set d := f.totalDegree
  set g := sigmaP P f
  have hg0 : ∀ x : Fin n → F, (∀ i, x i ∈ T) → eval x g = 0 := by
    intro x hx
    rw [eval_sigmaP]
    refine hf _ (fun i => ?_) (sigmaPt_pair P x)
    unfold sigmaPt
    split_ifs
    · exact hx i
    · exact hneg _ (hx _)
  have hgd : homogeneousComponent d g = sigmaP P (Degeneration.top f) := by
    rw [homogeneousComponent_sigmaP]; rfl
  have hdeg : ∀ e, d < e → homogeneousComponent e g = 0 := by
    intro e he
    rw [homogeneousComponent_sigmaP, homogeneousComponent_eq_zero e f he, map_zero]
  have hgdeg : g.totalDegree ≤ d := by
    by_contra hlt
    push_neg at hlt
    have h := hdeg _ hlt
    have hne : homogeneousComponent g.totalDegree g ≠ 0 := by
      intro h0
      obtain ⟨s, hs, hsd⟩ := Finset.exists_max_image g.support (fun s => s.degree) (by
        rcases eq_or_ne g 0 with hg | hg
        · rw [hg, totalDegree_zero] at hlt; omega
        · exact support_nonempty.2 hg)
      have : s.degree = g.totalDegree := by
        apply le_antisymm
        · exact le_totalDegree hs
        · rw [totalDegree]; exact Finset.sup_le fun t ht => hsd t ht
      have hc := congrArg (coeff s) h0
      rw [coeff_homogeneousComponent, if_pos this, coeff_zero] at hc
      exact (mem_support_iff.1 hs) hc
    exact hne h
  have hmem : homogeneousComponent d g ∈ Peel.powIdeal F q n := by
    rw [mem_powIdeal_iff]
    intro s hs
    rw [mem_support_iff, coeff_homogeneousComponent] at hs
    split_ifs at hs with hsd
    swap
    · exact absurd rfl hs
    by_contra hcon
    push_neg at hcon
    have htot : g.totalDegree = s.degree := by
      apply le_antisymm (hsd ▸ hgdeg)
      exact le_totalDegree (mem_support_iff.2 hs)
    obtain ⟨x, hx, hne⟩ := combinatorial_nullstellensatz_exists_eval_nonzero g s hs htot
      (fun _ => T) (fun i => by rw [hT]; exact hcon i)
    exact hne (hg0 x hx)
  have key : Degeneration.top f = (Degeneration.top f - sigmaP P (Degeneration.top f)) +
      homogeneousComponent d g := by rw [hgd]; ring
  rw [key]
  exact add_mem (Ideal.mem_sup_left (sub_sigmaP_mem P _)) (Ideal.mem_sup_right hmem)

/-! ### (C1) Finite point sets -/

/-- **(C1)** of `q_oddbox_equality.md`: evaluation `F[y_1, …, y_n] → F^Γ` at a finite set `Γ` of
points of `T^n`. -/
noncomputable def evPts (T : Finset F) (Γ : Finset (Fin n → T)) :
    MvPolynomial (Fin n) F →ₐ[F] (Γ → F) :=
  Pi.algHom F _ fun M => aeval fun j => ((M.1 j : T) : F)

/-- **(C1)** of `q_oddbox_equality.md`: the ideal `I(Γ)` of the polynomials vanishing on `Γ`. -/
noncomputable def IPts (T : Finset F) (Γ : Finset (Fin n → T)) : Ideal (MvPolynomial (Fin n) F) :=
  RingHom.ker (evPts T Γ)

/-- **(C1)** of `q_oddbox_equality.md` (proof): evaluation at `Γ` is onto (Lagrange interpolation,
`Degeneration.lagrangePoly`). -/
theorem evPts_surjective (T : Finset F) (Γ : Finset (Fin n → T)) :
    Function.Surjective (evPts T Γ) := by
  classical
  intro h
  refine ⟨∑ M : Γ, C (h M) * Degeneration.lagrangePoly T M.1, ?_⟩
  funext N
  have hl : ∀ M : Γ, aeval (fun j => ((N.1 j : T) : F)) (Degeneration.lagrangePoly T M.1) =
      if N = M then 1 else 0 := by
    intro M
    change eval _ _ = _
    rw [Degeneration.eval_lagrangePoly]
    by_cases hNM : N = M
    · rw [if_pos hNM, if_pos (congrArg Subtype.val hNM)]
    · rw [if_neg hNM, if_neg (fun e => hNM (Subtype.ext e))]
  simp only [evPts, Pi.algHom_apply, map_sum, map_mul, aeval_C, Algebra.algebraMap_self,
    RingHom.id_apply, hl]
  rw [Finset.sum_eq_single N (fun b _ hb => by rw [if_neg (Ne.symm hb), mul_zero])
    (fun h' => absurd (Finset.mem_univ N) h'), if_pos rfl, mul_one]

/-- **(C1)** of `q_oddbox_equality.md` (the ring of functions): `F[y]/I(Γ) ≅ F^Γ`, so
`dim F[y]/I(Γ) = |Γ|`; and (degeneration, `Degeneration.finrank_quotient_gr`)
`dim F[y]/gr(I(Γ)) = dim F[y]/I(Γ) = |Γ|`. Stated for any finite set `Γ` of points of `T^n`, `T ⊆ F`
finite (the file's form, `F[y]/(g(y_i))` the functions on `T^n`, is the case `Γ = T^n`). -/
theorem C1 (T : Finset F) (Γ : Finset (Fin n → T)) :
    FiniteDimensional F (MvPolynomial (Fin n) F ⧸ IPts T Γ) ∧
      Module.finrank F (MvPolynomial (Fin n) F ⧸ IPts T Γ) = Γ.card ∧
      FiniteDimensional F (MvPolynomial (Fin n) F ⧸ Degeneration.gr (IPts T Γ)) ∧
      Module.finrank F (MvPolynomial (Fin n) F ⧸ Degeneration.gr (IPts T Γ)) = Γ.card := by
  let e := Ideal.quotientKerAlgEquivOfSurjective (evPts_surjective T Γ)
  have hfin : FiniteDimensional F (MvPolynomial (Fin n) F ⧸ IPts T Γ) :=
    Module.Finite.equiv e.symm.toLinearEquiv
  have hrank : Module.finrank F (MvPolynomial (Fin n) F ⧸ IPts T Γ) = Γ.card := by
    rw [IPts, e.toLinearEquiv.finrank_eq, Module.finrank_fintype_fun_eq_card, Fintype.card_coe]
  obtain ⟨hfin', hrank'⟩ := Degeneration.finrank_quotient_gr (IPts T Γ) hfin
  exact ⟨hfin, hrank, hfin', hrank'.trans hrank⟩

/-- **(C4)** of `q_oddbox_equality.md` (proof): `gr` is monotone. -/
theorem gr_mono {I J : Ideal (MvPolynomial (Fin n) F)} (h : I ≤ J) :
    Degeneration.gr I ≤ Degeneration.gr J :=
  Ideal.span_mono fun _ ⟨f, hf, hf0, hp⟩ => ⟨f, h hf, hf0, hp⟩

/-! ### (C2), (C4) The closed tuples -/

/-- **(C4)** of `q_oddbox_equality.md`: let `T ⊆ F` be finite with `|T| = q − 1`, carrying a pointed
structure `S` (`EvenCount.PointedSetting`) whose involution is `u ↦ −u`, and let
`Γ = closedPointed S (2k+2)`. Then `gr(I(Γ)) ⊆ ⋂_P (I_P + (y_i^{q−1}))`. (A point of
`V(I_P) ∩ T^N` is closed by `EvenCount.mem_closedPointed_iff`, so `Γ ⊇ V(I_P) ∩ T^N`; then (C3).) -/
theorem C4 [DecidableEq F] (q : ℕ) (T : Finset F) (hT : T.card = q - 1) {h : ℕ} (S : EvenCount.PointedSetting T h)
    (hS : ∀ u, ((S.neg u : T) : F) = -(u : F)) (k : ℕ) :
    Degeneration.gr (IPts T (EvenCount.closedPointed S (2 * k + 2))) ≤
      ⨅ P : ColComp.PerfMatch (Fin (2 * k + 2)), IPS P ⊔ Peel.powIdeal F q (2 * k + 2) := by
  classical
  have hneg : ∀ u ∈ T, -u ∈ T := fun u hu => by
    have := (S.neg ⟨u, hu⟩).2
    rwa [hS] at this
  rw [Degeneration.gr, Ideal.span_le]
  rintro _ ⟨f, hf, -, rfl⟩
  simp only [SetLike.mem_coe, Submodule.mem_iInf]
  intro P
  refine top_mem_IPS_sup q T hT hneg P f fun M hM hP => ?_
  let g : Fin (2 * k + 2) → T := fun i => ⟨M i, hM i⟩
  have hg : g ∈ EvenCount.closedPointed S (2 * k + 2) := by
    rw [EvenCount.mem_closedPointed_iff]
    refine ⟨⟨P.1, P.2⟩, fun x => Subtype.ext ?_⟩
    rw [hS]
    exact hP x
  have h0 := congrFun ((RingHom.mem_ker).1 hf) ⟨g, hg⟩
  simpa [evPts, g] using h0

/-! ### (C5) -/

/-- **(C5)** of `q_oddbox_equality.md` (the box quotient): for a finite set `Γ` of points with
`gr(I(Γ)) ⊆ ⋂_P (I_P + (y_i^{q−1}))`,
`dim C_n/⋂_P I_P·C_n ≤ dim F[y]/gr(I(Γ)) = |Γ|` (the box ideal lies in every `I_P + (y_i^{q−1})`).
The file states the equality `C_n/⋂_P I_P·C_n = F[y]/⋂_P (I_P + (y_i^{q−1}))`; only the surjection
`F[y]/gr(I(Γ)) → C_n/⋂_P I_P·C_n` is needed and proved. -/
theorem C5 (q : ℕ) (T : Finset F) (Γ : Finset (Fin n → T))
    (hgr : Degeneration.gr (IPts T Γ) ≤
      ⨅ P : ColComp.PerfMatch (Fin n), IPS P ⊔ Peel.powIdeal F q n) :
    FiniteDimensional F (Peel.C F q n ⧸ Kint F q n) ∧
      Module.finrank F (Peel.C F q n ⧸ Kint F q n) ≤ Γ.card := by
  obtain ⟨-, -, hfin, hrank⟩ := C1 T Γ
  have hker : ∀ a ∈ Degeneration.gr (IPts T Γ),
      ((Ideal.Quotient.mkₐ F (Kint F q n)).comp (Ideal.Quotient.mkₐ F (Peel.powIdeal F q n))) a
        = 0 := by
    intro a ha
    have ha' := hgr ha
    simp only [Submodule.mem_iInf] at ha'
    simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem, Kint,
      Submodule.mem_iInf]
    intro P
    have hle : Ideal.map (Ideal.Quotient.mk (Peel.powIdeal F q n)) (IPS P ⊔ Peel.powIdeal F q n) ≤
        IPC F q P := by
      rw [Ideal.map_sup, Ideal.map_quotient_self, sup_bot_eq, IPS, Ideal.map_span, Ideal.span_le]
      rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
      exact Ideal.subset_span ⟨a, by simp [Tight.y]⟩
    exact hle (Ideal.mem_map_of_mem _ (ha' P))
  let φ := Ideal.Quotient.liftₐ (Degeneration.gr (IPts T Γ))
    ((Ideal.Quotient.mkₐ F (Kint F q n)).comp (Ideal.Quotient.mkₐ F (Peel.powIdeal F q n))) hker
  have hφ : Function.Surjective φ := by
    intro z
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective c
    exact ⟨Ideal.Quotient.mk _ p, rfl⟩
  have hrange : LinearMap.range φ.toLinearMap = ⊤ := LinearMap.range_eq_top.2 hφ
  have hfinC : FiniteDimensional F (Peel.C F q n ⧸ Kint F q n) := by
    exact Module.Finite.of_surjective φ.toLinearMap hφ
  refine ⟨hfinC, ?_⟩
  have := LinearMap.finrank_range_le φ.toLinearMap
  rw [hrange, finrank_top, hrank] at this
  exact this

/-! ### (C2) The points over `ℚ` -/

/-- **(C2)** of `q_oddbox_equality.md`: `T = {−h, …, h} ⊆ ℚ`. -/
noncomputable def TQ (h : ℕ) : Finset ℚ := (Finset.Icc (-(h : ℤ)) h).image (Int.cast)

/-- **(C2)** of `q_oddbox_equality.md`: `|T| = 2h + 1 = r`. -/
theorem card_TQ (h : ℕ) : (TQ h).card = 2 * h + 1 := by
  rw [TQ, Finset.card_image_of_injective _ Int.cast_injective, Int.card_Icc]
  omega

/-- **(C2)** of `q_oddbox_equality.md`: `−T = T`. -/
theorem neg_mem_TQ {h : ℕ} {u : ℚ} (hu : u ∈ TQ h) : -u ∈ TQ h := by
  simp only [TQ, Finset.mem_image, Finset.mem_Icc] at hu ⊢
  obtain ⟨z, ⟨h1, h2⟩, rfl⟩ := hu
  exact ⟨-z, ⟨by omega, by omega⟩, by push_cast; ring⟩

/-- **(C2)** of `q_oddbox_equality.md`: `0 ∈ T`. -/
theorem zero_mem_TQ (h : ℕ) : (0 : ℚ) ∈ TQ h := by
  simp only [TQ, Finset.mem_image, Finset.mem_Icc]
  exact ⟨0, ⟨by omega, by omega⟩, by simp⟩

/-- **(C2)** of `q_oddbox_equality.md`: `T = {−h, …, h}` is a pointed set
(`EvenCount.PointedSetting`) with the involution `u ↦ −u` and the fixed point `0`. -/
noncomputable def pointedTQ (h : ℕ) : EvenCount.PointedSetting (TQ h) h where
  neg u := ⟨-(u : ℚ), neg_mem_TQ u.2⟩
  neg_neg u := Subtype.ext (neg_neg _)
  o := ⟨0, zero_mem_TQ h⟩
  neg_o := Subtype.ext neg_zero
  eq_o_of_neg_eq u hu := by
    apply Subtype.ext
    have := congrArg Subtype.val hu
    simp only at this ⊢
    linarith
  card_eq := by rw [Fintype.card_coe, card_TQ]

/-- **(C2)** of `q_oddbox_equality.md`: `|Γ| = Q^e_k(q)`, `Γ = closedPointed T N`
(`EvenCount.card_closedPointed`). -/
theorem card_Gamma (h k : ℕ) :
    (EvenCount.closedPointed (pointedTQ h) (2 * k + 2)).card = EvenCount.QkEven k (2 * h + 2) :=
  EvenCount.card_closedPointed _ k

/-- **Part C** of `q_oddbox_equality.md` (conclusion of (C5) over `ℚ`): for `h ≥ 0` and every `k`,
`dim_ℚ C_ℚ/⋂_P I_P·C_ℚ ≤ Q^e_k(2h + 2)`, with `C_ℚ = Peel.C ℚ (2h+2) (2k+2)`. -/
theorem partC (h k : ℕ) :
    Module.finrank ℚ (Peel.C ℚ (2 * h + 2) (2 * k + 2) ⧸ Kint ℚ (2 * h + 2) (2 * k + 2)) ≤
      EvenCount.QkEven k (2 * h + 2) := by
  rw [← card_Gamma h k]
  refine (C5 (2 * h + 2) (TQ h) _ ?_).2
  exact C4 (2 * h + 2) (TQ h) (by rw [card_TQ]; omega) (pointedTQ h) (fun u => rfl) k

end OddEquality

end
