module

public import RequestProject.Tight.Defs

/-!
# Auxiliary lemmas for `q_P3_identities.md`
-/

@[expose] public section

open MvPolynomial

namespace Tight

open Peel ChainLemma

set_option synthInstance.maxHeartbeats 200000

/-! ### The Vandermonde product `Δ` (Setting and Lemma (ii), (iii), (iv) of `q_P3_identities.md`) -/

/-- Inserting a new index into the Vandermonde product (used for **Lemma (ii), (iii), (iv)** of
`q_P3_identities.md`): for `a ∉ B`,
`Δ(B ∪ {a}) = (−1)^{#{c ∈ B : a < c}} · Π_{c ∈ B} (x_a − x_c) · Δ(B)`. -/
theorem vand_insert {ι R : Type*} [LinearOrder ι] [CommRing R] (x : ι → R) (B : Finset ι)
    (a : ι) (ha : a ∉ B) :
    vand x (insert a B) = (-1) ^ (B.filter (a < ·)).card * (∏ c ∈ B, (x a - x c)) * vand x B := by
  unfold vand
  rw [Finset.prod_insert ha, Finset.filter_insert, if_neg (lt_irrefl a)]
  have h1 : ∀ c ∈ B, ∏ c' ∈ insert a B with c < c', (x c' - x c) =
      (if c < a then x a - x c else 1) * ∏ c' ∈ B with c < c', (x c' - x c) := by
    intro c hc
    rw [Finset.filter_insert]
    split_ifs with h
    · rw [Finset.prod_insert (by simp [ha])]
    · rw [one_mul]
  rw [Finset.prod_congr rfl h1, Finset.prod_mul_distrib]
  have h2 : ∏ c' ∈ B with a < c', (x c' - x a) =
      (-1) ^ (B.filter (a < ·)).card * ∏ c' ∈ B with a < c', (x a - x c') := by
    rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun _ _ => by ring)
  have h3 : ∏ c ∈ B, (if c < a then x a - x c else 1) = ∏ c ∈ B with ¬ a < c, (x a - x c) := by
    rw [Finset.prod_filter]
    refine Finset.prod_congr rfl (fun c hc => ?_)
    have : c ≠ a := fun h => ha (h ▸ hc)
    by_cases h : c < a
    · rw [if_pos h, if_pos (not_lt.2 h.le)]
    · rw [if_neg h, if_neg (by push_neg; exact lt_of_le_of_ne (not_lt.1 h) (Ne.symm this))]
  have h4 := (Finset.prod_filter_mul_prod_filter_not B (fun c => a < c) (fun c => x a - x c)).symm
  rw [h2, h3, h4]
  ring

/-- Ring maps commute with the Vandermonde product (used for **Lemma (ii)** of
`q_P3_identities.md`: the identities are identities of integer polynomials). -/
theorem map_vand {ι R S : Type*} [LinearOrder ι] [CommRing R] [CommRing S] (f : R →+* S)
    (x : ι → R) (B : Finset ι) : f (vand x B) = vand (fun i => f (x i)) B := by
  simp [vand, map_prod, map_sub]

/-- Counting positions (used for **Lemma (ii)** of `q_P3_identities.md`): for `b ∈ S`,
`#{c ∈ S : c < b} + #{c ∈ S ∖ {b} : b < c} + 1 = |S|`. -/
theorem card_filter_lt_add {ι : Type*} [LinearOrder ι] (S : Finset ι) {b : ι} (hb : b ∈ S) :
    (S.filter (· < b)).card + ((S.erase b).filter (b < ·)).card + 1 = S.card := by
  have e1 : (S.erase b).filter (b < ·) = S.filter (b < ·) := by
    ext c; simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨⟨_, h⟩, h'⟩; exact ⟨h, h'⟩
    · rintro ⟨h, h'⟩; exact ⟨⟨ne_of_gt h', h⟩, h'⟩
  have e2 : S.filter (fun c => ¬ b < c) = insert b (S.filter (· < b)) := by
    ext c; simp only [Finset.mem_filter, Finset.mem_insert, not_lt]
    constructor
    · rintro ⟨h, h'⟩; rcases h'.lt_or_eq with h'' | h''
      · exact Or.inr ⟨h, h''⟩
      · exact Or.inl h''
    · rintro (rfl | ⟨h, h'⟩)
      · exact ⟨hb, le_rfl⟩
      · exact ⟨h, h'.le⟩
  have := Finset.card_filter_add_card_filter_not (s := S) (fun c => b < c)
  rw [e2, Finset.card_insert_of_notMem (by simp)] at this
  rw [e1]; omega

/-- The cofactor relation (used for **Lemma (ii)** of `q_P3_identities.md`): for `b = b_c ∈ S`,
`Δ(S) = ε_b · Δ(S ∖ {b}) · Π_{d ∈ S ∖ {b}} (x_b − x_d)` with `ε_{b_c} = (−1)^{r+c}`. -/
theorem vand_eq_eps {ι R : Type*} [LinearOrder ι] [CommRing R] (x : ι → R) (S : Finset ι)
    {b : ι} (hb : b ∈ S) :
    vand x S = (-1) ^ (S.card + ((S.filter (· < b)).card + 1)) * vand x (S.erase b) *
      ∏ c ∈ S.erase b, (x b - x c) := by
  conv_lhs => rw [← Finset.insert_erase hb]
  rw [vand_insert x _ b (by simp)]
  have h := card_filter_lt_add S hb
  have : (-1 : R) ^ (S.card + ((S.filter (· < b)).card + 1)) =
      (-1) ^ ((S.erase b).filter (b < ·)).card := by
    rw [← h]
    rw [show (S.filter (· < b)).card + ((S.erase b).filter (b < ·)).card + 1 +
      ((S.filter (· < b)).card + 1) = ((S.erase b).filter (b < ·)).card +
        2 * ((S.filter (· < b)).card + 1) by ring]
    rw [pow_add, pow_mul]; simp
  rw [this]; ring

/-- **Lemma (ii)** of `q_P3_identities.md` over a field with distinct values `x_b`, via Lagrange
interpolation: for `t ≤ r − 1`,
`Σ_{b ∈ S} ε_b Δ(S ∖ {b}) x_b^t = [t = r − 1] · Δ(S)`. -/
theorem sum_eps_vand_field {ι K : Type*} [LinearOrder ι] [Field K] (x : ι → K) (S : Finset ι)
    (hx : Set.InjOn x S) (t : ℕ) (ht : t + 1 ≤ S.card) :
    ∑ b ∈ S, (-1) ^ (S.card + ((S.filter (· < b)).card + 1)) * vand x (S.erase b) * x b ^ t =
      (if S.card - 1 = t then 1 else 0) * vand x S := by
  have hP : ∀ b ∈ S, ∏ c ∈ S.erase b, (x b - x c) ≠ 0 := by
    intro b hb
    rw [Finset.prod_ne_zero_iff]
    intro c hc
    rw [sub_ne_zero]
    exact fun h => (Finset.mem_erase.1 hc).1 (hx (Finset.mem_of_mem_erase hc) hb h.symm)
  have key : ∀ b ∈ S, (-1) ^ (S.card + ((S.filter (· < b)).card + 1)) * vand x (S.erase b) *
      x b ^ t = vand x S * (Polynomial.eval (x b) (Polynomial.X ^ t) /
        ∏ c ∈ S.erase b, (x b - x c)) := by
    intro b hb
    rw [vand_eq_eps x S hb, Polynomial.eval_pow, Polynomial.eval_X]
    field_simp [hP b hb]
  rw [Finset.sum_congr rfl key, ← Finset.mul_sum, ← Lagrange.coeff_eq_sum hx,
    Polynomial.coeff_X_pow]
  · ring
  · rw [Polynomial.degree_X_pow]; exact_mod_cast ht

/-- **Lemma (ii)** of `q_P3_identities.md` in an arbitrary commutative ring (it is an identity
between polynomials with integer coefficients): for `t ≤ r − 1`,
`Σ_{b ∈ S} ε_b Δ(S ∖ {b}) x_b^t = [t = r − 1] · Δ(S)`. -/
theorem sum_eps_vand {ι R : Type*} [LinearOrder ι] [CommRing R] (x : ι → R) (S : Finset ι)
    (t : ℕ) (ht : t + 1 ≤ S.card) :
    ∑ b ∈ S, (-1) ^ (S.card + ((S.filter (· < b)).card + 1)) * vand x (S.erase b) * x b ^ t =
      (if S.card - 1 = t then 1 else 0) * vand x S := by
  let φ := algebraMap (MvPolynomial ι ℤ) (FractionRing (MvPolynomial ι ℤ))
  have hφ : Function.Injective φ := IsFractionRing.injective _ _
  have univ : ∑ b ∈ S, (-1) ^ (S.card + ((S.filter (· < b)).card + 1)) *
      vand (MvPolynomial.X : ι → MvPolynomial ι ℤ) (S.erase b) * MvPolynomial.X b ^ t =
      (if S.card - 1 = t then 1 else 0) * vand MvPolynomial.X S := by
    apply hφ
    simp only [map_sum, map_mul, map_pow, map_neg, map_one, map_vand, apply_ite φ, map_zero]
    rw [← sum_eps_vand_field (fun i => φ (MvPolynomial.X i)) S _ t ht]
    intro i _ j _ h
    exact MvPolynomial.X_injective (hφ h)
  have := congrArg (MvPolynomial.eval₂Hom (Int.castRingHom R) x) univ
  simp only [map_sum, map_mul, map_pow, map_neg, map_one, map_vand, MvPolynomial.coe_eval₂Hom,
    MvPolynomial.eval₂_X, apply_ite (MvPolynomial.eval₂Hom (Int.castRingHom R) x),
    map_zero] at this
  exact this

/-- **Lemma (iii)** of `q_P3_identities.md` for arbitrary values: if `a < b` for all `b ∈ B`, then
`Δ(B ∪ {a}) = Π_{c ∈ B} (x_c − x_a) · Δ(B)`. -/
theorem vand_insert_of_lt {ι R : Type*} [LinearOrder ι] [CommRing R] (x : ι → R) (B : Finset ι)
    (a : ι) (hlt : ∀ b ∈ B, a < b) :
    vand x (insert a B) = (∏ c ∈ B, (x c - x a)) * vand x B := by
  have ha : a ∉ B := fun h => lt_irrefl a (hlt a h)
  have hf : B.filter (a < ·) = B := Finset.filter_true_of_mem hlt
  rw [vand_insert _ _ _ ha, hf, ← Finset.prod_const, ← Finset.prod_mul_distrib]
  congr 1
  exact Finset.prod_congr rfl (fun _ _ => by ring)

/-- The Vandermonde product of `B` only depends on the values `x_b`, `b ∈ B` (used for
**Lemma (iii)** of `q_P3_identities.md`). -/
theorem vand_congr {ι R : Type*} [LinearOrder ι] [CommRing R] {x x' : ι → R} {B : Finset ι}
    (h : ∀ b ∈ B, x b = x' b) : vand x B = vand x' B := by
  unfold vand
  refine Finset.prod_congr rfl (fun c hc => Finset.prod_congr rfl (fun c' hc' => ?_))
  rw [h c hc, h c' (Finset.mem_filter.1 hc').1]

/-! ### Coefficients in `y_a` (Lemma (i) and (iii) of `q_P3_identities.md`) -/

variable {F : Type*} [Field F] {q m : ℕ}

/-- `y_a` viewed as a polynomial in `y_a` is the variable (used for **Lemma (i), (iii)** of
`q_P3_identities.md`). -/
theorem polyIn_X_self (a : Fin m) : polyIn F a (X a) = Polynomial.X := by
  simp [polyIn]

/-- For `b ≠ a`, `y_b` viewed as a polynomial in `y_a` is a constant (used for
**Lemma (i), (iii)** of `q_P3_identities.md`). -/
theorem polyIn_X_ne {a b : Fin m} (h : b ≠ a) : polyIn F a (X b) = Polynomial.C (X ⟨b, h⟩) := by
  simp [polyIn, Equiv.optionSubtypeNe_symm_of_ne h]

/-- For `j ≤ q − 2`, the coefficient of `y_a^j` maps the ideal `(y_1^{q−1}, …, y_m^{q−1})` into
itself, so it is well defined on `C_m` (convention of **Lemma (iii)** of
`q_P3_identities.md`). -/
theorem pcoeff_mem (a : Fin m) {j : ℕ} (hj : j ≤ q - 2) {p : MvPolynomial (Fin m) F}
    (hp : p ∈ powIdeal F q m) : pcoeff F a j p ∈ powIdeal F q m := by
  obtain ⟨c, rfl⟩ := (Ideal.mem_span_range_iff_exists_fun).1 hp
  simp only [pcoeff, map_sum, Polynomial.finset_sum_coeff]
  refine Ideal.sum_mem _ (fun i _ => ?_)
  by_cases hi : i = a
  · subst hi
    by_cases hq : q - 1 ≤ j
    · have h1 : (X i ^ (q - 1) : MvPolynomial (Fin m) F) ∈ powIdeal F q m :=
        Ideal.subset_span ⟨i, rfl⟩
      rw [show q - 1 = 0 by omega, pow_zero] at h1
      rw [(Ideal.eq_top_iff_one _).2 h1]; trivial
    rw [map_mul, map_pow, polyIn_X_self, Polynomial.coeff_mul_X_pow', if_neg hq, map_zero]
    exact Ideal.zero_mem _
  · rw [map_mul, map_pow, polyIn_X_ne hi, ← map_pow, Polynomial.coeff_mul_C, map_mul, map_pow,
      rename_X]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)

/-- The coefficient of `y_a^j` (`j ≤ q − 2`) of the class of `p` is the class of the coefficient
of `y_a^j` of `p` (convention of **Lemma (iii)** of `q_P3_identities.md`). -/
theorem coeffY_mk (a : Fin m) {j : ℕ} (hj : j ≤ q - 2) (p : MvPolynomial (Fin m) F) :
    coeffY a j (Ideal.Quotient.mk (powIdeal F q m) p) = Ideal.Quotient.mk _ (pcoeff F a j p) := by
  unfold coeffY
  rw [if_pos hj, Ideal.Quotient.eq]
  have h := (Ideal.Quotient.mk_surjective (Ideal.Quotient.mk (powIdeal F q m) p)).choose_spec
  rw [Ideal.Quotient.eq] at h
  have := pcoeff_mem a hj h
  simpa [pcoeff] using this

/-- The coefficients of `0` vanish (**Lemma (iii)** of `q_P3_identities.md`). -/
theorem coeffY_zero (a : Fin m) (j : ℕ) : coeffY a j (0 : C F q m) = 0 := by
  by_cases hj : j ≤ q - 2
  · rw [← map_zero (Ideal.Quotient.mk (powIdeal F q m)), coeffY_mk a hj]
    simp [pcoeff]
  · simp [coeffY, hj]

/-- For `q ≥ 2`, `1 ∉ (y_1^{q−1}, …, y_m^{q−1})` (used for **Lemma (iii)** of
`q_P3_identities.md`). -/
theorem one_notMem_powIdeal (hq : 2 ≤ q) : (1 : MvPolynomial (Fin m) F) ∉ powIdeal F q m := by
  have e : Set.range (fun i : Fin m => (X i ^ (q - 1) : MvPolynomial (Fin m) F)) =
      (fun s => monomial s (1 : F)) '' Set.range (fun i => Finsupp.single i (q - 1)) := by
    ext; simp [X_pow_eq_monomial]
  intro h
  rw [powIdeal, e, mem_ideal_span_monomial_image] at h
  obtain ⟨_, ⟨i, rfl⟩, hle⟩ := h 0 (by simp)
  have := hle i
  simp at this
  omega

/-- For `q ≥ 2`, `C_m` is a nontrivial ring (used for **Lemma (iii)** of `q_P3_identities.md`). -/
theorem nontrivial_C (hq : 2 ≤ q) : Nontrivial (C F q m) :=
  Ideal.Quotient.nontrivial_iff.2 (fun h => one_notMem_powIdeal (F := F) (m := m) hq (h ▸ trivial))

/-- `D(y_a, y_b)` is the class of the integer polynomial `Σ_{i=0}^{q−2} (−1)^i y_a^i y_b^{q−2−i}`
(**Setting** and **Lemma (i)** of `q_P3_identities.md`). -/
theorem D_eq_mk (a b : Fin m) : D F q a b = Ideal.Quotient.mk (powIdeal F q m)
    (∑ i ∈ Finset.range (q - 1), (-1) ^ i * X a ^ i * X b ^ (q - 2 - i)) := by
  simp [D, y, map_sum]

/-- `Δ(B)` is the class of the Vandermonde polynomial of `B` (**Setting** of
`q_P3_identities.md`). -/
theorem Delta_eq_mk (B : Finset (Fin m)) :
    Delta F q B = Ideal.Quotient.mk (powIdeal F q m) (vand X B) := by
  rw [map_vand]; rfl

/-- **Lemma (iii)** of `q_P3_identities.md` at the level of polynomials: if `a < b` for all
`b ∈ B`, the coefficient of `y_a^{|B|}` in `Δ(B ∪ {a})` is `(−1)^{|B|} Δ(B)`, and all
coefficients of higher powers of `y_a` vanish. -/
theorem pcoeff_vand_insert (B : Finset (Fin m)) (a : Fin m) (hlt : ∀ b ∈ B, a < b) :
    pcoeff F a B.card (vand X (insert a B)) = (-1) ^ B.card * vand X B ∧
    ∀ j, B.card < j → pcoeff F a j (vand X (insert a B)) = 0 := by
  have hB : ∀ c ∈ B, c ≠ a := fun c hc h => lt_irrefl a (h ▸ hlt c hc)
  set u : Fin m → MvPolynomial {b // b ≠ a} F := fun c => if h : c ≠ a then X ⟨c, h⟩ else 0
  have hw : polyIn F a (vand X B) = Polynomial.C (vand u B) := by
    rw [← AlgHom.coe_toRingHom, map_vand, map_vand]
    refine vand_congr (fun c hc => ?_)
    simp [u, hB c hc, polyIn_X_ne (hB c hc)]
  have hP : polyIn F a (∏ c ∈ B, (X c - X a)) =
      Polynomial.C ((-1) ^ B.card) * Lagrange.nodal B u := by
    rw [Lagrange.nodal, map_prod, Polynomial.C_pow, Polynomial.C_neg, Polynomial.C_1,
      ← Finset.prod_const, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun c hc => ?_)
    rw [map_sub, polyIn_X_self, polyIn_X_ne (hB c hc)]
    simp [u, hB c hc]
  have hu : rename Subtype.val (vand u B) = vand X B := by
    rw [← AlgHom.coe_toRingHom, map_vand]
    refine vand_congr (fun c hc => ?_)
    simp [u, hB c hc]
  have key : ∀ j, pcoeff F a j (vand X (insert a B)) =
      rename Subtype.val ((-1) ^ B.card * (Lagrange.nodal B u).coeff j) * vand X B := by
    intro j
    rw [pcoeff, vand_insert_of_lt _ _ _ hlt, map_mul, hP, hw, Polynomial.coeff_mul_C,
      Polynomial.coeff_C_mul, map_mul (rename Subtype.val) _ (vand u B), hu]
  refine ⟨?_, fun j hj => ?_⟩
  · rw [key]
    have h1 : (Lagrange.nodal B u).coeff B.card = 1 := by
      have := (Lagrange.nodal_monic (s := B) (v := u)).coeff_natDegree
      rwa [Lagrange.natDegree_nodal] at this
    simp [h1]
  · rw [key, Polynomial.coeff_eq_zero_of_natDegree_lt (by rwa [Lagrange.natDegree_nodal])]
    simp

/-- **Lemma (iii)** of `q_P3_identities.md`: for `a < B` and `|B| ≤ q − 2`, the coefficient of
`y_a^{|B|}` of `Δ(B ∪ {a}) ∈ C_m` is `(−1)^{|B|} Δ(B)`. -/
theorem coeffY_Delta_insert (B : Finset (Fin m)) (a : Fin m) (hlt : ∀ b ∈ B, a < b)
    (hB : B.card ≤ q - 2) :
    coeffY a B.card (Delta F q (insert a B)) = (-1) ^ B.card * Delta F q B := by
  rw [Delta_eq_mk, coeffY_mk a hB, (pcoeff_vand_insert B a hlt).1, map_mul, Delta_eq_mk]
  simp

/-- **Lemma (iii)** of `q_P3_identities.md`: for `a < B`, the coefficients of `y_a^j`, `j > |B|`,
of `Δ(B ∪ {a}) ∈ C_m` vanish. -/
theorem coeffY_Delta_insert_gt (B : Finset (Fin m)) (a : Fin m) (hlt : ∀ b ∈ B, a < b)
    {j : ℕ} (hj : B.card < j) : coeffY a j (Delta F q (insert a B)) = 0 := by
  by_cases hj' : j ≤ q - 2
  · rw [Delta_eq_mk, coeffY_mk a hj', (pcoeff_vand_insert B a hlt).2 j hj, map_zero]
  · simp [coeffY, hj']

/-- For `q ≥ 2` and `|B| ≤ q − 1`, `Δ(B) ≠ 0` in `C_m` (used for the "degree exactly `|B|`"
claim of **Lemma (iii)** of `q_P3_identities.md`). -/
theorem Delta_ne_zero (hq : 2 ≤ q) (B : Finset (Fin m)) (hB : B.card ≤ q - 1) :
    Delta F q B ≠ 0 := by
  haveI := nontrivial_C (F := F) (m := m) hq
  induction B using Finset.induction_on_min with
  | h0 => simp [Delta, vand]
  | step a s hlt ih =>
    have ha : a ∉ s := fun h => lt_irrefl a (hlt a h)
    rw [Finset.card_insert_of_notMem ha] at hB
    intro h0
    have := coeffY_Delta_insert (F := F) (q := q) s a hlt (by omega)
    rw [h0, coeffY_zero, eq_comm, neg_one_pow_mul_eq_zero_iff] at this
    exact ih (by omega) this

/-- **Lemma (iii)** of `q_P3_identities.md`: for `a < B` and `|B| ≤ q − 2`, `Δ(B ∪ {a})` has
degree exactly `|B|` in `y_a`. -/
theorem degY_Delta_insert (hq : 3 ≤ q) (B : Finset (Fin m)) (a : Fin m) (hlt : ∀ b ∈ B, a < b)
    (hB : B.card ≤ q - 2) : degY a (Delta F q (insert a B)) = B.card := by
  have hne : coeffY a B.card (Delta F q (insert a B)) ≠ 0 := by
    rw [coeffY_Delta_insert B a hlt hB, Ne, neg_one_pow_mul_eq_zero_iff]
    exact Delta_ne_zero (by omega) B (by omega)
  classical
  unfold degY
  refine le_antisymm (Finset.max_le (fun j hj => ?_)) (Finset.le_max (a := B.card) ?_)
  · rw [Finset.mem_filter] at hj
    by_contra hlt'
    exact hj.2 (coeffY_Delta_insert_gt B a hlt (WithBot.coe_lt_coe.1 (not_le.1 hlt')))
  · exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hne⟩

/-! ### Relabelling (Lemma (iv) of `q_P3_identities.md`) -/

/-- `x = ±y` (the sign relation of **Lemma (iv)** of `q_P3_identities.md`). -/
def PM {R : Type*} [CommRing R] (x y : R) : Prop := x = y ∨ x = -y

/-- `x = ±x` (**Lemma (iv)** of `q_P3_identities.md`). -/
theorem PM.refl {R : Type*} [CommRing R] (x : R) : PM x x := Or.inl rfl

/-- Symmetry of `x = ±y` (**Lemma (iv)** of `q_P3_identities.md`). -/
theorem PM.symm {R : Type*} [CommRing R] {x y : R} (h : PM x y) : PM y x := by
  rcases h with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (neg_neg _).symm

/-- Transitivity of `x = ±y` (**Lemma (iv)** of `q_P3_identities.md`). -/
theorem PM.trans {R : Type*} [CommRing R] {x y z : R} (h : PM x y) (h' : PM y z) : PM x z := by
  rcases h with rfl | rfl <;> rcases h' with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact Or.inr rfl
  · exact Or.inl (neg_neg _)

/-- Products of `±`-equal elements are `±`-equal (**Lemma (iv)** of `q_P3_identities.md`). -/
theorem PM.mul {R : Type*} [CommRing R] {a b c d : R} (h : PM a b) (h' : PM c d) :
    PM (a * c) (b * d) := by
  rcases h with rfl | rfl <;> rcases h' with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (by ring)
  · exact Or.inr (by ring)
  · exact Or.inl (by ring)

/-- `(−1)^k a = ±a` (**Lemma (iv)** of `q_P3_identities.md`). -/
theorem PM.neg_one_pow_mul {R : Type*} [CommRing R] (k : ℕ) (a : R) : PM ((-1) ^ k * a) a := by
  rcases neg_one_pow_eq_or R k with h | h
  · left; rw [h, one_mul]
  · right; rw [h, neg_one_mul]

/-- Ring maps preserve `x = ±y` (**Lemma (iv)** of `q_P3_identities.md`). -/
theorem PM.map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) {x y : R} (h : PM x y) :
    PM (f x) (f y) := by
  rcases h with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (map_neg f y)

/-- Finite products of `±`-equal factors are `±`-equal (**Lemma (iv)** of
`q_P3_identities.md`). -/
theorem PM.prod {ι R : Type*} [CommRing R] (s : Finset ι) {f g : ι → R}
    (h : ∀ i ∈ s, PM (f i) (g i)) : PM (∏ i ∈ s, f i) (∏ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact PM.refl _
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).mul
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

/-- The relabelling acts on classes of polynomials by renaming the variables (**Lemma (iv)** of
`q_P3_identities.md`). -/
theorem relabel_mk (σ : Equiv.Perm (Fin m)) (p : MvPolynomial (Fin m) F) :
    relabel F q σ (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ (rename σ p) := rfl

/-- The relabelling sends `y_i` to `y_{σ(i)}` (**Lemma (iv)** of `q_P3_identities.md`). -/
theorem relabel_y (σ : Equiv.Perm (Fin m)) (a : Fin m) :
    relabel F q σ (y F q a) = y F q (σ a) := by
  simp [y, relabel_mk]

/-- Relabelling by `σ` undoes relabelling by `σ⁻¹` (**Lemma (iv)** of `q_P3_identities.md`). -/
theorem relabel_relabel_symm (σ : Equiv.Perm (Fin m)) (x : C F q m) :
    relabel F q σ (relabel F q σ.symm x) = x := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [relabel_mk, relabel_mk, rename_rename]
  simp

/-- The relabelling sends `D(y_a, y_b)` to `D(y_{σ a}, y_{σ b})` (**Lemma (iv)** of
`q_P3_identities.md`). -/
theorem relabel_D (σ : Equiv.Perm (Fin m)) (a b : Fin m) :
    relabel F q σ (D F q a b) = D F q (σ a) (σ b) := by
  simp [D, relabel_y, map_sum]

/-- `D(y_b, y_a) = ±D(y_a, y_b)` (the antisymmetry remark of the **Setting** of
`q_P3_identities.md`, used in **Lemma (iv)**); precisely `D(y_b, y_a) = (−1)^q D(y_a, y_b)`. -/
theorem D_swap (a b : Fin m) : PM (D F q b a) (D F q a b) := by
  have key : D F q b a = (-1) ^ q * D F q a b := by
    unfold D
    rw [Finset.mul_sum, ← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [Finset.mem_range] at hi
    rw [show q - 2 - (q - 1 - 1 - i) = i by omega, show q - 1 - 1 - i = q - 2 - i by omega]
    have : (-1 : C F q m) ^ (q - 2 - i) = (-1) ^ q * (-1) ^ i := by
      rw [← pow_add, neg_one_pow_eq_pow_mod_two, neg_one_pow_eq_pow_mod_two (n := q + i)]
      congr 1; omega
    rw [this]; ring
  rw [key]; exact PM.neg_one_pow_mul q _

/-- Relabelling a Vandermonde product: `σ(Δ(B)) = ±Δ(σ(B))` ("reordering the elements of a block
changes `Δ` by the sign of the reordering", proof of **Lemma (iv)** of `q_P3_identities.md`). -/
theorem relabel_Delta (σ : Equiv.Perm (Fin m)) (B : Finset (Fin m)) :
    PM (relabel F q σ (Delta F q B)) (Delta F q (B.map σ.toEmbedding)) := by
  induction B using Finset.induction_on with
  | empty => simp [Delta, vand]; exact PM.refl _
  | insert a s ha ih =>
    rw [Finset.map_insert]
    unfold Delta
    rw [vand_insert _ _ _ ha, vand_insert _ _ _ (by simpa using ha), Finset.prod_map]
    simp only [map_mul, map_pow, map_neg, map_one, map_prod, map_sub, relabel_y]
    refine (((PM.neg_one_pow_mul _ _).mul ih).trans ?_)
    refine PM.symm (PM.trans ?_ (PM.refl _))
    rw [mul_assoc]
    exact PM.neg_one_pow_mul _ _

/-- The factor of a pair `{x, z}` is `±D(y_x, y_z)` (proof of **Lemma (iv)** of
`q_P3_identities.md`). -/
theorem pairD_pair {x z : Fin m} (hxz : x ≠ z) : PM (pairD F q {x, z}) (D F q x z) := by
  have hne : ({x, z} : Finset (Fin m)).Nonempty := ⟨x, by simp⟩
  have hc : 1 < ({x, z} : Finset (Fin m)).card := by rw [Finset.card_pair hxz]; omega
  have hlt := Finset.min'_lt_max'_of_card _ hc
  have h1 := Finset.min'_mem _ hne
  have h2 := Finset.max'_mem _ hne
  unfold pairD
  rw [dif_pos hne]
  simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rw [h1, h2] at hlt ⊢
  · exact absurd hlt (lt_irrefl _)
  · exact PM.refl _
  · exact D_swap x z
  · exact absurd hlt (lt_irrefl _)

/-- `σ` maps pairs to pairs: `σ(D(y_a, y_b)) = ±D(y_{min}, y_{max})` for the pair `σ({a, b})`
(proof of **Lemma (iv)** of `q_P3_identities.md`). -/
theorem relabel_pairD (σ : Equiv.Perm (Fin m)) {e : Finset (Fin m)} (he : e.card = 2) :
    PM (relabel F q σ (pairD F q e)) (pairD F q (e.map σ.toEmbedding)) := by
  obtain ⟨x, z, hxz, rfl⟩ := Finset.card_eq_two.1 he
  have h1 := (pairD_pair (F := F) (q := q) hxz).map (relabel F q σ).toRingHom
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, relabel_D] at h1
  have h2 := pairD_pair (F := F) (q := q) (σ.injective.ne hxz)
  rw [Finset.map_insert, Finset.map_singleton]
  exact h1.trans h2.symm

/-- Images commute with finite unions (used for **Lemma (iv)** of `q_P3_identities.md`). -/
theorem map_sup_eq {ι : Type*} (σ : Fin m ↪ Fin m) (s : Finset ι) (g : ι → Finset (Fin m)) :
    (s.sup g).map σ = s.sup (fun i => (g i).map σ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sup_insert, Finset.sup_insert, Finset.sup_eq_union, Finset.sup_eq_union,
      Finset.map_union, ih]

/-- **Lemma (iv)** of `q_P3_identities.md`: the image `σ(T)` of a tight pattern `T` of `λ` on
`I` under a permutation `σ` (pairs `σ(e)`, blocks `σ(B_c)`) is a tight pattern of `λ` on
`σ(I)`. -/
def TightPattern.relabel (σ : Equiv.Perm (Fin m)) {lam : Partition} {I : Finset (Fin m)}
    (T : TightPattern lam I) : TightPattern lam (I.map σ.toEmbedding) where
  pairs := T.pairs.map ⟨Finset.map σ.toEmbedding, Finset.map_injective _⟩
  blocks c := (T.blocks c).map σ.toEmbedding
  size_le := by rw [Finset.card_map]; exact T.size_le
  even_sub := by rw [Finset.card_map]; exact T.even_sub
  card_pairs := by rw [Finset.card_map, Finset.card_map]; exact T.card_pairs
  card_pair := by
    intro e he
    obtain ⟨e0, he0, rfl⟩ := Finset.mem_map.1 he
    simp only [Function.Embedding.coeFn_mk, Finset.card_map]
    exact T.card_pair e0 he0
  pairs_disjoint := by
    intro e1 he1 e2 he2 hne
    obtain ⟨f1, hf1, rfl⟩ := Finset.mem_map.1 he1
    obtain ⟨f2, hf2, rfl⟩ := Finset.mem_map.1 he2
    have : f1 ≠ f2 := fun h => hne (h ▸ rfl)
    simp only [Function.onFun, id, Function.Embedding.coeFn_mk, Finset.disjoint_map]
    exact T.pairs_disjoint hf1 hf2 this
  card_block := by
    intro c hc
    rw [Finset.card_map]; exact T.card_block c hc
  blocks_disjoint := by
    intro c hc d hd hne
    simp only [Function.onFun, Finset.disjoint_map]
    exact T.blocks_disjoint hc hd hne
  pairs_blocks_disjoint := by
    intro e he c hc
    obtain ⟨f, hf, rfl⟩ := Finset.mem_map.1 he
    simp only [Function.Embedding.coeFn_mk, Finset.disjoint_map]
    exact T.pairs_blocks_disjoint f hf c hc
  cover := by
    have hc := congrArg (Finset.map σ.toEmbedding) T.cover
    rw [Finset.map_union, map_sup_eq, map_sup_eq] at hc
    rw [Finset.sup_map]
    exact hc

/-- **Lemma (iv)** of `q_P3_identities.md`: `σ(G(T)) = ±G(σ(T))`. -/
theorem relabel_prod_PM (σ : Equiv.Perm (Fin m)) {lam : Partition} {I : Finset (Fin m)}
    (T : TightPattern lam I) : PM (relabel F q σ (T.prod F q)) ((T.relabel σ).prod F q) := by
  unfold TightPattern.prod
  rw [map_mul, map_prod, map_prod]
  simp only [TightPattern.relabel, Finset.prod_map, Function.Embedding.coeFn_mk]
  exact (PM.prod _ (fun e he => relabel_pairD σ (T.card_pair e he))).mul
    (PM.prod _ (fun c _ => relabel_Delta σ (T.blocks c)))

/-- Transport of a tight pattern along an equality of index sets (used for **Lemma (iv)** of
`q_P3_identities.md`). -/
theorem exists_pattern_of_eq {lam : Partition} {I J : Finset (Fin m)} (h : J = I)
    (T : TightPattern lam J) : ∃ T0 : TightPattern lam I, T0.prod F q = T.prod F q := by
  subst h; exact ⟨T, rfl⟩

/-! ### Column lengths (Setting of `q_P3_identities.md`) -/

/-- Auxiliary for the **Setting, "Column lengths"** of `q_P3_identities.md`: if all entries of `l`
are `≤ N`, then `Σ_{c=1}^{N} #{x ∈ l : x ≥ c} = Σ_{x ∈ l} x`. -/
theorem sum_filter_length_le (l : List ℕ) (N : ℕ) (hl : ∀ x ∈ l, x ≤ N) :
    ∑ c ∈ Finset.Icc 1 N, (l.filter (fun x => c ≤ x)).length = l.sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.filter_cons, List.sum_cons]
    have hx : x ≤ N := hl x (by simp)
    rw [← ih (fun y hy => hl y (by simp [hy]))]
    have : ∀ c, (if decide (c ≤ x) = true then x :: List.filter (fun x => decide (c ≤ x)) l
        else List.filter (fun x => decide (c ≤ x)) l).length =
        (if c ≤ x then 1 else 0) + (l.filter (fun x => c ≤ x)).length := by
      intro c; split_ifs with h1 h2 h2 <;> simp_all; omega
    simp only [this, Finset.sum_add_distrib, Finset.sum_boole]
    congr 1
    have : (Finset.Icc 1 N).filter (fun c => c ≤ x) = Finset.Icc 1 x := by
      ext c; simp; omega
    simp [this]

end Tight

end
