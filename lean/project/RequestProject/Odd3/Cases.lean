module

public import RequestProject.Odd3.Slice

/-!
# The cases I, II, III of the proof of part (ii) of the Theorem of `q_odd3.md`

Throughout, `m = n + 1`; the indices `{2, …, m}` of `C_m` are the elements `i.succ`
(`i : Fin n`) and `y_1` is `y 0`; the ring `C_{m−1}` in the variables `y_2, …, y_m` is `C_n`
(the variable `y i` of `C_n` is sent to `y i.succ` of `C_{n+1}` by `Peel.incl`); a set of pairs
`P` of `C_n` gives the set of pairs `liftP P` of `{2, …, m}`; and `W_j` is
`Ws (I(n + 1, J)) j`.
-/

@[expose] public section

namespace Odd3

open Peel Tight Polynomial

set_option synthInstance.maxHeartbeats 200000

variable {F : Type*} [Field F]

/-! ### Reading off coefficients of `y_1` -/

/-- Proof of part (ii) of `q_odd3.md`: an element `(y_1^2 − y_1 b + c)·d` of `V` (with `b, c, d`
not containing `y_1`) has degree `2` in `y_1` and `y_1^2`-coefficient `d`, so `d ∈ W_2`. -/
lemma mem_W2_of {n : ℕ} (V : Ideal (C F 4 (n + 1))) (b c d : C F 4 n)
    (h : (y F 4 0 ^ 2 - y F 4 0 * incl F 4 n b + incl F 4 n c) * incl F 4 n d ∈ V) :
    d ∈ Ws V 2 := by
  have := coeff_mem_W V 2 le_rfl ((X ^ 2 - Polynomial.C b * X + Polynomial.C c) * Polynomial.C d)
    (by compute_degree!) (by convert h using 1; simp; ring)
  convert this using 1
  simp

/-- Proof of part (ii) of `q_odd3.md`: an element `(y_1 a + e)·d` of `V` (with `a, e, d` not
containing `y_1`) has degree `≤ 1` in `y_1` and `y_1`-coefficient `a d`, so `a d ∈ W_1`. -/
lemma mem_W1_of {n : ℕ} (V : Ideal (C F 4 (n + 1))) (a e d : C F 4 n)
    (h : (y F 4 0 * incl F 4 n a + incl F 4 n e) * incl F 4 n d ∈ V) :
    a * d ∈ Ws V 1 := by
  have := coeff_mem_W V 1 (by norm_num) ((Polynomial.C a * X + Polynomial.C e) * Polynomial.C d)
    (by compute_degree!) (by convert h using 1; simp; ring)
  convert this using 1
  simp

/-- Proof of part (ii) of `q_odd3.md`: an element `(a − y_1)(b − y_1)·d` of `V` (with `a, b, d`
not containing `y_1`) has `y_1^2`-coefficient `d`, so `d ∈ W_2`. -/
lemma mem_W2_of' {n : ℕ} (V : Ideal (C F 4 (n + 1))) (a b d : C F 4 n)
    (h : (incl F 4 n a - y F 4 0) * (incl F 4 n b - y F 4 0) * incl F 4 n d ∈ V) :
    d ∈ Ws V 2 := by
  have := coeff_mem_W V 2 le_rfl ((Polynomial.C a - X) * (Polynomial.C b - X) * Polynomial.C d)
    (by compute_degree!) (by convert h using 1; simp)
  convert this using 1
  have : (Polynomial.C a - X) * (Polynomial.C b - X) * Polynomial.C d =
    X ^ 2 * Polynomial.C d - X * Polynomial.C ((a + b) * d) + Polynomial.C (a * b * d) := by
    simp only [map_mul, map_add]; ring
  rw [this]
  simp

/-- Proof of part (ii) of `q_odd3.md`: an element `y_1^2·d` of `V` (with `d` not containing
`y_1`) has `y_1^2`-coefficient `d`, so `d ∈ W_2`. -/
lemma mem_W2_of'' {n : ℕ} (V : Ideal (C F 4 (n + 1))) (d : C F 4 n)
    (h : y F 4 0 ^ 2 * incl F 4 n d ∈ V) :
    d ∈ Ws V 2 := by
  have := coeff_mem_W V 2 le_rfl (X ^ 2 * Polynomial.C d)
    (by compute_degree!) (by convert h using 1; rw [eval₂_mul, eval₂_X_pow, eval₂_C])
  simpa using this

/-! ### Generators of `I(m, J)` -/

/-- Proof of part (ii) of `q_odd3.md`: the generators `D_P` (`|P| = (m − J)/2`) of `I(m, J)`,
`J < m`, `J ≡ m`. -/
lemma DP_mem_even {m J : ℕ} (h : J < m) (hp : J % 2 = m % 2) {P : Finset (Finset (Fin m))}
    (hP : IsPairs P) (hc : P.card = (m - J) / 2) : DP F P ∈ I F m J := by
  rw [I_even h hp]; exact Ideal.subset_span ⟨P, hP, hc, rfl⟩

/-- Proof of part (ii) of `q_odd3.md`: the generators `(y_b − y_a)·D_P` of `I(m, J)`,
`1 ≤ J < m`, `J ≢ m`. -/
lemma gen1_mem_odd {m J : ℕ} (h1 : 1 ≤ J) (h : J < m) (hp : J % 2 ≠ m % 2)
    {P : Finset (Finset (Fin m))} (hP : IsPairs P) (hc : P.card = (m - 1 - J) / 2) {a b : Fin m}
    (hab : a ≠ b) (ha : a ∉ supp P) (hb : b ∉ supp P) :
    (y F 4 b - y F 4 a) * DP F P ∈ I F m J := by
  rw [I_odd h1 h hp]; exact Ideal.subset_span (Or.inl ⟨P, a, b, hP, hc, hab, ha, hb, rfl⟩)

/-- Proof of part (ii) of `q_odd3.md`: the generators `D_{P⁺}` of `I(m, J)`, `1 ≤ J < m`,
`J ≢ m`. -/
lemma gen2_mem_odd {m J : ℕ} (h1 : 1 ≤ J) (h : J < m) (hp : J % 2 ≠ m % 2)
    {P : Finset (Finset (Fin m))} (hP : IsPairs P) (hc : P.card = (m + 1 - J) / 2) :
    DP F P ∈ I F m J := by
  rw [I_odd h1 h hp]; exact Ideal.subset_span (Or.inr ⟨P, hP, hc, rfl⟩)

/-- Proof of part (ii) of `q_odd3.md`: the generators `y_c^2·D_P` of `I(m, 0)`, `m` odd. -/
lemma zero1_mem {m : ℕ} (hm : m % 2 = 1) (c : Fin m) {P : Finset (Finset (Fin m))}
    (hP : IsPairs P) (hs : supp P = Finset.univ.erase c) : y F 4 c ^ 2 * DP F P ∈ I F m 0 := by
  rw [I_zero hm]; exact Ideal.subset_span (Or.inl ⟨c, P, hP, hs, rfl⟩)

/-- Proof of part (ii) of `q_odd3.md`: the generators `Δ(y_a, y_b, y_c)·D_{P'}` of `I(m, 0)`,
`m` odd. -/
lemma zero2_mem {m : ℕ} (hm : m % 2 = 1) {a b c : Fin m} (hab : a < b) (hbc : b < c)
    {P : Finset (Finset (Fin m))} (hP : IsPairs P) (hs : supp P = Finset.univ \ {a, b, c}) :
    Delta F 4 {a, b, c} * DP F P ∈ I F m 0 := by
  rw [I_zero hm]; exact Ideal.subset_span (Or.inr ⟨a, b, c, P, hab, hbc, hP, hs, rfl⟩)

/-- Setting of `q_odd3.md`: `Δ(y_a, y_b, y_c) = (y_b − y_a)(y_c − y_a)(y_c − y_b)` for
`a < b < c`. -/
lemma Delta_three {m : ℕ} {a b c : Fin m} (hab : a < b) (hbc : b < c) :
    Delta F 4 {a, b, c} = (y F 4 b - y F 4 a) * (y F 4 c - y F 4 a) * (y F 4 c - y F 4 b) := by
  rw [Delta, vand_insert_of_lt _ _ _ (by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hab
      · exact hab.trans hbc),
    vand_insert_of_lt _ _ _ (by simpa using hbc)]
  rw [Finset.prod_pair (ne_of_lt hbc)]
  simp [vand, Finset.filter_singleton]

/-! ### Adding the pair `{1, b}` -/

/-- Proof of part (ii) of `q_odd3.md` (auxiliary): the set of pairs `P' ∪ {{1, b}}` of
`{1, …, m}`, for a set of pairs `P'` of `{2, …, m}` (given as a set of pairs of `C_{m−1}`) and a
free index `b`. -/
def insP {n : ℕ} (P : Finset (Finset (Fin n))) (b : Fin n) : Finset (Finset (Fin (n + 1))) :=
  insert {0, b.succ} (liftP P)

/-- Proof of part (ii) of `q_odd3.md` (auxiliary): `P' ∪ {{1, b}}` is a set of pairs. -/
lemma isPairs_insP {n : ℕ} {P : Finset (Finset (Fin n))} (hP : IsPairs P) {b : Fin n}
    (hb : b ∉ supp P) : IsPairs (insP P b) :=
  isPairs_insert (isPairs_liftP hP) (Fin.succ_ne_zero b).symm (zero_notMem_supp_liftP P)
    (by rwa [succ_mem_supp_liftP])

/-- Proof of part (ii) of `q_odd3.md` (auxiliary): `|P' ∪ {{1, b}}| = |P'| + 1`. -/
lemma card_insP {n : ℕ} (P : Finset (Finset (Fin n))) (b : Fin n) :
    (insP P b).card = P.card + 1 := by
  rw [insP, card_insert_pair (zero_notMem_supp_liftP P), card_liftP]

/-- Proof of part (ii) of `q_odd3.md` (auxiliary): an index `x ≠ b` free for `P'` stays free for
`P' ∪ {{1, b}}`. -/
lemma succ_notMem_insP {n : ℕ} {P : Finset (Finset (Fin n))} {b x : Fin n} (hx : x ∉ supp P)
    (hxb : x ≠ b) : x.succ ∉ supp (insP P b) := by
  rw [insP, supp_insert, Finset.mem_union, succ_mem_supp_liftP]
  simp only [Finset.mem_insert, Finset.mem_singleton, Fin.succ_ne_zero, false_or, Fin.succ_inj]
  tauto

/-- Proof of part (ii) of `q_odd3.md` (auxiliary): `D_{P' ∪ {{1,b}}} = D(1, b)·D_{P'}`, with
`D(1, b) = y_1^2 − y_1 y_b + y_b^2`. -/
lemma DP_insP {n : ℕ} {P : Finset (Finset (Fin n))} (hP : IsPairs P) {b : Fin n} :
    DP F (insP P b) = (y F 4 0 ^ 2 - y F 4 0 * incl F 4 n (y F 4 b) +
      incl F 4 n (y F 4 b ^ 2)) * incl F 4 n (DP F P) := by
  rw [insP, DP_insert (Fin.succ_ne_zero b).symm (zero_notMem_supp_liftP P), incl_DP hP, map_pow,
    incl_y]

/-! ### Case I: `J ≡ m (mod 2)`, `1 ≤ J ≤ m − 2` -/

/-- **Theorem, part (ii)**, proof, Case I of `q_odd3.md`: `W_2 ⊇ I(m − 1, J + 1)`, using
`D(1, b)·D_{P'} = D_{P' ∪ {{1,b}}}` with `y_1^2`-coefficient `D_{P'}`. -/
lemma caseI_two {n J : ℕ} (h1 : 1 ≤ J) (h2 : J + 2 ≤ n + 1) (hp : J % 2 = (n + 1) % 2) :
    (I F n (J + 1) : Set (C F 4 n)) ⊆ Ws (I F (n + 1) J) 2 := by
  rw [I_even' (by omega) (by omega)]
  refine span_subset_W _ 2 le_rfl _ ?_
  rintro _ ⟨P, hP, hc, rfl⟩
  obtain ⟨b, hb⟩ := exists_notMem (supp P) (by rw [card_supp hP]; omega)
  refine mem_W2_of _ (y F 4 b) (y F 4 b ^ 2) (DP F P) ?_
  rw [← DP_insP hP]
  exact DP_mem_even (by omega) hp (isPairs_insP hP hb) (by rw [card_insP]; omega)

/-- **Theorem, part (ii)**, proof, Case I of `q_odd3.md`: `W_1 ⊇ I(m − 1, J)`, using
`(D(1, b) − D(1, a))·D_{P'}` (with `y_1`-coefficient `−(y_b − y_a)D_{P'}`) and the generators
`D_{P''}`, which do not contain `y_1`. -/
lemma caseI_one {n J : ℕ} (h1 : 1 ≤ J) (h2 : J + 2 ≤ n + 1) (hp : J % 2 = (n + 1) % 2) :
    (I F n J : Set (C F 4 n)) ⊆ Ws (I F (n + 1) J) 1 := by
  rw [I_odd' h1 (by omega) (by omega)]
  refine span_subset_W _ 1 (by norm_num) _ ?_
  rintro _ (⟨P, a, b, hP, hc, hab, ha, hb, rfl⟩ | ⟨P, hP, hc, rfl⟩)
  · have key : (y F 4 a - y F 4 b) * DP F P ∈ Ws (I F (n + 1) J) 1 := by
      refine mem_W1_of _ _ (y F 4 b ^ 2 - y F 4 a ^ 2) _ ?_
      have e : (y F 4 0 * incl F 4 n (y F 4 a - y F 4 b) + incl F 4 n (y F 4 b ^ 2 - y F 4 a ^ 2)) *
          incl F 4 n (DP F P) = DP F (insP P b) - DP F (insP P a) := by
        rw [DP_insP hP, DP_insP hP]; simp only [map_sub, map_pow]; ring
      rw [e]
      exact sub_mem (DP_mem_even (by omega) hp (isPairs_insP hP hb) (by rw [card_insP]; omega))
        (DP_mem_even (by omega) hp (isPairs_insP hP ha) (by rw [card_insP]; omega))
    have := neg_mem key
    convert this using 1; ring
  · exact mem_W_of_incl _ 1 (by norm_num) _ (by
      rw [incl_DP hP]
      exact DP_mem_even (by omega) hp (isPairs_liftP hP) (by rw [card_liftP]; omega))

/-- **Theorem, part (ii)**, proof, Case I of `q_odd3.md`: `W_0 ⊇ I(m − 1, J − 1)`: its
generators `D_{P''}` are generators of `I(m, J)` that do not contain `y_1`. -/
lemma caseI_zero {n J : ℕ} (h1 : 1 ≤ J) (h2 : J + 2 ≤ n + 1) (hp : J % 2 = (n + 1) % 2) :
    (I F n (J - 1) : Set (C F 4 n)) ⊆ Ws (I F (n + 1) J) 0 := by
  rw [I_even' (by omega) (by omega)]
  refine span_subset_W _ 0 (by norm_num) _ ?_
  rintro _ ⟨P, hP, hc, rfl⟩
  exact mem_W_of_incl _ 0 (by norm_num) _ (by
    rw [incl_DP hP]
    exact DP_mem_even (by omega) hp (isPairs_liftP hP) (by rw [card_liftP]; omega))

/-! ### Case II: `J ≢ m (mod 2)`, `1 ≤ J ≤ m − 1` -/

/-- **Theorem, part (ii)**, proof, Case II of `q_odd3.md`: `W_2 ⊇ I(m − 1, J + 1)`, using
`D(1, 2) ∈ I(m, J)` if `J = m − 1`, and otherwise `(y_b − y_a)·D_{P' ∪ {{1,c}}}` and
`D_{P ∪ {{1,b}}}`. -/
lemma caseII_two {n J : ℕ} (h1 : 1 ≤ J) (hJ : J ≤ n) (hp : J % 2 ≠ (n + 1) % 2) :
    (I F n (J + 1) : Set (C F 4 n)) ⊆ Ws (I F (n + 1) J) 2 := by
  rcases eq_or_lt_of_le hJ with rfl | hlt
  · rw [I_top (by omega)]
    refine top_subset_W _ 2 le_rfl ?_
    have b : Fin J := ⟨0, by omega⟩
    have := mem_W2_of (I F (J + 1) J) (y F 4 b) (y F 4 b ^ 2) (DP F (∅ : Finset (Finset (Fin J))))
      (by
        rw [← DP_insP isPairs_empty]
        exact gen2_mem_odd h1 (by omega) hp (isPairs_insP isPairs_empty (by simp [supp]))
          (by rw [card_insP]; simp; omega))
    simpa using this
  · rw [I_odd' (by omega) (by omega) (by omega)]
    refine span_subset_W _ 2 le_rfl _ ?_
    rintro _ (⟨P, a, b, hP, hc, hab, ha, hb, rfl⟩ | ⟨P, hP, hc, rfl⟩)
    · obtain ⟨c, hc'⟩ := exists_notMem (insert a (insert b (supp P))) (by
        have := Finset.card_insert_le a (insert b (supp P))
        have := Finset.card_insert_le b (supp P)
        rw [card_supp hP] at *; omega)
      simp only [Finset.mem_insert, not_or] at hc'
      obtain ⟨hca, hcb, hcP⟩ := hc'
      refine mem_W2_of _ (y F 4 c) (y F 4 c ^ 2) ((y F 4 b - y F 4 a) * DP F P) ?_
      have e : (y F 4 0 ^ 2 - y F 4 0 * incl F 4 n (y F 4 c) + incl F 4 n (y F 4 c ^ 2)) *
          incl F 4 n ((y F 4 b - y F 4 a) * DP F P) =
          (y F 4 b.succ - y F 4 a.succ) * DP F (insP P c) := by
        rw [DP_insP hP, map_mul, map_sub]; simp only [incl_y]; ring
      rw [e]
      exact gen1_mem_odd h1 (by omega) hp (isPairs_insP hP hcP) (by rw [card_insP]; omega)
        (fun h => hab (Fin.succ_inj.1 h)) (succ_notMem_insP ha (Ne.symm hca))
        (succ_notMem_insP hb (Ne.symm hcb))
    · obtain ⟨b, hb⟩ := exists_notMem (supp P) (by rw [card_supp hP]; omega)
      refine mem_W2_of _ (y F 4 b) (y F 4 b ^ 2) (DP F P) ?_
      rw [← DP_insP hP]
      exact gen2_mem_odd h1 (by omega) hp (isPairs_insP hP hb) (by rw [card_insP]; omega)

/-- **Theorem, part (ii)**, proof, Case II of `q_odd3.md`: `W_1 ⊇ I(m − 1, J)`, using
`(y_b − y_1)·D_P ∈ I(m, J)`, of degree `1` in `y_1` with `y_1`-coefficient `−D_P`. -/
lemma caseII_one {n J : ℕ} (h1 : 1 ≤ J) (hJ : J ≤ n) (hp : J % 2 ≠ (n + 1) % 2) :
    (I F n J : Set (C F 4 n)) ⊆ Ws (I F (n + 1) J) 1 := by
  rw [I_even' hJ (by omega)]
  refine span_subset_W _ 1 (by norm_num) _ ?_
  rintro _ ⟨P, hP, hc, rfl⟩
  obtain ⟨b, hb⟩ := exists_notMem (supp P) (by rw [card_supp hP]; omega)
  have key : (-1) * DP F P ∈ Ws (I F (n + 1) J) 1 := by
    refine mem_W1_of _ (-1) (y F 4 b) (DP F P) ?_
    have e : (y F 4 0 * incl F 4 n (-1) + incl F 4 n (y F 4 b)) * incl F 4 n (DP F P) =
        (y F 4 b.succ - y F 4 0) * DP F (liftP P) := by
      rw [incl_DP hP, map_neg, map_one, incl_y]; ring
    rw [e]
    exact gen1_mem_odd h1 (by omega) hp (isPairs_liftP hP) (by rw [card_liftP]; omega)
      (Fin.succ_ne_zero b).symm (zero_notMem_supp_liftP P) (by rwa [succ_mem_supp_liftP])
  have := neg_mem key
  simpa using this

/-- Proof of part (ii) of `q_odd3.md` (auxiliary): a perfect matching of `S` has `2|P| = |S|`. -/
lemma two_mul_card_of_supp {n : ℕ} {P : Finset (Finset (Fin n))} (hP : IsPairs P)
    {S : Finset (Fin n)} (hs : supp P = S) : 2 * P.card = S.card := by
  rw [← card_supp hP, hs]

/-- **Theorem, part (ii)**, proof, Case II (`J = 1`) of `q_odd3.md`: the first polynomial
identity `y_c^2 = y_1·(y_c − y_1) + D(1, c)`, with `D(1, c) = y_1^2 − y_1 y_c + y_c^2` (stated in
an arbitrary commutative ring, which covers `ℤ[y_1, y_c]` and `C_m`). -/
lemma identity_sq {R : Type*} [CommRing R] (y1 yc : R) :
    yc ^ 2 = y1 * (yc - y1) + (y1 ^ 2 - y1 * yc + yc ^ 2) := by ring

/-- **Theorem, part (ii)**, proof, Case II (`J = 1`) of `q_odd3.md`: the second polynomial
identity `Δ(y_a, y_b, y_c) = D(1, a)·(y_c − y_b) − D(1, b)·(y_c − y_a) + D(1, c)·(y_b − y_a)`, with
`Δ(y_a, y_b, y_c) = (y_b − y_a)(y_c − y_a)(y_c − y_b)` and `D(1, x) = y_1^2 − y_1 y_x + y_x^2`
(stated in an arbitrary commutative ring). -/
lemma identity_vand {R : Type*} [CommRing R] (y1 ya yb yc : R) :
    (yb - ya) * (yc - ya) * (yc - yb) =
      (y1 ^ 2 - y1 * ya + ya ^ 2) * (yc - yb) - (y1 ^ 2 - y1 * yb + yb ^ 2) * (yc - ya) +
        (y1 ^ 2 - y1 * yc + yc ^ 2) * (yb - ya) := by ring

/-- **Theorem, part (ii)**, proof, Case II of `q_odd3.md`: `W_0 ⊇ I(m − 1, J − 1)`.  For `J ≥ 2`
the generators of `I(m − 1, J − 1)` are generators of `I(m, J)` not containing `y_1`; for `J = 1`
the two identities `y_c^2 = y_1(y_c − y_1) + D(1, c)` and
`Δ(y_a, y_b, y_c) = D(1, a)(y_c − y_b) − D(1, b)(y_c − y_a) + D(1, c)(y_b − y_a)` are used. -/
lemma caseII_zero {n J : ℕ} (h1 : 1 ≤ J) (hJ : J ≤ n) (hp : J % 2 ≠ (n + 1) % 2) :
    (I F n (J - 1) : Set (C F 4 n)) ⊆ Ws (I F (n + 1) J) 0 := by
  rcases (by omega : J = 1 ∨ 2 ≤ J) with rfl | hJ2
  · have hn : n % 2 = 1 := by omega
    rw [show 1 - 1 = 0 from rfl, I_zero hn]
    refine span_subset_W _ 0 (by norm_num) _ ?_
    rintro _ (⟨c, P, hP, hs, rfl⟩ | ⟨a, b, c, P, hab, hbc, hP, hs, rfl⟩)
    · refine mem_W_of_incl _ 0 (by norm_num) _ ?_
      have hcP : c ∉ supp P := by rw [hs]; simp
      have hcard := two_mul_card_of_supp hP hs
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
        at hcard
      have e : incl F 4 n (y F 4 c ^ 2 * DP F P) =
          y F 4 0 * ((y F 4 c.succ - y F 4 0) * DP F (liftP P)) + DP F (insP P c) := by
        rw [DP_insP hP, map_mul, map_pow, incl_y, incl_DP hP]
        linear_combination DP F (liftP P) * identity_sq (y F 4 0) (y F 4 c.succ)
      rw [e]
      refine add_mem (Ideal.mul_mem_left _ _ ?_) ?_
      · exact gen1_mem_odd le_rfl (by omega) hp (isPairs_liftP hP) (by rw [card_liftP]; omega)
          (Fin.succ_ne_zero c).symm (zero_notMem_supp_liftP P) (by rwa [succ_mem_supp_liftP])
      · exact gen2_mem_odd le_rfl (by omega) hp (isPairs_insP hP hcP) (by rw [card_insP]; omega)
    · refine mem_W_of_incl _ 0 (by norm_num) _ ?_
      have haP : a ∉ supp P := by rw [hs]; simp
      have hbP : b ∉ supp P := by rw [hs]; simp
      have hcP : c ∉ supp P := by rw [hs]; simp
      have hcard := two_mul_card_of_supp hP hs
      have h3 : ({a, b, c} : Finset (Fin n)).card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp [hab.ne, (hab.trans hbc).ne]),
          Finset.card_pair hbc.ne]
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), h3, Finset.card_univ,
        Fintype.card_fin] at hcard
      have hab' := hab.ne
      have hbc' := hbc.ne
      have hac' := (hab.trans hbc).ne
      have e : incl F 4 n (Delta F 4 {a, b, c} * DP F P) =
          (y F 4 c.succ - y F 4 b.succ) * DP F (insP P a) -
          (y F 4 c.succ - y F 4 a.succ) * DP F (insP P b) +
          (y F 4 b.succ - y F 4 a.succ) * DP F (insP P c) := by
        rw [DP_insP hP, DP_insP hP, DP_insP hP, map_mul, Delta_three hab hbc]
        simp only [map_mul, map_sub, map_pow, incl_y]
        linear_combination incl F 4 n (DP F P) *
          identity_vand (y F 4 0) (y F 4 a.succ) (y F 4 b.succ) (y F 4 c.succ)
      rw [e]
      have hcd : (insP P a).card = (n + 1 - 1 - 1) / 2 := by rw [card_insP]; omega
      refine add_mem (sub_mem ?_ ?_) ?_
      · exact gen1_mem_odd le_rfl (by omega) hp (isPairs_insP hP haP) (by rw [card_insP]; omega)
          (fun h => hbc' (Fin.succ_inj.1 h)) (succ_notMem_insP hbP hab'.symm)
          (succ_notMem_insP hcP hac'.symm)
      · exact gen1_mem_odd le_rfl (by omega) hp (isPairs_insP hP hbP) (by rw [card_insP]; omega)
          (fun h => hac' (Fin.succ_inj.1 h)) (succ_notMem_insP haP hab')
          (succ_notMem_insP hcP hbc'.symm)
      · exact gen1_mem_odd le_rfl (by omega) hp (isPairs_insP hP hcP) (by rw [card_insP]; omega)
          (fun h => hab' (Fin.succ_inj.1 h)) (succ_notMem_insP haP hac')
          (succ_notMem_insP hbP hbc')
  · rw [I_odd' (by omega) (by omega) (by omega)]
    refine span_subset_W _ 0 (by norm_num) _ ?_
    rintro _ (⟨P, a, b, hP, hc, hab, ha, hb, rfl⟩ | ⟨P, hP, hc, rfl⟩)
    · refine mem_W_of_incl _ 0 (by norm_num) _ ?_
      rw [map_mul, map_sub, incl_y, incl_y, incl_DP hP]
      exact gen1_mem_odd h1 (by omega) hp (isPairs_liftP hP) (by rw [card_liftP]; omega)
        (fun h => hab (Fin.succ_inj.1 h)) (by rwa [succ_mem_supp_liftP])
        (by rwa [succ_mem_supp_liftP])
    · refine mem_W_of_incl _ 0 (by norm_num) _ ?_
      rw [incl_DP hP]
      exact gen2_mem_odd h1 (by omega) hp (isPairs_liftP hP) (by rw [card_liftP]; omega)

/-! ### Case III: `J = 0` -/

/-- **Theorem, part (ii)**, proof, Case III of `q_odd3.md`: `W_2 ⊇ I(m − 1, 1)` for `J = 0`,
using `D(1, b)·D_{P'}` (`m` even), `y_1^2` (`m = 1`), and `y_1^2·D_{P⁺}` and
`Δ(y_1, y_a, y_b)·D_{P'}` (`m ≥ 3` odd). -/
lemma caseIII (n : ℕ) : (I F n 1 : Set (C F 4 n)) ⊆ Ws (I F (n + 1) 0) 2 := by
  by_cases hn : n % 2 = 1
  · rw [I_even' (by omega) (by omega)]
    refine span_subset_W _ 2 le_rfl _ ?_
    rintro _ ⟨P, hP, hc, rfl⟩
    obtain ⟨b, hb⟩ := exists_notMem (supp P) (by rw [card_supp hP]; omega)
    refine mem_W2_of _ (y F 4 b) (y F 4 b ^ 2) (DP F P) ?_
    rw [← DP_insP hP]
    exact DP_mem_even (by omega) (by omega) (isPairs_insP hP hb) (by rw [card_insP]; omega)
  · rcases Nat.eq_zero_or_pos n with rfl | hpos
    · rw [I_top (by norm_num)]
      refine top_subset_W _ 2 le_rfl ?_
      refine mem_W2_of'' (I F 1 0) 1 ?_
      rw [map_one, mul_one, ← mul_one (y F 4 0 ^ 2), ← DP_empty (F := F)]
      exact zero1_mem (by norm_num) 0 isPairs_empty (by ext x; fin_cases x; simp [supp])
    · rw [I_odd (by norm_num) (by omega) (by omega)]
      refine span_subset_W _ 2 le_rfl _ ?_
      rintro _ (⟨P, a, b, hP, hc, hab, ha, hb, rfl⟩ | ⟨P, hP, hc, rfl⟩)
      · wlog hlt : a < b generalizing a b
        · have := neg_mem (this b a hab.symm hb ha (lt_of_le_of_ne (not_lt.1 hlt) hab.symm))
          convert this using 1; ring
        have hs : supp P = Finset.univ \ {a, b} := by
          refine Finset.eq_of_subset_of_card_le (fun x hx => ?_) ?_
          · simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert,
              Finset.mem_singleton, true_and]
            rintro (rfl | rfl)
            · exact ha hx
            · exact hb hx
          · rw [card_supp hP, Finset.card_sdiff_of_subset (Finset.subset_univ _),
              Finset.card_pair hab, Finset.card_univ, Fintype.card_fin]
            omega
        have hs' : supp (liftP P) = Finset.univ \ {0, a.succ, b.succ} := by
          ext x
          refine Fin.cases ?_ (fun i => ?_) x
          · simp [zero_notMem_supp_liftP]
          · rw [succ_mem_supp_liftP, hs]
            simp [Fin.succ_ne_zero, Fin.succ_inj]
        refine mem_W2_of' _ (y F 4 a) (y F 4 b) ((y F 4 b - y F 4 a) * DP F P) ?_
        have e : (incl F 4 n (y F 4 a) - y F 4 0) * (incl F 4 n (y F 4 b) - y F 4 0) *
            incl F 4 n ((y F 4 b - y F 4 a) * DP F P) =
            Delta F 4 {0, a.succ, b.succ} * DP F (liftP P) := by
          rw [Delta_three (Fin.succ_pos a) (Fin.succ_lt_succ_iff.2 hlt), map_mul, map_sub,
            incl_y, incl_y, incl_DP hP]
          ring
        rw [e]
        exact zero2_mem (by omega) (Fin.succ_pos a) (Fin.succ_lt_succ_iff.2 hlt)
          (isPairs_liftP hP) hs'
      · have hs : supp P = Finset.univ := by
          refine Finset.eq_univ_of_card _ ?_
          rw [card_supp hP, Fintype.card_fin]; omega
        refine mem_W2_of'' _ _ ?_
        rw [incl_DP hP]
        refine zero1_mem (by omega) 0 (isPairs_liftP hP) ?_
        ext x
        refine Fin.cases ?_ (fun i => ?_) x
        · simp [zero_notMem_supp_liftP]
        · rw [succ_mem_supp_liftP, hs]
          simp [Fin.succ_ne_zero]

end Odd3

end
