module

public import RequestProject.Support.Defs

/-!
# Lemma (evaluation) of `q_support.md`

Formalization of the **Lemma (evaluation)** of `q_support.md`, parts (i), (ii) and (iii), for
the polynomials `DP` (`D(y_a, y_b)`), `DeltaP` (`Δ(B)`) and `prodP` (the product `G` of a tight
pattern) of `RequestProject/Support/Defs.lean`, evaluated at points `M ∈ T^m` (`y_i ↦ M_i`,
i.e. `MvPolynomial.eval (fun j => (M j : F))`).
-/

@[expose] public section

open MvPolynomial

namespace Support

open ChainLemma Tight

set_option synthInstance.maxHeartbeats 200000

variable {F : Type*} [Field F]

/-- **Proof** of the Lemma (evaluation) of `q_support.md`: the value `D(u, v)` of the divided
difference at a point with `y_a ↦ u`, `y_b ↦ v`. -/
theorem eval_DP (q : ℕ) {m : ℕ} (x : Fin m → F) (a b : Fin m) :
    eval x (DP F q a b) = ∑ i ∈ Finset.range (q - 1), (-1) ^ i * x a ^ i * x b ^ (q - 2 - i) := by
  simp [DP, map_sum]

/-- **Proof** of the Lemma (evaluation), part (i), of `q_support.md`:
`(a + b)·D(a, b) = b^{q−1} − a^{q−1} = 1 − 1 = 0` for `a, b ∈ T`, so `D(a, b) = 0` if `b ≠ −a`. -/
theorem dsum_eq_zero {q : ℕ} (hodd : Odd q) {T : Finset F}
    (hprod : ∏ u ∈ T, (Polynomial.X - Polynomial.C u) = Polynomial.X ^ (q - 1) - 1)
    {u v : F} (hu : u ∈ T) (hv : v ∈ T) (huv : v ≠ -u) :
    ∑ i ∈ Finset.range (q - 1), (-1) ^ i * u ^ i * v ^ (q - 2 - i) = 0 := by
  have hg := geom_sum₂_mul (-u) v (q - 1)
  have hu1 := pow_eq_one hprod hu
  have hv1 := pow_eq_one hprod hv
  have hneg : (-u) ^ (q - 1) = 1 := by
    obtain ⟨k, rfl⟩ := hodd
    rw [show 2 * k + 1 - 1 = 2 * k by omega] at hu1 ⊢
    rw [pow_mul, neg_sq, ← pow_mul, hu1]
  rw [hneg, hv1, sub_self] at hg
  have hne : -u - v ≠ 0 := by
    intro h; apply huv; linear_combination -h
  have h2 := (mul_eq_zero.1 hg).resolve_right hne
  rw [← h2]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [neg_pow, show q - 1 - 1 - i = q - 2 - i by omega]
  ring

/-- **Proof** of the Lemma (evaluation), part (i), of `q_support.md`: every term of `D(a, −a)` is
`(−1)^i a^i (−a)^{q−2−i} = −a^{q−2}` (as `q − 2` is odd), and there are `q − 1` terms. -/
theorem dsum_neg {q : ℕ} (hq : 3 ≤ q) (hodd : Odd q) (u : F) :
    ∑ i ∈ Finset.range (q - 1), (-1) ^ i * u ^ i * (-u) ^ (q - 2 - i) =
      -(((q - 1 : ℕ) : F) * u ^ (q - 2)) := by
  have hterm : ∀ i ∈ Finset.range (q - 1),
      (-1 : F) ^ i * u ^ i * (-u) ^ (q - 2 - i) = -(u ^ (q - 2)) := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [neg_pow u, show (-1 : F) ^ i * u ^ i * ((-1) ^ (q - 2 - i) * u ^ (q - 2 - i)) =
      (-1) ^ (i + (q - 2 - i)) * u ^ (i + (q - 2 - i)) by ring,
      show i + (q - 2 - i) = q - 2 by omega]
    obtain ⟨k, rfl⟩ := hodd
    rw [show 2 * k + 1 - 2 = 2 * (k - 1) + 1 by omega, pow_succ, pow_mul]
    simp
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring

/-- **Lemma (evaluation), part (i)**, of `q_support.md`, first half: for a point `M ∈ T^m` and
indices `a, b` with values `M_a, M_b ∈ T`, `D(M_a, M_b) = 0` if `M_b ≠ −M_a`. -/
theorem eval_DP_eq_zero {q : ℕ} (hodd : Odd q) {T : Finset F}
    (hprod : ∏ u ∈ T, (Polynomial.X - Polynomial.C u) = Polynomial.X ^ (q - 1) - 1)
    {m : ℕ} (M : Fin m → T) (a b : Fin m) (hab : (M b : F) ≠ -(M a : F)) :
    eval (fun j => (M j : F)) (DP F q a b) = 0 := by
  rw [eval_DP]
  exact dsum_eq_zero hodd hprod (M a).2 (M b).2 hab

/-- **Lemma (evaluation), part (i)**, of `q_support.md`, second half: for a point `M ∈ T^m` and
indices `a, b` with `M_b = −M_a`, `D(M_a, −M_a) = −(q − 1) M_a^{q−2} ≠ 0`. -/
theorem eval_DP_of_eq_neg {q : ℕ} (hq : 3 ≤ q) (hodd : Odd q) {T : Finset F}
    (hprod : ∏ u ∈ T, (Polynomial.X - Polynomial.C u) = Polynomial.X ^ (q - 1) - 1)
    {m : ℕ} (M : Fin m → T) (a b : Fin m) (hab : (M b : F) = -(M a : F)) :
    eval (fun j => (M j : F)) (DP F q a b) = -(((q - 1 : ℕ) : F) * (M a : F) ^ (q - 2)) ∧
      eval (fun j => (M j : F)) (DP F q a b) ≠ 0 := by
  have h : eval (fun j => (M j : F)) (DP F q a b) = -(((q - 1 : ℕ) : F) * (M a : F) ^ (q - 2)) := by
    rw [eval_DP]; simp only [hab]; exact dsum_neg hq hodd _
  refine ⟨h, ?_⟩
  rw [h, neg_ne_zero]
  exact mul_ne_zero (natCast_sub_one_ne_zero hprod)
    (pow_ne_zero _ (ne_zero_of_mem hq hprod (M a).2))

/-- **Proof** of the Lemma (evaluation), part (ii), of `q_support.md`:
`Δ(B)(x) = Π_{c<c'} (x_{b_{c'}} − x_{b_c})`. -/
theorem eval_DeltaP {m : ℕ} (x : Fin m → F) (B : Finset (Fin m)) :
    eval x (DeltaP F B) = vand x B := by
  simp [DeltaP, vand, map_prod]

/-- **Lemma (evaluation), part (ii)**, of `q_support.md`: for a finite set of indices `B`,
`Δ(B)(M) ≠ 0` iff the values `M_b`, `b ∈ B`, are pairwise distinct.  (This holds at every point
`M ∈ F^m`, in particular at every point of `T^m`.) -/
theorem eval_DeltaP_ne_zero_iff {m : ℕ} (M : Fin m → F) (B : Finset (Fin m)) :
    eval M (DeltaP F B) ≠ 0 ↔ Set.InjOn M B := by
  rw [eval_DeltaP, vand, Finset.prod_ne_zero_iff]
  simp only [Finset.prod_ne_zero_iff, Finset.mem_filter, sub_ne_zero]
  constructor
  · intro h c hc c' hc' hcc'
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact h c hc c' ⟨hc', hlt⟩ hcc'.symm
    · exact h c' hc' c ⟨hc, hlt⟩ hcc'
  · rintro h c hc c' ⟨hc', hlt⟩ heq
    exact (ne_of_gt hlt) (h hc' hc heq)

/-- **Lemma (evaluation)** of `q_support.md`: the value of the factor of a pair `e = {a < b}` at
`M ∈ T^m` is non-zero iff `M_b = −M_a`. -/
theorem eval_pairDP_ne_zero_iff {q : ℕ} (hq : 3 ≤ q) (hodd : Odd q) {T : Finset F}
    (hprod : ∏ u ∈ T, (Polynomial.X - Polynomial.C u) = Polynomial.X ^ (q - 1) - 1)
    {m : ℕ} (M : Fin m → T) (e : Finset (Fin m)) (he : e.card = 2) :
    eval (fun j => (M j : F)) (pairDP F q e) ≠ 0 ↔
      ∀ a ∈ e, ∀ b ∈ e, a ≠ b → (M b : F) = -(M a : F) := by
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 he
  have hne : ({a, b} : Finset (Fin m)).Nonempty := ⟨a, by simp⟩
  have hsymm : ((M b : F) = -(M a : F)) ↔ ((M a : F) = -(M b : F)) := by
    constructor <;> intro h <;> rw [h, neg_neg]
  have hall : (∀ x ∈ ({a, b} : Finset (Fin m)), ∀ y ∈ ({a, b} : Finset (Fin m)), x ≠ y →
      (M y : F) = -(M x : F)) ↔ (M b : F) = -(M a : F) := by
    constructor
    · intro h; exact h a (by simp) b (by simp) hab
    · intro h x hx y hy hxy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact absurd rfl hxy
      · exact h
      · exact hsymm.1 h
      · exact absurd rfl hxy
  rw [hall]
  set lo := ({a, b} : Finset (Fin m)).min' hne
  set hi := ({a, b} : Finset (Fin m)).max' hne
  have hlohi : (lo = a ∧ hi = b) ∨ (lo = b ∧ hi = a) := by
    rcases lt_or_gt_of_ne hab with h | h
    · left
      refine ⟨le_antisymm (Finset.min'_le _ _ (by simp)) ?_,
        le_antisymm (Finset.max'_le _ _ _ ?_) (Finset.le_max' _ _ (by simp))⟩
      · exact Finset.le_min' _ _ _ (by simp [h.le])
      · simp [h.le]
    · right
      refine ⟨le_antisymm (Finset.min'_le _ _ (by simp)) ?_,
        le_antisymm (Finset.max'_le _ _ _ ?_) (Finset.le_max' _ _ (by simp))⟩
      · exact Finset.le_min' _ _ _ (by simp [h.le])
      · simp [h.le]
  have key : eval (fun j => (M j : F)) (pairDP F q {a, b}) ≠ 0 ↔ (M hi : F) = -(M lo : F) := by
    unfold pairDP
    rw [dif_pos hne]
    constructor
    · intro h
      by_contra h'
      exact h (eval_DP_eq_zero hodd hprod M lo hi h')
    · intro h
      exact (eval_DP_of_eq_neg hq hodd hprod M lo hi h).2
  rw [key]
  rcases hlohi with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2]; exact hsymm.symm

/-- **Lemma (evaluation), part (iii)**, of `q_support.md`: the product `G` of a tight pattern
`(P, B_1, …, B_{λ_1})` of `λ` satisfies `G(M) ≠ 0` at `M ∈ T^m` iff `M_b = −M_a` for every pair
`{a, b} ∈ P` and every block `B_c` carries pairwise distinct values. -/
theorem eval_prodP_ne_zero_iff {q : ℕ} (hq : 3 ≤ q) (hodd : Odd q) {T : Finset F}
    (hprod : ∏ u ∈ T, (Polynomial.X - Polynomial.C u) = Polynomial.X ^ (q - 1) - 1)
    {m : ℕ} {lam : Partition} {I : Finset (Fin m)} (Tp : TightPattern lam I) (M : Fin m → T) :
    eval (fun j => (M j : F)) (prodP F q Tp) ≠ 0 ↔
      (∀ e ∈ Tp.pairs, ∀ a ∈ e, ∀ b ∈ e, a ≠ b → (M b : F) = -(M a : F)) ∧
      ∀ c ∈ Finset.Icc 1 (lam.row 1), Set.InjOn (fun j => (M j : F)) (Tp.blocks c) := by
  rw [prodP, map_mul, mul_ne_zero_iff, map_prod, map_prod, Finset.prod_ne_zero_iff,
    Finset.prod_ne_zero_iff]
  refine and_congr (forall₂_congr fun e he => ?_) (forall₂_congr fun c _ => ?_)
  · exact eval_pairDP_ne_zero_iff hq hodd hprod M e (Tp.card_pair e he)
  · exact eval_DeltaP_ne_zero_iff _ _

end Support

end
