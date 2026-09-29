module

public import RequestProject.Ballot.Alg

/-!
# Step (ii) of `q3_ballot_lower_bound.md`: the elements `y_T · D_J`

Given a set `U` of variables together with a partner `c` of `0` and a pairing `π` of the other
variables whose pairs have their smaller element in `U`, we build the matching `J`, the set `T`
and the polynomial lift of `y_T · D_J`, and compute its minimal-weight monomial `y_U`.
-/

@[expose] public section

open MvPolynomial Finset

namespace BallotBound

variable {F : Type*} [Field F] {k : ℕ}

/-- The monomial exponent `y_U` of a set `U` of variables. -/
noncomputable def indU (U : Finset (Fin (2 * k + 1))) : Fin (2 * k + 1) →₀ ℕ :=
  ∑ x ∈ U, Finsupp.single x 1

/-- Coefficients of the monomial `y_U` (**Setting** of `q3_ballot_lower_bound.md`). -/
lemma indU_apply (U : Finset (Fin (2 * k + 1))) (y : Fin (2 * k + 1)) :
    indU U y = if y ∈ U then 1 else 0 := by
  simp [indU, Finsupp.finset_sum_apply, Finsupp.single_apply]

/-- The weight used to order monomials: variable `y_{j+1} = X j` gets weight `j`. -/
def wt (k : ℕ) : Fin (2 * k + 1) → ℕ := fun j => j.val

/-- The data produced by the greedy matching in step (ii) of `q3_ballot_lower_bound.md`:
the partner `c` of `0` and a pairing `π` (a fixed-point-free involution away from `c`)
of the remaining variables, whose pairs have their smaller element in `U`. -/
structure PairData (k : ℕ) (U : Finset (Fin (2 * k + 1))) where
  c : Fin (2 * k + 1)
  π : Fin (2 * k + 1) → Fin (2 * k + 1)
  inv : Function.Involutive π
  fix : π c = c
  ne : ∀ x, x ≠ c → π x ≠ x
  minU : ∀ x, x < π x → x ∈ U

namespace PairData

variable {U : Finset (Fin (2 * k + 1))} (P : PairData k U)

/-- Step (ii) of `q3_ballot_lower_bound.md`: the partner of an element other than `c` is not `c`. -/
lemma π_ne_c {x : Fin (2 * k + 1)} (hx : x ≠ P.c) : P.π x ≠ P.c := by
  intro h
  apply hx
  rw [← P.inv x, h, P.fix]

/-- The matching `J ∈ 𝒥`: `{0, c}` together with the pairs `{x, π x}` (shifted by one). -/
def J : Fin (2 * k + 2) → Fin (2 * k + 2) :=
  Fin.cases P.c.succ (fun j => if j = P.c then 0 else (P.π j).succ)

/-- Step (ii) of `q3_ballot_lower_bound.md`: the partner of `0` in `J` is `c`. -/
lemma J_zero : P.J 0 = P.c.succ := rfl

/-- Step (ii) of `q3_ballot_lower_bound.md`: the partner in `J` of a nonzero element. -/
lemma J_succ (j : Fin (2 * k + 1)) : P.J j.succ = if j = P.c then 0 else (P.π j).succ := rfl

/-- The matching of step (ii) as an element of `𝒥`. -/
def matching : Matching k := ⟨P.J, by
  intro x
  refine Fin.cases ?_ (fun j => ?_) x
  · rw [J_zero, J_succ, if_pos rfl]
    exact ⟨Fin.succ_ne_zero _, rfl⟩
  · by_cases hj : j = P.c
    · rw [J_succ, if_pos hj, J_zero, hj]
      exact ⟨(Fin.succ_ne_zero _).symm, rfl⟩
    · rw [J_succ, if_neg hj, J_succ, if_neg (P.π_ne_c hj), P.inv j]
      exact ⟨fun h => P.ne j hj (Fin.succ_injective _ h), rfl⟩⟩

/-- The smaller elements `a` of the pairs of `J` not containing `0`. -/
noncomputable def A : Finset (Fin (2 * k + 1)) := univ.filter (fun x => x ≠ P.c ∧ x < P.π x)

/-- Untouched ("matched") pairs: the larger element is not in `U`. -/
noncomputable def Am : Finset (Fin (2 * k + 1)) := P.A.filter (fun x => P.π x ∉ U)

/-- Touched ("full") pairs: both elements are in `U`. -/
noncomputable def Af : Finset (Fin (2 * k + 1)) := P.A.filter (fun x => P.π x ∈ U)

/-- The contribution `y_c` (if `c ∈ U`) to the monomial factors. -/
noncomputable def C : Fin (2 * k + 1) →₀ ℕ := if P.c ∈ U then Finsupp.single P.c 1 else 0

/-- The exponent of `y_T`: the smaller element of each full pair, and `c` if `c ∈ U`. -/
noncomputable def T : Fin (2 * k + 1) →₀ ℕ := ∑ x ∈ P.Af, Finsupp.single x 1 + P.C

/-- The monomial exponent `Q`: both elements of each full pair, and `c` if `c ∈ U`. -/
noncomputable def Q : Fin (2 * k + 1) →₀ ℕ :=
  ∑ x ∈ P.Af, Finsupp.single x 1 + ∑ x ∈ P.Af, Finsupp.single (P.π x) 1 + P.C

/-- The polynomial lift `X^Q · ∏_{untouched pairs} (X_b − X_a)` of `y_T · D_J`. -/
noncomputable def g : MvPolynomial (Fin (2 * k + 1)) F :=
  monomial P.Q 1 * ∏ x ∈ P.Am, (X (P.π x) - X x)

/-- Step (i) of `q3_ballot_lower_bound.md`: `D_J` is the product of `y_b − y_a` over the pairs `(a, b = π a)` of `J` not containing `0`. -/
lemma D_matching : D (F := F) P.matching =
    ∏ x ∈ P.A, (Ideal.Quotient.mk (squaresIdeal F k) (X (P.π x)) -
      Ideal.Quotient.mk (squaresIdeal F k) (X x)) := by
  unfold D matching A
  rw [prod_filter, prod_filter, Fin.prod_univ_succ]
  simp only [ne_eq, not_true_eq_false, false_and, if_false, one_mul]
  refine prod_congr rfl fun j _ => ?_
  by_cases hj : j = P.c
  · simp [J_succ, hj]
  · rw [J_succ, if_neg hj]
    simp [Fin.succ_ne_zero, Fin.succ_lt_succ_iff, hj, y]

/-- Step (ii) of `q3_ballot_lower_bound.md`: the element `y_T · D_J` lies in `V`; its lift is `P.g`, using `y_a (y_b − y_a) = y_a y_b` for touched pairs (step (i)). -/
lemma mk_g_mem : Ideal.Quotient.mk (squaresIdeal F k) (P.g (F := F)) ∈ V F k := by
  set mk := Ideal.Quotient.mk (squaresIdeal F k)
  have hsq : ∀ x, mk (X x) * mk (X x) = 0 := fun x => by
    rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem, ← sq]
    exact Ideal.subset_span ⟨x, rfl⟩
  have hadd : ∀ a b : Fin (2 * k + 1) →₀ ℕ,
      monomial (a + b) (1 : F) = monomial a 1 * monomial b 1 := by
    intro a b; rw [monomial_mul, one_mul]
  have hmono1 : mk (monomial (∑ x ∈ P.Af, Finsupp.single x 1) (1 : F)) = ∏ x ∈ P.Af, mk (X x) := by
    rw [monomial_sum_one, map_prod]; rfl
  have hmono2 : mk (monomial (∑ x ∈ P.Af, Finsupp.single (P.π x) 1) (1 : F)) =
      ∏ x ∈ P.Af, mk (X (P.π x)) := by
    rw [monomial_sum_one, map_prod]; rfl
  have hsplit : ∏ x ∈ P.A, (mk (X (P.π x)) - mk (X x)) =
      (∏ x ∈ P.Af, (mk (X (P.π x)) - mk (X x))) * ∏ x ∈ P.Am, (mk (X (P.π x)) - mk (X x)) :=
    (prod_filter_mul_prod_filter_not _ _ _).symm
  have hpair : (∏ x ∈ P.Af, mk (X x)) * ∏ x ∈ P.Af, mk (X (P.π x)) =
      (∏ x ∈ P.Af, mk (X x)) * ∏ x ∈ P.Af, (mk (X (P.π x)) - mk (X x)) := by
    rw [← prod_mul_distrib, ← prod_mul_distrib]
    refine prod_congr rfl fun x _ => ?_
    rw [mul_sub, hsq, sub_zero]
  have key : mk (P.g (F := F)) = mk (monomial P.T 1) * D (F := F) P.matching := by
    rw [D_matching, hsplit, g, T, Q, hadd, hadd, hadd]
    simp only [map_mul, map_prod, map_sub]
    rw [hmono1, hmono2]
    calc (∏ x ∈ P.Af, mk (X x)) * (∏ x ∈ P.Af, mk (X (P.π x))) * mk (monomial P.C 1) *
          ∏ x ∈ P.Am, (mk (X (P.π x)) - mk (X x))
        = ((∏ x ∈ P.Af, mk (X x)) * ∏ x ∈ P.Af, mk (X (P.π x))) * mk (monomial P.C 1) *
          ∏ x ∈ P.Am, (mk (X (P.π x)) - mk (X x)) := by ring
      _ = _ := by rw [hpair]; ring
  rw [key]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨_, rfl⟩)

/-- Step (i)/(ii) of `q3_ballot_lower_bound.md`: the leading monomial of `y_T · D_J` is `y_U` (`U = {a : (a, b) untouched} ∪ ⋃_{touched pairs} {a, b} ∪ ({c} ∩ T)`). -/
lemma indU_eq : indU U = P.Q + ∑ x ∈ P.Am, Finsupp.single x 1 := by
  ext y
  have hAf : ∀ x, x ∈ P.Af ↔ (x ≠ P.c ∧ x < P.π x) ∧ P.π x ∈ U := by
    intro x; simp [Af, A]
  have hAm : ∀ x, x ∈ P.Am ↔ (x ≠ P.c ∧ x < P.π x) ∧ P.π x ∉ U := by
    intro x; simp [Am, A]
  have hsum : (∑ x ∈ P.Af, Finsupp.single (P.π x) 1 : Fin (2 * k + 1) →₀ ℕ) y =
      if P.π y ∈ P.Af then 1 else 0 := by
    rw [Finsupp.finset_sum_apply]
    simp_rw [Finsupp.single_apply, P.inv.eq_iff]
    rw [sum_ite_eq']
  have h1 := indU_apply P.Af y
  have h2 := indU_apply P.Am y
  unfold indU at h1 h2
  have hC : P.C y = if P.c ∈ U ∧ P.c = y then 1 else 0 := by
    unfold C
    by_cases hc : P.c ∈ U <;> simp [hc, Finsupp.single_apply]
  simp only [Q, Finsupp.add_apply, hsum, h1, h2, hC, indU_apply]
  by_cases hyc : y = P.c
  · subst hyc
    simp [hAf, hAm, P.fix]
  · have hne := P.ne y hyc
    have hpc := P.π_ne_c hyc
    have hyc' : P.c ≠ y := Ne.symm hyc
    rcases lt_or_gt_of_ne hne with h | h
    · have h' : ¬ y < P.π y := lt_asymm h
      simp only [hAf, hAm, P.inv y, hyc, hpc, h, h', hyc', ne_eq, not_false_eq_true, true_and,
        and_false, false_and, if_false]
      split_ifs <;> simp_all
    · have hyU := P.minU y h
      have h' : ¬ P.π y < y := lt_asymm h
      simp only [hAf, hAm, P.inv y, hyc, hpc, h, h', hyc', hyU, ne_eq, not_false_eq_true,
        true_and, and_false, false_and, if_false, if_true]
      split_ifs <;> simp_all

/-- Step (i) of `q3_ballot_lower_bound.md`: in each untouched pair `(a, b)` we have `a < b`. -/
lemma wt_lt : ∀ x ∈ P.Am, wt k x < wt k (P.π x) := by
  intro x hx
  simp only [Am, A, mem_filter, mem_univ, true_and] at hx
  exact hx.1.2

/-- Steps (i)–(ii) of `q3_ballot_lower_bound.md`: the coefficient of `y_U` in `y_T · D_J` is `±1`. -/
lemma coeff_g_indU : coeff (indU U) (P.g (F := F)) ≠ 0 := by
  unfold g
  rw [coeff_monomial_mul_prod_sub (wt k) P.π P.Am P.wt_lt P.Q (indU U) (by rw [indU_eq]),
    if_pos P.indU_eq]
  exact pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)

/-- Steps (i)–(ii) of `q3_ballot_lower_bound.md`: `y_U` is the leading monomial of `y_T · D_J` (all other monomials of weight at most that of `y_U` have coefficient `0`). -/
lemma coeff_g_eq_zero (m : Fin (2 * k + 1) →₀ ℕ) (hm : m ≠ indU U)
    (hw : Finsupp.weight (wt k) m ≤ Finsupp.weight (wt k) (indU U)) :
    coeff m (P.g (F := F)) = 0 := by
  unfold g
  rw [coeff_monomial_mul_prod_sub (wt k) P.π P.Am P.wt_lt P.Q m (by rwa [← indU_eq]),
    if_neg (by rwa [← indU_eq])]

end PairData

end BallotBound

end
