module

public import RequestProject.ColUpper.Count
public import RequestProject.ColUpper.Matching
public import RequestProject.TheoremB.Main

/-!
# Part (iii) of the Theorem of `q_col_upper.md`: the points are closed tuples

`K` contains a set `μ_m` of `m` distinct `m`-th roots of unity, `m ≠ 0` in `K` and `m` is odd.

* `evR_psiG_ne_zero_iff` (*The values of `ψ_J`*): `ev_a(ψ_J) ≠ 0` iff `a_{J(x)} ≠ 1` for every
  pair `x < J(x)` and `a_x a_{J(x)} = 1` for every pair `0 < x < J(x)`;
* `pointSetting` (*A point set*): `T = μ_m ∖ {1}` with `u ↦ u^{−1}` is a point set with
  `|T| = m − 1 = 2h`, `h = (m − 1)/2` (for `m ≥ 3`);
* `card_Gamma_eq_card_closed` (*The bijection*): `|Γ|` is the number of closed tuples in
  `T^{2k+2}`;
* `card_Gamma` (Theorem (iii)): `|Γ| = Q_k(m)`, by Theorem (ii) of `q_theorem_B_lower.md`
  (`TheoremB.card_closedTuples` with `q := m`).
-/

@[expose] public section

namespace ColUpper

open ColSplit ColSurv Fibres TheoremB

set_option synthInstance.maxHeartbeats 200000

variable {K : Type*} [Field K] {m : ℕ}

/-! ### The values of `φ` -/

/-- **Proof of (iii)** in `q_col_upper.md`: `φ(1) = m`. -/
theorem phi_one : phi m (1 : K) = m := by simp [phi]

/-- **Proof of (iii)** in `q_col_upper.md`: for `b^m = 1`, `b ≠ 1`: `(b − 1) φ(b) = b^m − 1 = 0`,
so `φ(b) = 0`. -/
theorem phi_eq_zero {b : K} (hb : b ^ m = 1) (h1 : b ≠ 1) : phi m b = 0 := by
  have := geom_sum_mul b m
  rw [hb, sub_self] at this
  exact (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 h1)

/-- **Proof of (iii)** in `q_col_upper.md`: for `b^m = 1` and `m ≠ 0` in `K`: `φ(b) ≠ 0` iff
`b = 1`. -/
theorem phi_ne_zero_iff (hm : (m : K) ≠ 0) {b : K} (hb : b ^ m = 1) : phi m b ≠ 0 ↔ b = 1 :=
  ⟨fun h => by_contra fun h1 => h (phi_eq_zero hb h1), fun h => by rw [h, phi_one]; exact hm⟩

/-- **Proof of (iii)** in `q_col_upper.md`: if `u^m = 1`, `u^2 = 1` and `m` is odd, then
`u = 1` (`u = u^m · (u^2)^{−(m−1)/2}`). -/
theorem eq_one_of_sq_eq_one (hodd : Odd m) {u : K} (hu : u ^ m = 1) (h2 : u ^ 2 = 1) : u = 1 := by
  obtain ⟨t, rfl⟩ := hodd
  rw [pow_succ, pow_mul, h2, one_pow, one_mul] at hu
  exact hu

/-- **Proof of (iii)** in `q_col_upper.md` (*The bijection*): if the entries of `u ∈ K^n` are
`m`-th roots of unity (`m` odd) and an involution `J` pairs them into inverse pairs
(`u_x u_{J(x)} = 1`), then `Π_x u_x = 1`. (Indeed `(Π u)^2 = Π_x u_x u_{J(x)} = 1` and
`(Π u)^m = 1`.) -/
theorem prod_eq_one_of_pairs (hodd : Odd m) {n : ℕ} (u : Fin n → K) (J : Fin n → Fin n)
    (hJ : ∀ x, J (J x) = x) (hu : ∀ x, u x ^ m = 1) (hpair : ∀ x, u x * u (J x) = 1) :
    ∏ x, u x = 1 := by
  apply eq_one_of_sq_eq_one hodd
  · rw [← Finset.prod_pow]; simp [hu]
  · have hperm : ∏ x, u (J x) = ∏ x, u x :=
      Equiv.prod_comp (Function.Involutive.toPerm J hJ) u
    rw [sq]
    nth_rewrite 2 [← hperm]
    rw [← Finset.prod_mul_distrib]
    simp [hpair]

/-- **Proof of (iii)** in `q_col_upper.md` (auxiliary): if `x < y` in `V` then `y ≠ 0`. -/
theorem ne_zero_of_lt {k : ℕ} {x y : Fin (2 * k + 2)} (h : x < y) : y ≠ 0 := by
  rintro rfl
  exact Fin.not_lt_zero x h

section roots

open scoped Classical

variable {μm : Finset K}
  (hprod : (Polynomial.X ^ m - 1 : Polynomial K) = ∏ ξ ∈ μm, (Polynomial.X - Polynomial.C ξ))
include hprod

/-- **Proof of (iii)** in `q_col_upper.md`: the elements of `μ_m` are non-zero. -/
theorem ne_zero_of_mem {ξ : K} (hξ : ξ ∈ μm) : ξ ≠ 0 := by
  rintro rfl
  have := pow_eq_one_of_mem hprod hξ
  rw [zero_pow (pos_of_prod hprod).ne'] at this
  exact zero_ne_one this

/-- **Proof of (iii)** in `q_col_upper.md`: `μ_m` is closed under inverses. -/
theorem inv_mem_of_mem {ξ : K} (hξ : ξ ∈ μm) : ξ⁻¹ ∈ μm :=
  (mem_iff_pow_eq_one hprod _).2 (by rw [inv_pow, pow_eq_one_of_mem hprod hξ, inv_one])

/-- **Proof of (iii)** in `q_col_upper.md`: `1 ∈ μ_m`. -/
theorem one_mem_of_prod : (1 : K) ∈ μm := (mem_iff_pow_eq_one hprod _).2 (one_pow _)

omit hprod in
/-- **Proof of (iii)** in `q_col_upper.md`: for `a ∈ μ_m^d`, the values `a_x = ev_a(t_x)`
indexed by `x ∈ V` (with the dummy value `0` at `x = 0`). -/
noncomputable def aExt {k : ℕ} (a : Fin (2 * k + 1) → μm) : Fin (2 * k + 2) → K :=
  Fin.cases 0 (fun j => (a j : K))

/-- **Proof of (iii)** in `q_col_upper.md`: `ev_a(t_x) = a_x`. -/
theorem evR_tU {k : ℕ} (a : Fin (2 * k + 1) → μm) (x : Fin (2 * k + 2)) :
    evR hprod a (tU K m k x) = aExt a x := by
  cases x using Fin.cases <;> simp [tU, aExt]

omit hprod in
/-- **Proof of (iii)** in `q_col_upper.md`: `a_x ∈ μ_m` for `x ≠ 0`. -/
theorem aExt_mem {k : ℕ} (a : Fin (2 * k + 1) → μm) {x : Fin (2 * k + 2)} (hx : x ≠ 0) :
    aExt a x ∈ μm := by
  obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.2 hx
  simp [aExt]

/-- **Proof of (iii)** in `q_col_upper.md` (*The values of `ψ_J`*): for `a ∈ μ_m^d` and `m ≠ 0`
in `K`: `ev_a(ψ_J) ≠ 0` iff `a_{J(x)} ≠ 1` for every pair `x < J(x)` of `J` and
`a_x a_{J(x)} = 1` for every pair with `0 < x < J(x)`. -/
theorem evR_psiG_ne_zero_iff (hm : (m : K) ≠ 0) {k : ℕ} (a : Fin (2 * k + 1) → μm)
    (J : BallotBound.Matching k) :
    evR hprod a (psiG K m J) ≠ 0 ↔
      (∀ x, x < J.1 x → aExt a (J.1 x) ≠ 1) ∧
        (∀ x, 0 < x → x < J.1 x → aExt a x * aExt a (J.1 x) = 1) := by
  simp only [psiG, map_mul, map_prod, map_sub, map_one, map_phi, evR_tU]
  rw [mul_ne_zero_iff, Finset.prod_ne_zero_iff, Finset.prod_ne_zero_iff]
  apply and_congr
  · simp [sub_ne_zero]
  · apply forall_congr'
    intro x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hpow : 0 < x → x < J.1 x → (aExt a x * aExt a (J.1 x)) ^ m = 1 := by
      intro h0 hlt
      rw [mul_pow, pow_eq_one_of_mem hprod (aExt_mem a h0.ne'),
        pow_eq_one_of_mem hprod (aExt_mem a (ne_zero_of_lt hlt)), one_mul]
    constructor
    · intro h h0 hlt
      exact (phi_ne_zero_iff hm (hpow h0 hlt)).1 (h ⟨h0, hlt⟩)
    · rintro h ⟨h0, hlt⟩
      exact (phi_ne_zero_iff hm (hpow h0 hlt)).2 (h h0 hlt)

omit hprod in
/-- **Proof of (iii)** in `q_col_upper.md` (*A point set*): the set `T := μ_m ∖ {1}`. -/
abbrev Tpts (μm : Finset K) : Type _ := ↥(μm.erase 1)

/-- **Proof of (iii)** in `q_col_upper.md` (*A point set*): for `m ≥ 3` odd,
`T := μ_m ∖ {1}` with `u ↦ u^{−1}` is a point set (`Fibres.FibreSetting`) with
`|T| = m − 1 = 2h`, `h = (m − 1)/2`: if `u^{−1} = u` then `u^2 = 1 = u^m`, so `u = 1`. -/
noncomputable def pointSetting (hodd : Odd m) (h3 : 3 ≤ m) : FibreSetting (Tpts μm) ((m - 1) / 2) where
  neg u := ⟨(u : K)⁻¹, Finset.mem_erase.2 ⟨inv_ne_one.2 (Finset.ne_of_mem_erase u.2),
    inv_mem_of_mem hprod (Finset.mem_of_mem_erase u.2)⟩⟩
  neg_neg u := Subtype.ext (inv_inv _)
  neg_ne u h := by
    have h' : (u : K)⁻¹ = u := congrArg Subtype.val h
    have hu : (u : K) ^ m = 1 := pow_eq_one_of_mem hprod (Finset.mem_of_mem_erase u.2)
    have hne : (u : K) ≠ 0 := ne_zero_of_mem hprod (Finset.mem_of_mem_erase u.2)
    have h2 : (u : K) ^ 2 = 1 := by
      rw [sq]
      nth_rewrite 1 [← h']
      exact inv_mul_cancel₀ hne
    exact Finset.ne_of_mem_erase u.2 (eq_one_of_sq_eq_one hodd hu h2)
  one_le := by obtain ⟨t, rfl⟩ := hodd; omega
  card_eq := by
    rw [Fintype.card_coe, Finset.card_erase_of_mem (one_mem_of_prod hprod), card_of_prod hprod]
    obtain ⟨t, rfl⟩ := hodd
    omega

omit hprod in
/-- **Proof of (iii)** in `q_col_upper.md` (*The bijection*): a tuple `g = (g_0, g_1, …, g_d)` of
`T^{2k+2}` gives the point `(g_1, …, g_d) ∈ μ_m^d`. -/
def tailA {k : ℕ} (g : Fin (2 * k + 2) → Tpts μm) : Fin (2 * k + 1) → μm :=
  fun j => ⟨(g j.succ : K), Finset.mem_of_mem_erase (g j.succ).2⟩

omit hprod in
/-- **Proof of (iii)** in `q_col_upper.md` (auxiliary): `a_x = g_x` for `a = (g_1, …, g_d)` and
`x ≠ 0`. -/
theorem aExt_tailA {k : ℕ} (g : Fin (2 * k + 2) → Tpts μm) {x : Fin (2 * k + 2)} (hx : x ≠ 0) :
    aExt (tailA g) x = (g x : K) := by
  obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.2 hx
  rfl

/-- **Proof of (iii)** in `q_col_upper.md` (*The bijection*): the product of the entries of a
closed tuple `g` is `1`, so `g_0 = (g_1 ⋯ g_d)^{−1}`. -/
theorem head_eq_of_closed (hodd : Odd m) (h3 : 3 ≤ m) {k : ℕ} [DecidableEq (Tpts μm)]
    {g : Fin (2 * k + 2) → Tpts μm} (hg : g ∈ closedTuples (pointSetting hprod hodd h3) (2 * k + 2)) :
    (g 0 : K) = (∏ j : Fin (2 * k + 1), (g j.succ : K))⁻¹ := by
  obtain ⟨J, hJ⟩ := exists_matching_of_closed _ hg
  have hJK : ∀ x, (g (J.1 x) : K) = (g x : K)⁻¹ := fun x => congrArg Subtype.val (hJ x)
  have h1 : ∏ x, (g x : K) = 1 :=
    prod_eq_one_of_pairs hodd (fun x => (g x : K)) J.1 (fun x => (J.2 x).2)
      (fun x => pow_eq_one_of_mem hprod (Finset.mem_of_mem_erase (g x).2))
      (fun x => by
        show (g x : K) * (g (J.1 x) : K) = 1
        rw [hJK x, mul_inv_cancel₀ (ne_zero_of_mem hprod (Finset.mem_of_mem_erase (g x).2))])
  rw [Fin.prod_univ_succ] at h1
  exact eq_inv_of_mul_eq_one_left h1

/-- **Proof of (iii)** in `q_col_upper.md` (*The bijection*): for `m ≥ 3` odd and `m ≠ 0` in `K`,
`a ↦ (a_0, a_1, …, a_d)` with `a_0 = (a_1 ⋯ a_d)^{−1}` is a bijection from `Γ` onto the closed
tuples of `T^{2k+2}` (written here via its inverse `g ↦ (g_1, …, g_d)`); so `|Γ|` is the number
of closed tuples. -/
theorem card_Gamma_eq_card_closed (hm : (m : K) ≠ 0) (hodd : Odd m) (h3 : 3 ≤ m) (k : ℕ)
    [DecidableEq (Tpts μm)] :
    (Gamma hprod k).card = (closedTuples (pointSetting hprod hodd h3) (2 * k + 2)).card := by
  classical
  symm
  apply Finset.card_bij (fun g _ => tailA g)
  · -- a closed tuple gives a point of `Γ`
    intro g hg
    obtain ⟨J, hJ⟩ := exists_matching_of_closed _ hg
    have hJK : ∀ x, (g (J.1 x) : K) = (g x : K)⁻¹ := fun x => congrArg Subtype.val (hJ x)
    simp only [Gamma, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨J, (evR_psiG_ne_zero_iff hprod hm _ J).2 ⟨?_, ?_⟩⟩
    · intro x hx
      rw [aExt_tailA g (ne_zero_of_lt hx)]
      exact Finset.ne_of_mem_erase (g _).2
    · intro x h0 hx
      rw [aExt_tailA g h0.ne', aExt_tailA g (ne_zero_of_lt hx), hJK,
        mul_inv_cancel₀ (ne_zero_of_mem hprod (Finset.mem_of_mem_erase (g x).2))]
  · -- injectivity
    intro g1 hg1 g2 hg2 h
    have ht : ∀ j : Fin (2 * k + 1), (g1 j.succ : K) = (g2 j.succ : K) := fun j =>
      congrArg (fun y : μm => (y : K)) (congrFun h j)
    funext x
    cases x using Fin.cases with
    | zero =>
      apply Subtype.ext
      rw [head_eq_of_closed hprod hodd h3 hg1, head_eq_of_closed hprod hodd h3 hg2]
      simp only [ht]
    | succ j => exact Subtype.ext (ht j)
  · -- surjectivity
    intro a ha
    simp only [Gamma, Finset.mem_filter, Finset.mem_univ, true_and] at ha
    obtain ⟨J, hJ⟩ := ha
    obtain ⟨h1, h2⟩ := (evR_psiG_ne_zero_iff hprod hm a J).1 hJ
    set b := J.1 0 with hbdef
    have hb0 : b ≠ 0 := (J.2 0).1
    have hab : aExt a b ≠ 0 := ne_zero_of_mem hprod (aExt_mem a hb0)
    let v : Fin (2 * k + 2) → K := fun x => if x = 0 then (aExt a b)⁻¹ else aExt a x
    have hvx : ∀ x, x ≠ 0 → v x = aExt a x := fun x hx => if_neg hx
    have hv0 : v 0 = (aExt a b)⁻¹ := if_pos rfl
    have hpair : ∀ x, v x * v (J.1 x) = 1 := by
      intro x
      by_cases hx : x = 0
      · subst hx
        rw [hv0, ← hbdef, hvx b hb0, inv_mul_cancel₀ hab]
      by_cases hJx : J.1 x = 0
      · have hxb : x = b := by rw [hbdef, ← hJx, (J.2 x).2]
        rw [hJx, hv0, hxb, hvx b hb0, mul_inv_cancel₀ hab]
      rw [hvx x hx, hvx _ hJx]
      rcases lt_or_gt_of_ne (J.2 x).1.symm with hlt | hlt
      · exact h2 x (Fin.pos_iff_ne_zero.2 hx) hlt
      · have := h2 (J.1 x) (Fin.pos_iff_ne_zero.2 hJx) (by rw [(J.2 x).2]; exact hlt)
        rw [(J.2 x).2, mul_comm] at this
        exact this
    have hvne : ∀ x, v x ≠ 1 := by
      intro x hvx1
      rcases lt_or_gt_of_ne (J.2 x).1.symm with hlt | hlt
      · have := hpair x
        rw [hvx1, one_mul, hvx _ (ne_zero_of_lt hlt)] at this
        exact h1 x hlt this
      · have hx0 : x ≠ 0 := ne_zero_of_lt hlt
        have := h1 (J.1 x) (by rw [(J.2 x).2]; exact hlt)
        rw [(J.2 x).2, ← hvx x hx0] at this
        exact this hvx1
    have hvmem : ∀ x, v x ∈ μm := by
      intro x
      by_cases hx : x = 0
      · rw [hx, hv0]; exact inv_mem_of_mem hprod (aExt_mem a hb0)
      · rw [hvx x hx]; exact aExt_mem a hx
    let g : Fin (2 * k + 2) → Tpts μm := fun x => ⟨v x, Finset.mem_erase.2 ⟨hvne x, hvmem x⟩⟩
    refine ⟨g, closed_of_matching _ J (fun x => Subtype.ext ?_), ?_⟩
    · show v (J.1 x) = (v x)⁻¹
      exact eq_inv_of_mul_eq_one_right (hpair x)
    · funext j
      apply Subtype.ext
      show v j.succ = (a j : K)
      rw [hvx _ (Fin.succ_ne_zero j)]
      rfl

/-- **Theorem (iii)** of `q_col_upper.md` (the points are closed tuples): if `K` contains a set
`μ_m` of `m` distinct `m`-th roots of unity, `m ≠ 0` in `K`, and `m` is odd, then
`|Γ| = Q_k(m)`. (For `m ≥ 3` this is `card_Gamma_eq_card_closed` together with
`TheoremB.card_closedTuples` with `q := m`, `h := (m − 1)/2`; for `m = 1` both sides are `0`.)
The hypothesis `|μ_m| = m` of the file follows from the factorization and is omitted. -/
theorem card_Gamma (hm : (m : K) ≠ 0) (hodd : Odd m) (k : ℕ) :
    (Gamma hprod k).card = Qk k m := by
  classical
  obtain ⟨t, ht⟩ := hodd
  rcases Nat.eq_zero_or_pos t with h0 | h0
  · -- `m = 1`: `Γ` is empty and `Q_k(1) = 0`
    subst h0
    have hm1 : m = 1 := by omega
    have hQ : Qk k m = 0 := by rw [hm1]; simp [Qk]
    rw [hQ, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro a ha
    simp only [Gamma, Finset.mem_filter, Finset.mem_univ, true_and] at ha
    obtain ⟨J, hJ⟩ := ha
    obtain ⟨h1, -⟩ := (evR_psiG_ne_zero_iff hprod hm a J).1 hJ
    have hJ0 : J.1 0 ≠ 0 := (J.2 0).1
    apply h1 0 (Fin.pos_iff_ne_zero.2 hJ0)
    have := pow_eq_one_of_mem hprod (aExt_mem a hJ0)
    rwa [hm1, pow_one] at this
  · have h3 : 3 ≤ m := by omega
    rw [card_Gamma_eq_card_closed hprod hm ⟨t, ht⟩ h3 k, card_closedTuples]

end roots

end ColUpper

end
