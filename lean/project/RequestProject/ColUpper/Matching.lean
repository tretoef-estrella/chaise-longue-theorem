module

public import RequestProject.TheoremB.Defs

/-!
# Closed tuples and matchings (proof of part (iii) of `q_col_upper.md`)

For a point set `T` (a `Fibres.FibreSetting`) and a closed tuple `g ∈ T^{2k+2}`
(`TheoremB.closedTuples`), there is a matching `J` of `V = {0, …, 2k+1}` with
`g_{J(x)} = −g_x` for every `x` ("for each pair `{u, −u}` of values, match the positions with value
`u` bijectively to those with value `−u`"); conversely such a matching makes `g` closed.

The bijections are made explicit by ranks: the position `x` with value `u` that is the `i`-th
(from the left) among the positions with value `u` is matched to the `i`-th position with value
`−u`.
-/

@[expose] public section

namespace ColUpper

open Fibres TheoremB

variable {T : Type*} [DecidableEq T] {h : ℕ}

section rank

variable {n : ℕ} (M : Fin n → T)

/-- **Proof of (iii)** in `q_col_upper.md` (*The bijection*, auxiliary): the rank of a position
`x` among the positions with the same value, `#{y < x : M_y = M_x}`. -/
def rk (x : Fin n) : ℕ := (Finset.univ.filter fun y => y < x ∧ M y = M x).card

variable {M}

/-- **Proof of (iii)** in `q_col_upper.md` (auxiliary): positions with the same value and the same
rank are equal. -/
theorem eq_of_rk_eq {x y : Fin n} (hv : M x = M y) (hr : rk M x = rk M y) : x = y := by
  by_contra hne
  have key : ∀ x y : Fin n, M x = M y → x < y → rk M x < rk M y := by
    intro x y hv hlt
    apply Finset.card_lt_card
    refine ⟨fun z hz => ?_, fun hsub => ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
      exact ⟨hz.1.trans hlt, hz.2.trans hv⟩
    · have : x ∈ Finset.univ.filter fun z => z < x ∧ M z = M x :=
        hsub (by simp [hlt, hv])
      simp at this
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact absurd hr (key x y hv hlt).ne
  · exact absurd hr (key y x hv.symm hlt).ne'

/-- **Proof of (iii)** in `q_col_upper.md` (auxiliary): the rank of `x` is less than the number of
positions with value `M_x`. -/
theorem rk_lt_cnt (x : Fin n) : rk M x < cnt M (M x) := by
  apply Finset.card_lt_card
  refine ⟨fun z hz => ?_, fun hsub => ?_⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    exact hz.2
  · have : x ∈ Finset.univ.filter fun z => z < x ∧ M z = M x := hsub (by simp)
    simp at this

/-- **Proof of (iii)** in `q_col_upper.md` (auxiliary): every rank `i < #{M_x = u}` is taken by a
position with value `u`. -/
theorem exists_rk_eq (u : T) {i : ℕ} (hi : i < cnt M u) : ∃ x, M x = u ∧ rk M x = i := by
  have hsurj := Finset.surj_on_of_inj_on_of_card_le (s := Finset.univ.filter fun x => M x = u)
    (t := Finset.range (cnt M u)) (fun x _ => rk M x)
    (fun x hx => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      rw [Finset.mem_range]
      show rk M x < cnt M u
      rw [← hx]
      exact rk_lt_cnt x)
    (fun x y hx hy hxy => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
      exact eq_of_rk_eq (hx.trans hy.symm) hxy)
    (by rw [Finset.card_range]; rfl)
  obtain ⟨x, hx, hxi⟩ := hsurj i (Finset.mem_range.2 hi)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
  exact ⟨x, hx, hxi.symm⟩

end rank

/-- **Proof of (iii)** in `q_col_upper.md` (*The bijection*): for a closed tuple `g ∈ T^n` there is
a fixed-point-free involution `J` of the positions with `g_{J(x)} = −g_x` for every `x`. -/
theorem exists_invol_of_closed [Fintype T] (S : FibreSetting T h) {n : ℕ} {g : Fin n → T}
    (hg : g ∈ closedTuples S n) :
    ∃ J : Fin n → Fin n, ∀ x, J x ≠ x ∧ J (J x) = x ∧ g (J x) = S.neg (g x) := by
  simp only [closedTuples, Finset.mem_filter, Finset.mem_univ, true_and] at hg
  have hex : ∀ x, ∃ y, g y = S.neg (g x) ∧ rk g y = rk g x := fun x =>
    exists_rk_eq (M := g) (S.neg (g x)) (by rw [← hg]; exact rk_lt_cnt x)
  choose J hJ1 hJ2 using hex
  refine ⟨J, fun x => ⟨fun h => S.neg_ne (g x) (by rw [← hJ1 x, h]), ?_, hJ1 x⟩⟩
  apply eq_of_rk_eq (M := g)
  · rw [hJ1, hJ1, S.neg_neg]
  · rw [hJ2, hJ2]

/-- **Proof of (iii)** in `q_col_upper.md` (*The bijection*): for a closed tuple
`g ∈ T^{2k+2}` there is a matching `J` of `V` with `g_{J(x)} = −g_x` for every `x`. -/
theorem exists_matching_of_closed [Fintype T] (S : FibreSetting T h) {k : ℕ} {g : Fin (2 * k + 2) → T}
    (hg : g ∈ closedTuples S (2 * k + 2)) :
    ∃ J : BallotBound.Matching k, ∀ x, g (J.1 x) = S.neg (g x) := by
  obtain ⟨J, hJ⟩ := exists_invol_of_closed S hg
  exact ⟨⟨J, fun x => ⟨(hJ x).1, (hJ x).2.1⟩⟩, fun x => (hJ x).2.2⟩

/-- **Proof of (iii)** in `q_col_upper.md` (*The bijection*): if a matching `J` pairs the entries of
`g` into pairs `{u, −u}` (`g_{J(x)} = −g_x`), then `g` is closed. -/
theorem closed_of_matching [Fintype T] (S : FibreSetting T h) {k : ℕ} {g : Fin (2 * k + 2) → T}
    (J : BallotBound.Matching k) (hJ : ∀ x, g (J.1 x) = S.neg (g x)) :
    g ∈ closedTuples S (2 * k + 2) := by
  simp only [closedTuples, Finset.mem_filter, Finset.mem_univ, true_and]
  intro u
  refine Finset.card_bij' (fun x _ => J.1 x) (fun x _ => J.1 x) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    rw [hJ, hx]
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    rw [hJ, hx, S.neg_neg]
  · intro x _; exact (J.2 x).2
  · intro x _; exact (J.2 x).2

end ColUpper

end
