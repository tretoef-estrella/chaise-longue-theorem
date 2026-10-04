module

public import RequestProject.RankTwo.OddDefs

/-!
# Part H of `q_membership.md`: the matrix `H(y)` in the box

Theorem H of `q_membership.md`: (H1) the entries of `RankTwo.Hm h y` factor in the box,
(H2) `Hm` commutes with restriction of the indices, (H3) the sum over matchings of
`pf(Hm h z)` in the box. `r = 2h + 1`, `D(a, b) = ColOne.Dab (2h+2) a b`.
-/

@[expose] public section

namespace Membership

open Matrix Polynomial Finset Pfaffian

variable {A : Type*} [CommRing A]

/-- **(H1)** of Theorem H in `q_membership.md`: if `y_j^{2h+1} = 0` then
`Hm h y (i, j) = C(D(y_i, y_j))·Od h y (j)` with `D = ColOne.Dab (2h+2)` (from (S3)). The
hypothesis `h ≥ 1` of Part H is not needed. -/
theorem H1 (h : ℕ) {n : ℕ} (y : Fin n → A) (i j : Fin n) (hj : y j ^ (2 * h + 1) = 0) :
    RankTwo.Hm h y i j = C (ColOne.Dab (2 * h + 2) (y i) (y j)) * RankTwo.Od h y j := by
  unfold RankTwo.Hm RankTwo.Od
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [show 2 * (h + τ) + 1 = 2 * h + (2 * τ + 1) by ring, RankTwo.S3 h _ _ _ hj, C_mul]
  ring

/-- **(H2)** of Theorem H in `q_membership.md`: for every map `f : Fin m → Fin n`,
`(Hm h y).submatrix f f = Hm h (y ∘ f)`. -/
theorem H2 (h : ℕ) {n m : ℕ} (y : Fin n → A) (f : Fin m → Fin n) :
    (RankTwo.Hm h y).submatrix f f = RankTwo.Hm h (y ∘ f) := rfl

/-- **(H3)** of Theorem H in `q_membership.md`: if `z_i^{2h+1} = 0` for every `i`, then
`pf(Hm h z) = Σ_π (−1)^{cr(π)}·C(Π_{x < π(x)} D(z_x, z_{π(x)}))·Π_{x < π(x)} Od h z (π(x))`,
the sum over the perfect matchings `π` of `Fin m` as in (A1) `pf_eq_sum_matchings`, with
`D = ColOne.Dab (2h+2)`. (From (A1) and (H1).) -/
theorem H3 (h : ℕ) {m : ℕ} (z : Fin m → A) (hz : ∀ i, z i ^ (2 * h + 1) = 0) :
    pf m (RankTwo.Hm h z) = ∑ π ∈ univ.filter (fun π : Fin m → Fin m => IsMatching π),
      (-1) ^ (crossings π) *
        C (∏ x ∈ univ.filter (fun x => x < π x), ColOne.Dab (2 * h + 2) (z x) (z (π x))) *
        ∏ x ∈ univ.filter (fun x => x < π x), RankTwo.Od h z (π x) := by
  rw [pf_eq_sum_matchings]
  refine Finset.sum_congr rfl fun π _ => ?_
  simp_rw [H1 h z _ _ (hz _), Finset.prod_mul_distrib, map_prod]
  ring

end Membership
