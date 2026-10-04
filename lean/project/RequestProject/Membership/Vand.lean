module

public import RequestProject.Tight.Defs
public import RequestProject.RankTwo.OddDefs

/-!
# Part V of `q_membership.md`: determinants with polynomial columns

Theorem V of `q_membership.md`: (V1) the Vandermonde product `Δ(x) = Π_{i < j} (x_j − x_i)`
divides `det(p_k(x_i))` over any commutative ring; (V2) `Tight.vand y S` is `Δ(y ∘ ι)` for the
increasing enumeration `ι` of `S`; (V3) columns "polynomial in `y`", the three families of such
columns, and the divisibility of a determinant of such columns by `C (Tight.vand y S)`.
Nothing is divided.
-/

@[expose] public section

namespace Membership

open Matrix Polynomial Finset

/-- **(V1)** of Theorem V in `q_membership.md`: for a commutative ring `R`, points
`x : Fin m → R` and polynomials `p_0, …, p_{m−1} ∈ R[T]`, the Vandermonde product
`Δ(x) = Π_{i < j} (x_j − x_i)` divides `det(p_k(x_i))_{i, k < m}` (rows indexed by the points,
columns by the polynomials). Proof by induction on `m` as in the file: subtract the row `0`
from the others, write `p(T) = p(a) + (T − a)·q(T)` with `q = p /ₘ (T − a)`, and expand along
the row `0`. -/
theorem V1 {R : Type*} [CommRing R] : ∀ {m : ℕ} (x : Fin m → R) (p : Fin m → R[X]),
    (∏ i : Fin m, ∏ j ∈ Ioi i, (x j - x i)) ∣ (Matrix.of fun i k => (p k).eval (x i)).det
  | 0, x, p => by simp
  | m + 1, x, p => by
    set a := x 0
    set q : Fin (m + 1) → R[X] := fun k => p k /ₘ (X - C a) with hq
    have hp : ∀ k t, (p k).eval t = (p k).eval a + (t - a) * (q k).eval t := by
      intro k t
      have h := modByMonic_add_div (p k) (monic_X_sub_C a)
      rw [modByMonic_X_sub_C_eq_C_eval] at h
      conv_lhs => rw [← h]
      simp [hq]
    have hdet : (Matrix.of fun i k => (p k).eval (x i)).det =
        (Matrix.of fun i k => (Fin.cons ((p k).eval a)
          (fun i : Fin m => (x i.succ - a) * (q k).eval (x i.succ)) : Fin (m+1) → R) i).det := by
      refine det_eq_of_forall_row_eq_smul_add_const (Fin.cons 0 (fun _ => 1)) 0 rfl ?_
      intro i j
      refine Fin.cases ?_ (fun i' => ?_) i
      · simp [a]
      · simp only [of_apply, Fin.cons_succ, Fin.cons_zero, one_mul]
        rw [hp j]; ring
    rw [hdet, det_succ_row_zero]
    have hΔ : (∏ i : Fin (m + 1), ∏ j ∈ Ioi i, (x j - x i)) =
        (∏ i : Fin m, (x i.succ - a)) * ∏ i : Fin m, ∏ j ∈ Ioi i, (x j.succ - x i.succ) := by
      rw [Fin.prod_univ_succ, Fin.prod_Ioi_zero]
      congr 1
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [Fin.prod_Ioi_succ]
    rw [hΔ]
    refine Finset.dvd_sum fun j _ => ?_
    refine Dvd.dvd.mul_left ?_ _
    have hsub : ((Matrix.of fun i k => (Fin.cons ((p k).eval a)
          (fun i : Fin m => (x i.succ - a) * (q k).eval (x i.succ)) : Fin (m+1) → R) i).submatrix
          Fin.succ j.succAbove) = Matrix.of fun i k => (x i.succ - a) *
            (Matrix.of fun i k => (q (j.succAbove k)).eval (x i.succ)) i k := by
      ext i k; simp
    rw [hsub, det_mul_column]
    exact mul_dvd_mul_left _ (V1 (fun i => x i.succ) (fun k => q (j.succAbove k)))

/-- Auxiliary for (V2) and (M4) of `q_membership.md`: the Vandermonde product is transported
along an order embedding `ι`: `Tight.vand y (ι(T)) = Tight.vand (y ∘ ι) T`. -/
theorem vand_map {α β R : Type*} [LinearOrder α] [LinearOrder β] [CommRing R]
    (y : α → R) (ι : β ↪o α) (T : Finset β) :
    Tight.vand y (T.map ι.toEmbedding) = Tight.vand (y ∘ ι) T := by
  unfold Tight.vand
  rw [prod_map]
  refine prod_congr rfl fun c _ => ?_
  rw [filter_map, prod_map]
  refine prod_congr ?_ fun _ _ => rfl
  ext c'; simp

/-- **(V2)** of Theorem V in `q_membership.md`: for `y : Fin n → A` and a set `S` of `m` indices
with increasing enumeration `ι = S.orderEmbOfFin hS`,
`Tight.vand y S = Δ(y ∘ ι) = Π_{i < j} (y_{ι(j)} − y_{ι(i)})`. -/
theorem V2 {A : Type*} [CommRing A] {n m : ℕ} (y : Fin n → A) (S : Finset (Fin n))
    (hS : S.card = m) :
    Tight.vand y S = ∏ i : Fin m, ∏ j ∈ Ioi i,
      (y (S.orderEmbOfFin hS j) - y (S.orderEmbOfFin hS i)) := by
  conv_lhs => rw [← map_orderEmbOfFin_univ S hS, vand_map]
  unfold Tight.vand
  refine prod_congr rfl fun i _ => prod_congr ?_ fun _ _ => rfl
  ext j; simp

variable {A : Type*} [CommRing A]

/-- **(V3)** of Theorem V in `q_membership.md`, definition: a column `c : Fin n → A[ζ]` is
*polynomial in `y`* if there is `P ∈ (A[ζ])[T]` with `c(i) = P(C(y_i))` for every `i`. -/
def PolyIn {n : ℕ} (y : Fin n → A) (c : Fin n → A[X]) : Prop :=
  ∃ P : Polynomial (Polynomial A), ∀ i, c i = P.eval (C (y i))

/-- **(V3)** of Theorem V in `q_membership.md`: the column `i ↦ C(y_i^e)` is polynomial in `y`
(`P = T^e`). -/
theorem polyIn_pow {n : ℕ} (y : Fin n → A) (e : ℕ) : PolyIn y (fun i => C (y i ^ e)) :=
  ⟨X ^ e, fun i => by simp⟩

/-- **(V3)** of Theorem V in `q_membership.md`: the column `Ev h y` is polynomial in `y`
(`P = Σ_{α=0}^{h} ζ^α T^{2α}`). -/
theorem polyIn_Ev (h : ℕ) {n : ℕ} (y : Fin n → A) : PolyIn y (RankTwo.Ev h y) :=
  ⟨∑ α ∈ range (h + 1), C (X ^ α) * X ^ (2 * α), fun i => by
    simp [RankTwo.Ev, eval_finset_sum]⟩

/-- **(V3)** of Theorem V in `q_membership.md`: the column `Od h y` is polynomial in `y`
(`P = Σ_{β=0}^{h−1} ζ^β T^{2β+1}`). -/
theorem polyIn_Od (h : ℕ) {n : ℕ} (y : Fin n → A) : PolyIn y (RankTwo.Od h y) :=
  ⟨∑ β ∈ range h, C (X ^ β) * X ^ (2 * β + 1), fun i => by
    simp [RankTwo.Od, eval_finset_sum]⟩

/-- **(V3)** of Theorem V in `q_membership.md`, the divisibility: if the columns
`c'_0, …, c'_{m−1}` are polynomial in `y` and `ι = S.orderEmbOfFin hS`, then
`C(Tight.vand y S)` divides `det(c'_k(ι(i)))_{i, k < m}` in `A[ζ]` (by (V1) over `A[ζ]` at the
points `C(y_{ι(i)})`, and (V2)). -/
theorem V3 {n m : ℕ} (y : Fin n → A) (S : Finset (Fin n)) (hS : S.card = m)
    (c' : Fin m → Fin n → A[X]) (hc : ∀ k, PolyIn y (c' k)) :
    C (Tight.vand y S) ∣ (Matrix.of fun i k => c' k (S.orderEmbOfFin hS i)).det := by
  choose P hP using hc
  have e : (Matrix.of fun i k => c' k (S.orderEmbOfFin hS i)) =
      Matrix.of fun i k => (P k).eval (C (y (S.orderEmbOfFin hS i))) := by
    ext i k; simp [hP]
  rw [e, V2 y S hS]
  simpa [map_prod, map_sub] using
    V1 (fun i => C (y (S.orderEmbOfFin hS i))) P

end Membership
