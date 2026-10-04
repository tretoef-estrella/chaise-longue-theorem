module

public import RequestProject.Pfaffian.Main

/-!
# Part R of `q_rank_two.md`: (R5)

**(R5)** (top coefficient) of Theorem R in `q_rank_two.md`, over the polynomial ring `R[ζ]`
(`Polynomial R`, `ζ = Polynomial.X`). First the statement for `pf`, by induction with the
recursion of the definition; then for `bpf`, by induction on the number of borders with the
expansion along the last border (B2) `Pfaffian.bpf_expand_last`.
-/

@[expose] public section

namespace RankTwo

open Finset Pfaffian Polynomial

variable {R : Type*} [CommRing R]

/-- Auxiliary for (R5) of `q_rank_two.md`: degree and coefficient of `(−1)^e·p·q` when
`deg p ≤ α` and `deg q ≤ β`. -/
theorem signed_mul_aux (e : ℕ) {p q : R[X]} {α β : ℕ} (hp : p.natDegree ≤ α)
    (hq : q.natDegree ≤ β) :
    ((-1 : R[X]) ^ e * p * q).natDegree ≤ α + β ∧
      ((-1 : R[X]) ^ e * p * q).coeff (α + β) = (-1 : R) ^ e * p.coeff α * q.coeff β := by
  have e1 : (-1 : R[X]) ^ e * p * q = C ((-1 : R) ^ e) * (p * q) := by
    simp [mul_assoc]
  rw [e1]
  refine ⟨(natDegree_C_mul_le _ _).trans (natDegree_mul_le_of_le hp hq), ?_⟩
  rw [coeff_C_mul, coeff_mul_add_eq_of_natDegree_le hp hq, mul_assoc]

/-- Auxiliary for (R5) of `q_rank_two.md`: the statement for `pf` on `Fin m` for every `m`,
with `κ = ⌊m/2⌋`. -/
theorem pf_top_aux : ∀ (m d : ℕ) (A : Matrix (Fin m) (Fin m) R[X]),
    (∀ i j, (A i j).natDegree ≤ d) →
    (pf m A).natDegree ≤ m / 2 * d ∧
      (pf m A).coeff (m / 2 * d) = pf m (fun i j => (A i j).coeff d)
  | 0, d, A, _ => by simp
  | 1, d, A, _ => by simp
  | m + 2, d, A, hA => by
    have hm : (m + 2) / 2 * d = d + m / 2 * d := by
      rw [show (m + 2) / 2 = m / 2 + 1 by omega]; ring
    rw [pf_succ_succ, pf_succ_succ, hm]
    have ih := fun j : Fin (m + 1) => pf_top_aux m d
      (A.submatrix (fun i => (j.succAbove i).succ) (fun i => (j.succAbove i).succ))
      (fun i k => hA _ _)
    refine ⟨natDegree_sum_le_of_forall_le _ _ fun j _ => ?_, ?_⟩
    · exact (signed_mul_aux _ (hA _ _) (ih j).1).1
    · rw [finset_sum_coeff]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [(signed_mul_aux _ (hA _ _) (ih j).1).2, (ih j).2]
      rfl

/-- **(R5)** of Theorem R in `q_rank_two.md` (top coefficient), the statement for `pf`: for a
matrix `A` on `Fin (2κ)` over `R[ζ]` whose entries have degree at most `d`, `pf(A)` has degree
at most `κd` and `[ζ^{κd}] pf(A) = pf([ζ^d] A)`. -/
theorem R5_pf (κ d : ℕ) (A : Matrix (Fin (2 * κ)) (Fin (2 * κ)) R[X])
    (hA : ∀ i j, (A i j).natDegree ≤ d) :
    (pf (2 * κ) A).natDegree ≤ κ * d ∧
      (pf (2 * κ) A).coeff (κ * d) = pf (2 * κ) (fun i j => (A i j).coeff d) := by
  have h := pf_top_aux (2 * κ) d A hA
  rwa [show 2 * κ / 2 = κ by omega] at h

/-- Auxiliary for (R5) of `q_rank_two.md`: the coefficient matrix of an alternating matrix is
alternating. -/
theorem isAlt_coeff {n : ℕ} {a : Matrix (Fin n) (Fin n) R[X]} (ha : IsAlt a) (d : ℕ) :
    IsAlt (fun i j => (a i j).coeff d) :=
  ⟨fun i => by simp [ha.1], fun i j => by simp [ha.2 i j]⟩

/-- Auxiliary for (R5) of `q_rank_two.md`: with no border, `bpf(a; ∅) = pf(a)` entrywise. -/
theorem bmat_zero_borders {n : ℕ} (a : Matrix (Fin n) (Fin n) R) (c : Fin 0 → Fin n → R) :
    bmat a c = a := by
  ext p q
  induction p using Fin.addCases with
  | left i =>
    induction q using Fin.addCases with
    | left j => exact bmat_cc a c i j
    | right k => exact k.elim0
  | right k => exact k.elim0

/-- **(R5)** of Theorem R in `q_rank_two.md` (top coefficient), the statement for `bpf`: let
`a` be an alternating matrix on `Fin n` over `R[ζ]` and `c` a list of `s` border columns over
`R[ζ]`, with `n = s + 2κ`. If every entry `a(i, j)` has degree at most `d` and every entry
`c_k(i)` has degree at most `d_k`, then with `N := κ·d + Σ_k d_k`, `bpf(a; c)` has degree at
most `N` and `[ζ^N] bpf(a; c) = bpf(a^{top}; c^{top})`, where `a^{top}(i, j) = [ζ^d] a(i, j)`
and `c^{top}_k(i) = [ζ^{d_k}] c_k(i)`. -/
theorem R5_bpf (κ d : ℕ) : ∀ {n s : ℕ} (_ : n = s + 2 * κ) (a : Matrix (Fin n) (Fin n) R[X])
    (_ : IsAlt a) (c : Fin s → Fin n → R[X]) (dk : Fin s → ℕ)
    (_ : ∀ i j, (a i j).natDegree ≤ d) (_ : ∀ k i, (c k i).natDegree ≤ dk k),
    (bpf a c).natDegree ≤ κ * d + ∑ k, dk k ∧
      (bpf a c).coeff (κ * d + ∑ k, dk k) =
        bpf (fun i j => (a i j).coeff d) (fun k i => (c k i).coeff (dk k))
  | n, 0, hn, a, _, c, dk, hd, _ => by
    obtain rfl : n = 2 * κ := by omega
    have h := R5_pf κ d a hd
    simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero]
    unfold bpf
    rw [bmat_zero_borders, bmat_zero_borders]
    exact h
  | n, s + 1, hn, a, ha, c, dk, hd, hc => by
    obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    have hN : κ * d + ∑ k, dk k = dk (Fin.last s) + (κ * d + ∑ k : Fin s, dk k.castSucc) := by
      rw [Fin.sum_univ_castSucc]; ring
    rw [bpf_expand_last a ha c, bpf_expand_last _ (isAlt_coeff ha d), hN]
    have ih := fun b : Fin (n + 1) => R5_bpf κ d (n := n) (s := s) (by omega)
      (a.submatrix b.succAbove b.succAbove) (ha.submatrix _)
      (fun k i => c k.castSucc (b.succAbove i)) (fun k => dk k.castSucc)
      (fun i j => hd _ _) (fun k i => hc _ _)
    refine ⟨natDegree_sum_le_of_forall_le _ _ fun b _ => ?_, ?_⟩
    · exact (signed_mul_aux _ (hc _ _) (ih b).1).1
    · rw [finset_sum_coeff]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [(signed_mul_aux _ (hc _ _) (ih b).1).2]
      congr 1
      exact (ih b).2

end RankTwo
