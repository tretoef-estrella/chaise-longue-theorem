module

public import RequestProject.Pfaffian.Bordered

/-!
# Part B of `q_pfaffian.md`: (B4), the expansion along a variable

As in the file: (A4) along the variable `x`; the terms `z = n + k` give the sum over the
borders, and the terms `z = b < n` are matched with the expansion (B2) of
`bpf(a^{(x)}; c^{(x)}, a_x^{(x)})` along its last border.

The statement is split according to the number of borders: `s + 1` borders
(`bpf_expand_var`) and no border (`bpf_expand_var_zero`, where the sum over the borders is
empty), because the bordered Pfaffian "with the columns `c_j`, `j ≠ k`" has `s` borders.
-/

@[expose] public section

namespace Pfaffian

open Finset Equiv

variable {R : Type*} [CommRing R]

/-- Auxiliary for (B4) of `q_pfaffian.md`: reindexing by `Fin.cast` does not change the Pfaffian. -/
theorem pf_submatrix_cast {k k' : ℕ} (h : k = k') (M : Matrix (Fin k') (Fin k') R) :
    pf k (M.submatrix (Fin.cast h) (Fin.cast h)) = pf k' M := by
  subst h; rfl

/-- Auxiliary for (B4) of `q_pfaffian.md`: the term of a border `k` in the expansion along the variable `x`. -/
theorem border_term {n s : ℕ} (a : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (c : Fin (s + 1) → Fin (n + 1) → R) (x : Fin (n + 1)) (k : Fin (s + 1)) :
    eps ((Fin.castAdd (s + 1) x : Fin (n + 1 + (s + 1))) : ℕ)
        ((Fin.natAdd (n + 1) k : Fin (n + 1 + (s + 1))) : ℕ) *
      bmat a c (Fin.castAdd (s + 1) x) (Fin.natAdd (n + 1) k) *
      pf (n + s) ((bmat a c).submatrix (bemb x.succAbove k.succAbove)
        (bemb x.succAbove k.succAbove)) =
    (-1) ^ ((x : ℕ) + (n + 1) + (k : ℕ) + 1) * c k x *
      bpf (a.submatrix x.succAbove x.succAbove) (fun j i => c (k.succAbove j) (x.succAbove i)) := by
  rw [bmat_submatrix_bemb, bmat_cn]
  unfold eps bpf
  simp only [Fin.val_castAdd, Fin.val_natAdd]
  rw [if_pos (by omega)]
  ring_nf

/-- Auxiliary for (B4) of `q_pfaffian.md`: the range condition for the minors of the border terms. -/
theorem border_range {n s : ℕ} (x : Fin (n + 1)) (k : Fin (s + 1)) (y : Fin (n + 1 + (s + 1))) :
    (∃ p, bemb (n' := n) (s' := s) x.succAbove k.succAbove p = y) ↔
      (y ≠ Fin.castAdd (s + 1) x ∧ y ≠ Fin.natAdd (n + 1) k) := by
  induction y using Fin.addCases with
  | left i =>
    rw [bemb_range_castAdd, Fin.exists_succAbove_eq_iff]
    simp only [ne_eq, Fin.castAdd_inj]
    exact ⟨fun h => ⟨h, castAdd_ne_natAdd _ _⟩, fun h => h.1⟩
  | right k' =>
    rw [bemb_range_natAdd, Fin.exists_succAbove_eq_iff]
    simp only [ne_eq, Fin.natAdd_inj]
    exact ⟨fun h => ⟨(castAdd_ne_natAdd _ _).symm, h⟩, fun h => h.2⟩

/-- Auxiliary for (B4) of `q_pfaffian.md`: the range condition for the minors of the variable terms. -/
theorem var_range {n s : ℕ} (x : Fin (n + 2)) (b : Fin (n + 1)) (h : n + 1 + s = n + (s + 1))
    (y : Fin (n + 2 + (s + 1))) :
    (∃ p, bemb (n' := n) (s' := s + 1) (fun i => x.succAbove (b.succAbove i)) id
        (Fin.cast h p) = y) ↔
      (y ≠ Fin.castAdd (s + 1) x ∧ y ≠ Fin.castAdd (s + 1) (x.succAbove b)) := by
  have e : (∃ p, bemb (n' := n) (s' := s + 1) (fun i => x.succAbove (b.succAbove i)) id
      (Fin.cast h p) = y) ↔
      ∃ p, bemb (n' := n) (s' := s + 1) (fun i => x.succAbove (b.succAbove i)) id p = y :=
    ⟨fun ⟨p, hp⟩ => ⟨_, hp⟩, fun ⟨p, hp⟩ => ⟨Fin.cast h.symm p, by simpa using hp⟩⟩
  rw [e]
  induction y using Fin.addCases with
  | left i =>
    rw [bemb_range_castAdd, exists_succAbove_succAbove_iff]
    simp only [ne_eq, Fin.castAdd_inj]
  | right k' =>
    rw [bemb_range_natAdd]
    exact ⟨fun _ => ⟨(castAdd_ne_natAdd _ _).symm, (castAdd_ne_natAdd _ _).symm⟩,
      fun _ => ⟨k', rfl⟩⟩

/-- Auxiliary for (B4) of `q_pfaffian.md`: the variable term `b = x.succAbove b'` of the expansion along `x`
equals the corresponding term of the expansion of `bpf(a^{(x)}; c^{(x)}, a_x^{(x)})` along its
last border (with the sign `(−1)^{x+n+s}`). -/
theorem var_term {n s : ℕ} (a : Matrix (Fin (n + 2)) (Fin (n + 2)) R)
    (c : Fin (s + 1) → Fin (n + 2) → R) (x : Fin (n + 2)) (b : Fin (n + 1))
    (h : n + 1 + s = n + (s + 1)) :
    eps ((Fin.castAdd (s + 1) x : Fin (n + 2 + (s + 1))) : ℕ)
        ((Fin.castAdd (s + 1) (x.succAbove b) : Fin (n + 2 + (s + 1))) : ℕ) *
      bmat a c (Fin.castAdd (s + 1) x) (Fin.castAdd (s + 1) (x.succAbove b)) *
      pf (n + 1 + s) ((bmat a c).submatrix
        (fun p => bemb (fun i => x.succAbove (b.succAbove i)) id (Fin.cast h p))
        (fun p => bemb (fun i => x.succAbove (b.succAbove i)) id (Fin.cast h p))) =
    (-1) ^ ((x : ℕ) + (n + 2) + (s + 1)) *
      ((-1) ^ ((n + 1) + (s + 1 + 1) + (b : ℕ)) *
        (Fin.snoc (α := fun _ => Fin (n + 1) → R) (fun k i => c k (x.succAbove i))
          (fun i => a x (x.succAbove i))) (Fin.last (s + 1)) b *
        bpf ((a.submatrix x.succAbove x.succAbove).submatrix b.succAbove b.succAbove)
          (fun k i => (Fin.snoc (α := fun _ => Fin (n + 1) → R)
            (fun k i => c k (x.succAbove i)) (fun i => a x (x.succAbove i))) k.castSucc
              (b.succAbove i))) := by
  have e1 : (bmat a c).submatrix
      (fun p => bemb (fun i => x.succAbove (b.succAbove i)) id (Fin.cast h p))
      (fun p => bemb (fun i => x.succAbove (b.succAbove i)) id (Fin.cast h p)) =
      ((bmat a c).submatrix (bemb (fun i => x.succAbove (b.succAbove i)) id)
        (bemb (fun i => x.succAbove (b.succAbove i)) id)).submatrix (Fin.cast h) (Fin.cast h) :=
    rfl
  rw [e1, pf_submatrix_cast, bmat_submatrix_bemb, bmat_cc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castAdd, eps_succAbove]
  unfold bpf
  have e2 : (-1 : R) ^ ((x : ℕ) + (n + 2) + (s + 1)) * (-1) ^ ((n + 1) + (s + 1 + 1) + (b : ℕ)) =
      (-1) ^ ((x : ℕ) + (b : ℕ)) := by
    rw [← pow_add, show (x : ℕ) + (n + 2) + (s + 1) + ((n + 1) + (s + 1 + 1) + (b : ℕ)) =
      (x + b) + 2 * (n + s + 3) by ring, pow_add, pow_mul]
    simp
  rw [← mul_assoc, ← mul_assoc, e2]
  rfl

/-- **(B4)** of Theorem B in `q_pfaffian.md` (expansion along a variable; (F4) of the paper),
for `n ≥ 1` variables (written `n + 1`) and `s ≥ 1` borders (written `s + 1`): for a variable
`x`, with `a_x` the column `b ↦ a(x, b)`,
`bpf(a; c) = (−1)^{x+n+s}·bpf(a^{(x)}; c_0^{(x)}, …, c_{s−1}^{(x)}, a_x^{(x)})
  + Σ_{k < s} (−1)^{x+n+k+1}·c_k(x)·bpf(a^{(x)}; the columns c_j^{(x)} with j ≠ k)`
(here `n` and `s` of the file are `n + 1` and `s + 1`; the columns `c_j`, `j ≠ k`, in order, are
`c (k.succAbove j)`; the new last border `a_x^{(x)}` is appended with `Fin.snoc`). -/
theorem bpf_expand_var {n s : ℕ} (a : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (ha : IsAlt a)
    (c : Fin (s + 1) → Fin (n + 1) → R) (x : Fin (n + 1)) :
    bpf a c = (-1) ^ ((x : ℕ) + (n + 1) + (s + 1)) *
        bpf (a.submatrix x.succAbove x.succAbove)
          (Fin.snoc (α := fun _ => Fin n → R) (fun k i => c k (x.succAbove i))
            (fun i => a x (x.succAbove i)))
      + ∑ k : Fin (s + 1), (-1) ^ ((x : ℕ) + (n + 1) + (k : ℕ) + 1) * c k x *
        bpf (a.submatrix x.succAbove x.succAbove)
          (fun j i => c (k.succAbove j) (x.succAbove i)) := by
  rcases n with _ | n
  · rw [bpf_eq_zero_of_lt (a.submatrix x.succAbove x.succAbove) (ha.submatrix _) _ (by omega),
      mul_zero, show ∀ y : R, 0 + y = y from zero_add, bpf]
    rw [pf_expand_fam (k := 0 + s) (by omega) _ (ha.bmat c) (Fin.castAdd (s + 1) x)
      (fun k : Fin (s + 1) => Fin.natAdd 1 k) (fun k k' h => (Fin.natAdd_inj _).1 h)
      (fun k => (castAdd_ne_natAdd _ _).symm) ?_ (fun k => bemb x.succAbove k.succAbove) ?_]
    · exact Finset.sum_congr rfl fun k _ => border_term a c x k
    · intro z hz hφ
      exfalso
      induction z using Fin.addCases with
      | left j => exact hz (by rw [show j = x from Fin.ext (by omega)])
      | right k => exact hφ k rfl
    · intro k
      exact ⟨bemb_strictMono (Fin.strictMono_succAbove _) (Fin.strictMono_succAbove _),
        border_range x k⟩
  · have h : n + 1 + s = n + (s + 1) := by omega
    rw [bpf_expand_last (a.submatrix x.succAbove x.succAbove) (ha.submatrix _), bpf]
    rw [pf_expand_fam (k := n + 1 + s) (by omega) _ (ha.bmat c) (Fin.castAdd (s + 1) x)
      (ι := Fin (n + 1) ⊕ Fin (s + 1))
      (Sum.elim (fun b => Fin.castAdd (s + 1) (x.succAbove b)) (fun k => Fin.natAdd (n + 2) k))
      ?_ ?_ ?_
      (Sum.elim (fun b p => bemb (fun i => x.succAbove (b.succAbove i)) id (Fin.cast h p))
        (fun k => bemb x.succAbove k.succAbove)) ?_]
    · rw [Fintype.sum_sum_type, Finset.mul_sum]
      congr 1
      · refine Finset.sum_congr rfl fun b _ => ?_
        exact var_term a c x b h
      · exact Finset.sum_congr rfl fun k _ => border_term a c x k
    · rintro (b | k) (b' | k') hbb
      · simp only [Sum.elim_inl, Fin.castAdd_inj] at hbb
        rw [Fin.succAbove_right_injective hbb]
      · exact absurd hbb (castAdd_ne_natAdd _ _)
      · exact absurd hbb.symm (castAdd_ne_natAdd _ _)
      · simp only [Sum.elim_inr] at hbb
        rw [(Fin.natAdd_inj _).1 hbb]
    · rintro (b | k)
      · simp only [Sum.elim_inl, ne_eq, Fin.castAdd_inj]
        exact Fin.succAbove_ne _ _
      · exact (castAdd_ne_natAdd _ _).symm
    · intro z hz hφ
      exfalso
      induction z using Fin.addCases with
      | left j =>
        have hj : j ≠ x := fun e => hz (by rw [e])
        obtain ⟨b, rfl⟩ := Fin.exists_succAbove_eq hj
        exact hφ (Sum.inl b) rfl
      | right k => exact hφ (Sum.inr k) rfl
    · rintro (b | k)
      · refine ⟨fun p q hpq => ?_, var_range x b h⟩
        exact bemb_strictMono
          (fun i j hij => Fin.strictMono_succAbove _ (Fin.strictMono_succAbove _ hij))
          strictMono_id (show Fin.cast h p < Fin.cast h q from hpq)
      · exact ⟨bemb_strictMono (Fin.strictMono_succAbove _) (Fin.strictMono_succAbove _),
          border_range x k⟩

/-- **(B4)** of Theorem B in `q_pfaffian.md` (expansion along a variable; (F4) of the paper),
case of no border (`s = 0`, the sum over the borders is empty), for `n ≥ 1` variables (written
`n + 1`): `bpf(a; ∅) = (−1)^{x+n+0}·bpf(a^{(x)}; a_x^{(x)})`. -/
theorem bpf_expand_var_zero {n : ℕ} (a : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (ha : IsAlt a)
    (c : Fin 0 → Fin (n + 1) → R) (x : Fin (n + 1)) :
    bpf a c = (-1) ^ ((x : ℕ) + (n + 1) + 0) *
        bpf (a.submatrix x.succAbove x.succAbove)
          (Fin.snoc (α := fun _ => Fin n → R) (fun k i => c k (x.succAbove i))
            (fun i => a x (x.succAbove i))) := by
  rcases n with _ | n
  · rw [bpf_eq_zero_of_lt (a.submatrix x.succAbove x.succAbove) (ha.submatrix _) _ (by omega),
      mul_zero]
    exact bpf_odd a c ⟨0, rfl⟩
  · rw [bpf_expand_last (a.submatrix x.succAbove x.succAbove) (ha.submatrix _), bpf]
    rw [pf_expand_fam (k := n + 0) (by omega) _ (ha.bmat c) (Fin.castAdd 0 x)
      (fun b : Fin (n + 1) => Fin.castAdd 0 (x.succAbove b))
      (fun b b' h => Fin.succAbove_right_injective (Fin.castAdd_inj.1 h))
      (fun b => by simp only [ne_eq, Fin.castAdd_inj]; exact Fin.succAbove_ne _ _) ?_
      (fun b => bemb (fun i => x.succAbove (b.succAbove i)) id) ?_]
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [bmat_submatrix_bemb, bmat_cc]
      simp only [Fin.snoc_last, Fin.val_castAdd, eps_succAbove]
      unfold bpf
      have e2 : (-1 : R) ^ ((x : ℕ) + (n + 1 + 1) + 0) * (-1) ^ ((n + 1) + (0 + 1) + (b : ℕ)) =
          (-1) ^ ((x : ℕ) + (b : ℕ)) := by
        rw [← pow_add, show (x : ℕ) + (n + 1 + 1) + 0 + ((n + 1) + (0 + 1) + (b : ℕ)) =
          (x + b) + 2 * (n + 2) by ring, pow_add, pow_mul]
        simp
      have e3 : (fun (k : Fin 0) (i : Fin n) => c (id k) (x.succAbove (b.succAbove i))) =
          (fun k i => (Fin.snoc (α := fun _ => Fin (n + 1) → R)
            (fun k i => c k (x.succAbove i)) (fun i => a x (x.succAbove i))) k.castSucc
              (b.succAbove i)) := funext fun k => k.elim0
      rw [e3, ← mul_assoc, ← mul_assoc, e2]
      rfl
    · intro z hz hφ
      exfalso
      induction z using Fin.addCases with
      | left j =>
        have hj : j ≠ x := fun e => hz (by rw [e])
        obtain ⟨b, rfl⟩ := Fin.exists_succAbove_eq hj
        exact hφ b rfl
      | right k => exact k.elim0
    · intro b
      refine ⟨bemb_strictMono
        (fun i j hij => Fin.strictMono_succAbove _ (Fin.strictMono_succAbove _ hij))
        strictMono_id, fun y => ?_⟩
      induction y using Fin.addCases with
      | left i =>
        rw [bemb_range_castAdd, exists_succAbove_succAbove_iff]
        simp only [ne_eq, Fin.castAdd_inj]
      | right k => exact k.elim0

end Pfaffian
