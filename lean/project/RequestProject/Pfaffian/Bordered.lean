module

public import RequestProject.Pfaffian.Expand

/-!
# Part B of `q_pfaffian.md`: bordered Pfaffians, (B0)–(B3)

The **Definition** of Part B (the bordered matrix `B(a; c)` and `bpf(a; c)`) and (B0), (B1),
(B2), (B3) of Theorem B.

Indexing: the `s` border columns are given as a family `c : Fin s → Fin n → R` (`c k` is the
column `c_k`), as allowed in the request. The bordered matrix lives on `Fin (n + s)`, the
variables being the indices `Fin.castAdd s i` (`i < n`) and the borders the indices
`Fin.natAdd n k` (the index `n + k`).
-/

@[expose] public section

namespace Pfaffian

open Finset Equiv

variable {R : Type*} [CommRing R]

/-- **Part B, Definition** of `q_pfaffian.md`: the bordered matrix `B(a; c)` on `Fin (n + s)`
(first the `n` variables, then the `s` borders), with entries `a(i, j)` for `i, j < n`,
`c_k(i)` at `(i, n + k)`, `−c_k(i)` at `(n + k, i)` and `0` at `(n + k, n + k')`. -/
def bmat {n s : ℕ} (a : Matrix (Fin n) (Fin n) R) (c : Fin s → Fin n → R) :
    Matrix (Fin (n + s)) (Fin (n + s)) R := fun p q =>
  Fin.addCases (fun i => Fin.addCases (fun j => a i j) (fun k => c k i) q)
    (fun k => Fin.addCases (fun j => -c k j) (fun _ => 0) q) p

/-- **Part B, Definition** of `q_pfaffian.md`: `bpf(a; c) := pf(B(a; c))`. -/
noncomputable def bpf {n s : ℕ} (a : Matrix (Fin n) (Fin n) R) (c : Fin s → Fin n → R) : R :=
  pf (n + s) (bmat a c)

section entries

variable {n s : ℕ} (a : Matrix (Fin n) (Fin n) R) (c : Fin s → Fin n → R)

/-- Entry `a(i, j)` of the bordered matrix (**Part B, Definition** of `q_pfaffian.md`). -/
@[simp] theorem bmat_cc (i j : Fin n) : bmat a c (Fin.castAdd s i) (Fin.castAdd s j) = a i j := by
  simp [bmat]

/-- Entry `c_k(i)` at `(i, n + k)` of the bordered matrix (**Part B, Definition** of `q_pfaffian.md`). -/
@[simp] theorem bmat_cn (i : Fin n) (k : Fin s) :
    bmat a c (Fin.castAdd s i) (Fin.natAdd n k) = c k i := by
  simp [bmat]

/-- Entry `−c_k(j)` at `(n + k, j)` of the bordered matrix (**Part B, Definition** of `q_pfaffian.md`). -/
@[simp] theorem bmat_nc (k : Fin s) (j : Fin n) :
    bmat a c (Fin.natAdd n k) (Fin.castAdd s j) = -c k j := by
  simp [bmat]

/-- Entry `0` at `(n + k, n + k')` of the bordered matrix (**Part B, Definition** of `q_pfaffian.md`). -/
@[simp] theorem bmat_nn (k k' : Fin s) : bmat a c (Fin.natAdd n k) (Fin.natAdd n k') = 0 := by
  simp [bmat]

end entries

/-- Auxiliary for Part B of `q_pfaffian.md`: a variable index is never a border index. -/
theorem castAdd_ne_natAdd {n s : ℕ} (i : Fin n) (k : Fin s) :
    Fin.castAdd s i ≠ Fin.natAdd n k := by
  intro h
  have h' := congrArg Fin.val h
  rw [Fin.val_castAdd, Fin.val_natAdd] at h'
  omega

/-- **Part B, Definition** of `q_pfaffian.md`: the bordered matrix of an alternating `a` is
alternating. -/
theorem IsAlt.bmat {n s : ℕ} {a : Matrix (Fin n) (Fin n) R} (ha : IsAlt a)
    (c : Fin s → Fin n → R) : IsAlt (bmat a c) := by
  refine ⟨fun p => ?_, fun p q => ?_⟩
  · induction p using Fin.addCases with
    | left i => simp [ha.1]
    | right k => simp
  · induction p using Fin.addCases with
    | left i =>
      induction q using Fin.addCases with
      | left j => rw [bmat_cc, bmat_cc, ha.2]
      | right k => simp
    | right k =>
      induction q using Fin.addCases with
      | left j => simp
      | right k' => simp

/-- Auxiliary for Part B of `q_pfaffian.md`: the map `Fin (n' + s') → Fin (n + s)` sending the
variable `i` to the variable `u i` and the border `k` to the border `v k`. -/
def bemb {n s n' s' : ℕ} (u : Fin n' → Fin n) (v : Fin s' → Fin s) : Fin (n' + s') → Fin (n + s) :=
  Fin.addCases (fun i => Fin.castAdd s (u i)) (fun k => Fin.natAdd n (v k))

/-- Auxiliary for Part B of `q_pfaffian.md`: `bemb u v` on a variable. -/
@[simp] theorem bemb_castAdd {n s n' s' : ℕ} (u : Fin n' → Fin n) (v : Fin s' → Fin s)
    (i : Fin n') : bemb u v (Fin.castAdd s' i) = Fin.castAdd s (u i) := by
  simp [bemb]

/-- Auxiliary for Part B of `q_pfaffian.md`: `bemb u v` on a border. -/
@[simp] theorem bemb_natAdd {n s n' s' : ℕ} (u : Fin n' → Fin n) (v : Fin s' → Fin s)
    (k : Fin s') : bemb u v (Fin.natAdd n' k) = Fin.natAdd n (v k) := by
  simp [bemb]

/-- Auxiliary for Part B of `q_pfaffian.md`: reindexing a bordered matrix along `bemb u v` gives
the bordered matrix of `a` reindexed by `u` with the borders `c ∘ v` restricted along `u`. -/
theorem bmat_submatrix_bemb {n s n' s' : ℕ} (a : Matrix (Fin n) (Fin n) R)
    (c : Fin s → Fin n → R) (u : Fin n' → Fin n) (v : Fin s' → Fin s) :
    (bmat a c).submatrix (bemb u v) (bemb u v) =
      bmat (a.submatrix u u) (fun k i => c (v k) (u i)) := by
  ext p q
  induction p using Fin.addCases with
  | left i =>
    induction q using Fin.addCases with
    | left j => simp
    | right k => simp
  | right k =>
    induction q using Fin.addCases with
    | left j => simp
    | right k' => simp

/-- Auxiliary for Part B of `q_pfaffian.md`: `bemb u v` is increasing if `u` and `v` are. -/
theorem bemb_strictMono {n s n' s' : ℕ} {u : Fin n' → Fin n} {v : Fin s' → Fin s}
    (hu : StrictMono u) (hv : StrictMono v) : StrictMono (bemb u v) := by
  intro p q hpq
  induction p using Fin.addCases with
  | left i =>
    induction q using Fin.addCases with
    | left j =>
      simp only [bemb_castAdd, Fin.lt_def, Fin.val_castAdd] at hpq ⊢
      exact hu (Fin.lt_def.2 hpq)
    | right k => simp only [bemb_castAdd, bemb_natAdd, Fin.lt_def, Fin.val_castAdd,
        Fin.val_natAdd]; omega
  | right k =>
    induction q using Fin.addCases with
    | left j =>
      simp only [Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd] at hpq; omega
    | right k' =>
      simp only [bemb_natAdd, Fin.lt_def, Fin.val_natAdd] at hpq ⊢
      have := hv (Fin.lt_def.2 (by omega : (k : ℕ) < k'))
      rw [Fin.lt_def] at this; omega

/-- Auxiliary for Part B of `q_pfaffian.md`: the variables in the range of `bemb u v`. -/
theorem bemb_range_castAdd {n s n' s' : ℕ} (u : Fin n' → Fin n) (v : Fin s' → Fin s)
    (i : Fin n) : (∃ p, bemb u v p = Fin.castAdd s i) ↔ ∃ j, u j = i := by
  constructor
  · rintro ⟨p, hp⟩
    induction p using Fin.addCases with
    | left j =>
      refine ⟨j, Fin.ext ?_⟩
      have := congrArg Fin.val hp
      simpa using this
    | right k => exact absurd hp.symm (by simpa using castAdd_ne_natAdd i (v k))
  · rintro ⟨j, rfl⟩; exact ⟨Fin.castAdd s' j, by simp⟩

/-- Auxiliary for Part B of `q_pfaffian.md`: the borders in the range of `bemb u v`. -/
theorem bemb_range_natAdd {n s n' s' : ℕ} (u : Fin n' → Fin n) (v : Fin s' → Fin s)
    (k : Fin s) : (∃ p, bemb u v p = Fin.natAdd n k) ↔ ∃ j, v j = k := by
  constructor
  · rintro ⟨p, hp⟩
    induction p using Fin.addCases with
    | left j => exact absurd hp (by simpa using castAdd_ne_natAdd (u j) k)
    | right k' =>
      refine ⟨k', Fin.ext ?_⟩
      have := congrArg Fin.val hp
      simpa using this
  · rintro ⟨j, rfl⟩; exact ⟨Fin.natAdd n' j, by simp⟩

/-! ### (B0) -/

/-- Auxiliary for (B0) of `q_pfaffian.md`: the Pfaffian of the zero matrix on `m ≥ 1` indices is `0`. -/
theorem pf_eq_zero_of_zero {m : ℕ} (hm : 1 ≤ m) (M : Matrix (Fin m) (Fin m) R)
    (hM : ∀ i j, M i j = 0) : pf m M = 0 := by
  rcases m with _ | _ | m
  · omega
  · rfl
  · rw [pf_succ_succ]; simp [hM]

/-- **(B0)** of Theorem B in `q_pfaffian.md`, first part: `bpf(a; c) = 0` if `n + s` is odd. -/
theorem bpf_odd {n s : ℕ} (a : Matrix (Fin n) (Fin n) R) (c : Fin s → Fin n → R)
    (h : Odd (n + s)) : bpf a c = 0 :=
  pf_odd _ _ h

/-! ### (B1) -/

/-- Auxiliary for (B1) of `q_pfaffian.md`: a permutation `σ` of the variables, acting on `Fin (n + s)`. -/
def permVars {n : ℕ} (σ : Perm (Fin n)) (s : ℕ) : Perm (Fin (n + s)) :=
  finSumFinEquiv.permCongr (σ.sumCongr 1)

/-- Auxiliary for (B1) of `q_pfaffian.md`: a permutation `τ` of the borders, acting on `Fin (n + s)`. -/
def permBorders (n : ℕ) {s : ℕ} (τ : Perm (Fin s)) : Perm (Fin (n + s)) :=
  finSumFinEquiv.permCongr ((1 : Perm (Fin n)).sumCongr τ)

/-- Auxiliary for (B1) of `q_pfaffian.md`: `permVars σ s` is `bemb σ id`. -/
theorem permVars_eq {n : ℕ} (σ : Perm (Fin n)) (s : ℕ) :
    (permVars σ s : Fin (n + s) → Fin (n + s)) = bemb σ id := by
  funext p
  induction p using Fin.addCases with
  | left i => simp [permVars, Equiv.permCongr_apply]
  | right k => simp [permVars, Equiv.permCongr_apply]

/-- Auxiliary for (B1) of `q_pfaffian.md`: `permBorders n τ` is `bemb id τ`. -/
theorem permBorders_eq (n : ℕ) {s : ℕ} (τ : Perm (Fin s)) :
    (permBorders n τ : Fin (n + s) → Fin (n + s)) = bemb id τ := by
  funext p
  induction p using Fin.addCases with
  | left i => simp [permBorders, Equiv.permCongr_apply]
  | right k => simp [permBorders, Equiv.permCongr_apply]

/-- **(B1)** of Theorem B in `q_pfaffian.md` (signs; (F1) of the paper), permutations of the
variables: for a permutation `σ` of `Fin n`, with `a^σ(i, j) = a(σ i, σ j)` and
`c^σ_k(i) = c_k(σ i)`, `bpf(a^σ; c^σ) = sgn(σ)·bpf(a; c)`. -/
theorem bpf_perm_vars {n s : ℕ} (a : Matrix (Fin n) (Fin n) R) (ha : IsAlt a)
    (c : Fin s → Fin n → R) (σ : Perm (Fin n)) :
    bpf (a.submatrix σ σ) (fun k i => c k (σ i)) = ((Perm.sign σ : ℤ) : R) * bpf a c := by
  have e : bmat (a.submatrix σ σ) (fun k i => c k (σ i)) =
      (bmat a c).submatrix (permVars σ s) (permVars σ s) := by
    rw [permVars_eq, bmat_submatrix_bemb]; rfl
  unfold bpf
  rw [e, (pf_perm _ (ha.bmat c) _).2]
  simp [permVars, Perm.sign_permCongr, Perm.sign_sumCongr]

/-- **(B1)** of Theorem B in `q_pfaffian.md` (signs; (F1) of the paper), permutations of the
borders: for a permutation `τ` of `Fin s`, `bpf(a; c_{τ 0}, …, c_{τ(s−1)}) = sgn(τ)·bpf(a; c)`. -/
theorem bpf_perm_borders {n s : ℕ} (a : Matrix (Fin n) (Fin n) R) (ha : IsAlt a)
    (c : Fin s → Fin n → R) (τ : Perm (Fin s)) :
    bpf a (fun k => c (τ k)) = ((Perm.sign τ : ℤ) : R) * bpf a c := by
  have e : bmat a (fun k => c (τ k)) =
      (bmat a c).submatrix (permBorders n τ) (permBorders n τ) := by
    rw [permBorders_eq, bmat_submatrix_bemb]; rfl
  unfold bpf
  rw [e, (pf_perm _ (ha.bmat c) _).2]
  simp [permBorders, Perm.sign_permCongr, Perm.sign_sumCongr]

/-! ### (B2) -/

/-- **(B2)** of Theorem B in `q_pfaffian.md` (the borders; (F2) of the paper): `bpf(a; c)` is
additive and homogeneous in each border column `c_k` (the others fixed):
`bpf(a; …, x + t·y, …) = bpf(a; …, x, …) + t·bpf(a; …, y, …)` (in place `k`). -/
theorem bpf_add_border {n s : ℕ} (a : Matrix (Fin n) (Fin n) R) (ha : IsAlt a)
    (c : Fin s → Fin n → R) (k : Fin s) (x y : Fin n → R) (t : R) :
    bpf a (Function.update c k (fun i => x i + t * y i)) =
      bpf a (Function.update c k x) + t * bpf a (Function.update c k y) := by
  unfold bpf
  refine pf_add_row _ _ _ (ha.bmat _) (ha.bmat _) (ha.bmat _) (Fin.natAdd n k) t ?_ ?_
  · intro p q hp hq
    induction p using Fin.addCases with
    | left i =>
      induction q using Fin.addCases with
      | left j => simp
      | right k' =>
        have : k' ≠ k := fun h => hq (by rw [h])
        simp [Function.update_of_ne this]
    | right k' =>
      have : k' ≠ k := fun h => hp (by rw [h])
      induction q using Fin.addCases with
      | left j => simp [Function.update_of_ne this]
      | right k'' => simp
  · intro q
    induction q using Fin.addCases with
    | left j => simp; ring
    | right k' => simp

/-- **(B2)** of Theorem B in `q_pfaffian.md` (the borders; (F2) of the paper): `bpf(a; c) = 0`
if two border columns are equal. -/
theorem bpf_eq_zero_of_border_eq {n s : ℕ} (a : Matrix (Fin n) (Fin n) R) (ha : IsAlt a)
    (c : Fin s → Fin n → R) {k k' : Fin s} (hkk' : k ≠ k') (h : c k = c k') : bpf a c = 0 := by
  unfold bpf
  refine pf_eq_zero_of_rows _ (ha.bmat c) (x := Fin.natAdd n k) (z := Fin.natAdd n k')
    (fun e => hkk' ((Fin.natAdd_inj _).1 e)) fun q => ?_
  induction q using Fin.addCases with
  | left j => simp [h]
  | right k'' => simp

/-- **(B2)** of Theorem B in `q_pfaffian.md` (the borders; (F2) of the paper): the expansion
along the last border, for `s ≥ 1` borders (written `s + 1`) and `n ≥ 1` variables (written
`n + 1`; for `n = 0` both sides are `0`, see (B0)):
`bpf(a; c_0, …, c_s) = Σ_{b} (−1)^{(n+1)+(s+1)+b}·c_s(b)·bpf(a^{(b)}; c_0^{(b)}, …, c_{s−1}^{(b)})`,
where `a^{(b)}` is `a` without the row and the column `b` and `c_k^{(b)}` is `c_k` restricted
to the other indices (in order). -/
theorem bpf_expand_last {n s : ℕ} (a : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (ha : IsAlt a)
    (c : Fin (s + 1) → Fin (n + 1) → R) :
    bpf a c = ∑ b : Fin (n + 1), (-1) ^ ((n + 1) + (s + 1) + (b : ℕ)) * c (Fin.last s) b *
      bpf (a.submatrix b.succAbove b.succAbove) (fun k i => c k.castSucc (b.succAbove i)) := by
  unfold bpf
  rw [pf_expand_fam (k := n + s) (by omega) _ (ha.bmat c) (Fin.natAdd (n + 1) (Fin.last s))
    (fun b : Fin (n + 1) => Fin.castAdd (s + 1) b) (fun b b' h => Fin.castAdd_inj.1 h)
    (fun b => castAdd_ne_natAdd _ _) ?_ (fun b => bemb b.succAbove Fin.castSucc) ?_]
  · refine Finset.sum_congr rfl fun b _ => ?_
    rw [bmat_submatrix_bemb, bmat_nc]
    unfold eps
    simp only [Fin.val_natAdd, Fin.val_last, Fin.val_castAdd]
    rw [if_neg (by omega)]
    ring
  · intro z hz hφ
    induction z using Fin.addCases with
    | left j => exact absurd rfl (hφ j)
    | right k => exact bmat_nn a c _ _
  · intro b
    refine ⟨bemb_strictMono (Fin.strictMono_succAbove _) (Fin.strictMono_castSucc), fun y => ?_⟩
    induction y using Fin.addCases with
    | left i =>
      rw [bemb_range_castAdd, Fin.exists_succAbove_eq_iff]
      simp only [ne_eq, Fin.castAdd_inj]
      exact ⟨fun h => ⟨castAdd_ne_natAdd _ _, h⟩, fun h => h.2⟩
    | right k =>
      rw [bemb_range_natAdd, Fin.exists_castSucc_eq]
      simp only [ne_eq, Fin.natAdd_inj]
      exact ⟨fun h => ⟨h, (castAdd_ne_natAdd _ _).symm⟩, fun h => h.1⟩

/-- **(B0)** of Theorem B in `q_pfaffian.md`, second part: `bpf(a; c) = 0` if `s > n`. -/
theorem bpf_eq_zero_of_lt : ∀ {n s : ℕ} (a : Matrix (Fin n) (Fin n) R), IsAlt a →
    ∀ (c : Fin s → Fin n → R), n < s → bpf a c = 0
  | 0, s, a, _, c, h => by
    unfold bpf
    refine pf_eq_zero_of_zero (by omega) _ fun p q => ?_
    induction p using Fin.addCases with
    | left i => exact i.elim0
    | right k =>
      induction q using Fin.addCases with
      | left j => exact j.elim0
      | right k' => exact bmat_nn a c k k'
  | n + 1, s, a, ha, c, h => by
    obtain ⟨s, rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
    rw [bpf_expand_last a ha c]
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [bpf_eq_zero_of_lt _ (ha.submatrix _) _ (by omega), mul_zero]

/-! ### (B3) -/

/-- **(B3)** of Theorem B in `q_pfaffian.md` (as many borders as variables; (F3) of the paper):
if `n = s`, `bpf(a; c) = (−1)^{s(s−1)/2}·det(c_k(i))_{i, k < s}`; in particular it does not
depend on `a`. -/
theorem bpf_square : ∀ {s : ℕ} (a : Matrix (Fin s) (Fin s) R), IsAlt a →
    ∀ (c : Fin s → Fin s → R),
      bpf a c = (-1) ^ (s * (s - 1) / 2) * (Matrix.of fun i k => c k i).det
  | 0, a, _, c => by simp [bpf]
  | s + 1, a, ha, c => by
    rw [bpf_expand_last a ha c, Matrix.det_succ_column _ (Fin.last s), Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [bpf_square _ (ha.submatrix _), Nat.triangle_succ]
    have e : (Matrix.of fun i k => c k i).submatrix b.succAbove (Fin.last s).succAbove =
        Matrix.of fun i k => c k.castSucc (b.succAbove i) := by
      ext i k; simp [Fin.succAbove_last]
    rw [e]
    simp only [Matrix.of_apply, Fin.val_last]
    have h2 : ((-1 : R) ^ (s + 1 + (s + 1))) = 1 := by
      rw [← two_mul, pow_mul]; simp
    rw [pow_add _ (s + 1 + (s + 1)), h2, pow_add _ (s * (s - 1) / 2)]
    have h3 : ((-1 : R) ^ (s * 2)) = 1 := by rw [mul_comm, pow_mul]; simp
    linear_combination (-(c (Fin.last s) b *
      (Matrix.of fun i k => c k.castSucc (b.succAbove i)).det * (-1) ^ (b : ℕ) *
      (-1) ^ (s * (s - 1) / 2))) * h3

end Pfaffian
