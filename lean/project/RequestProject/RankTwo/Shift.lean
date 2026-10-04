module

public import RequestProject.Pfaffian.Main

/-!
# Part R of `q_rank_two.md`: (R1) and (R2)

**(R1)** (elementary operation: add `λ` times the row-and-column `x` to the row-and-column `w`)
and **(R2)** (border shift) of Theorem R in `q_rank_two.md`, over an arbitrary commutative ring.
The proofs follow the file: (R1) from (A5) `Pfaffian.pf_add_row` and (A3)
`Pfaffian.pf_eq_zero_of_rows`; (R2) by (R1) for one variable at a time.
-/

@[expose] public section

namespace RankTwo

open Finset Pfaffian

variable {R : Type*} [CommRing R]

/-- **(R1)** of Theorem R in `q_rank_two.md`, the matrix
`A'(i, j) := A(i, j) + λ·([i = w]·A(x, j) + [j = w]·A(i, x))`. -/
def elemOp {m : ℕ} (A : Matrix (Fin m) (Fin m) R) (x w : Fin m) (lam : R) :
    Matrix (Fin m) (Fin m) R := fun i j =>
  A i j + lam * ((if i = w then A x j else 0) + (if j = w then A i x else 0))

/-- **(R1)** of Theorem R in `q_rank_two.md`, first part: the matrix `A'` is alternating. -/
theorem elemOp_isAlt {m : ℕ} {A : Matrix (Fin m) (Fin m) R} (hA : IsAlt A) (x w : Fin m)
    (lam : R) : IsAlt (elemOp A x w lam) := by
  refine ⟨fun i => ?_, fun i j => ?_⟩
  · unfold elemOp
    by_cases h : i = w
    · subst h; simp [hA.1, hA.2 i x]
    · simp [h, hA.1]
  · unfold elemOp
    rw [hA.2 i j, hA.2 x i, hA.2 j x]
    split_ifs <;> ring

/-- **(R1)** of Theorem R in `q_rank_two.md` (elementary operation): for an alternating `A`
on `Fin m`, indices `x ≠ w` and `λ ∈ R`, the matrix
`A'(i, j) = A(i, j) + λ·([i = w]·A(x, j) + [j = w]·A(i, x))` is alternating and
`pf(A') = pf(A)`. -/
theorem R1 {m : ℕ} (A : Matrix (Fin m) (Fin m) R) (hA : IsAlt A) {x w : Fin m} (hxw : x ≠ w)
    (lam : R) :
    IsAlt (fun i j => A i j + lam * ((if i = w then A x j else 0) +
      (if j = w then A i x else 0))) ∧
    pf m (fun i j => A i j + lam * ((if i = w then A x j else 0) +
      (if j = w then A i x else 0))) = pf m A := by
  refine ⟨elemOp_isAlt hA x w lam, ?_⟩
  -- the matrix `A''` of the proof
  set A'' : Matrix (Fin m) (Fin m) R := fun i j =>
    if i = w then (if j = w then 0 else A x j) else if j = w then A i x else A i j with hA''
  have hA''alt : IsAlt A'' := by
    refine ⟨fun i => by by_cases h : i = w <;> simp [hA'', h, hA.1], fun i j => ?_⟩
    simp only [hA'']
    by_cases hi : i = w <;> by_cases hj : j = w
    · subst hi; subst hj; simp
    · simp [hi, hj, hA.2 x j]
    · simp [hi, hj, hA.2 i x]
    · simp [hi, hj, hA.2 i j]
  have h1 := pf_add_row (elemOp A x w lam) A A'' (elemOp_isAlt hA x w lam) hA hA''alt w lam
    (fun i j hi hj => by simp [elemOp, hA'', hi, hj])
    (fun k => by
      simp only [elemOp, hA'', if_pos rfl]
      by_cases hk : k = w
      · subst hk; simp [hA.1, hA.2 k x]
      · simp [hk])
  have h2 : pf m A'' = 0 := pf_eq_zero_of_rows A'' hA''alt hxw.symm (fun k => by
    simp only [hA'', if_pos rfl, if_neg hxw]
    by_cases hk : k = w
    · subst hk; simp [hA.1]
    · simp [hk])
  change pf m (elemOp A x w lam) = pf m A
  rw [h1, h2, mul_zero, add_zero]

/-- Auxiliary for (R2) of `q_rank_two.md`: the matrix
`a(i, j) + Σ_{w ∈ S} λ_w·([i = w]·c_k(j) − [j = w]·c_k(i))` (the shift done for the variables of
`S` only). -/
def shiftS {n s : ℕ} (a : Matrix (Fin n) (Fin n) R) (c : Fin s → Fin n → R) (k : Fin s)
    (lam : Fin n → R) (S : Finset (Fin n)) : Matrix (Fin n) (Fin n) R := fun i j =>
  a i j + (if i ∈ S then lam i * c k j else 0) - (if j ∈ S then lam j * c k i else 0)

/-- Auxiliary for (R2) of `q_rank_two.md`: `shiftS` of an alternating matrix is alternating. -/
theorem shiftS_isAlt {n s : ℕ} {a : Matrix (Fin n) (Fin n) R} (ha : IsAlt a)
    (c : Fin s → Fin n → R) (k : Fin s) (lam : Fin n → R) (S : Finset (Fin n)) :
    IsAlt (shiftS a c k lam S) := by
  refine ⟨fun i => by simp [shiftS, ha.1], fun i j => ?_⟩
  simp only [shiftS, ha.2 i j]
  ring

/-- Auxiliary for (R2) of `q_rank_two.md`: the shift for one variable `w ∉ S`, by (R1) applied to
`B(a; c)` with `x := n + k` (the border `k`), the variable `w`, and `λ := −λ_w`. -/
theorem bpf_shiftS_insert {n s : ℕ} {a : Matrix (Fin n) (Fin n) R} (ha : IsAlt a)
    (c : Fin s → Fin n → R) (k : Fin s) (lam : Fin n → R) {S : Finset (Fin n)} {w : Fin n}
    (hw : w ∉ S) : bpf (shiftS a c k lam (insert w S)) c = bpf (shiftS a c k lam S) c := by
  have hB := (shiftS_isAlt ha c k lam S).bmat c
  have h := (R1 (bmat (shiftS a c k lam S) c) hB
    (castAdd_ne_natAdd w k).symm (-lam w)).2
  unfold bpf
  rw [← h]
  congr 1
  ext p q
  induction p using Fin.addCases with
  | left i =>
    induction q using Fin.addCases with
    | left j =>
      simp only [bmat_cc, bmat_nc, bmat_cn, Fin.castAdd_inj, shiftS, mem_insert]
      by_cases hi : i = w <;> by_cases hj : j = w
      · subst hi; subst hj; simp
      · subst hi; simp [hj, hw]; ring
      · subst hj; simp [hi, hw]; ring
      · simp [hi, hj]
    | right k' =>
      simp [(castAdd_ne_natAdd _ _).symm]
  | right k' =>
    induction q using Fin.addCases with
    | left j =>
      simp only [bmat_nc, bmat_nn, Fin.castAdd_inj,
        (castAdd_ne_natAdd _ _).symm, if_false, zero_add]
      by_cases hj : j = w
      · subst hj; simp
      · simp [hj]
    | right k'' => simp [(castAdd_ne_natAdd _ _).symm]

/-- Auxiliary for (R2) of `q_rank_two.md`: the shift for the variables of any finite set `S`. -/
theorem bpf_shiftS {n s : ℕ} {a : Matrix (Fin n) (Fin n) R} (ha : IsAlt a)
    (c : Fin s → Fin n → R) (k : Fin s) (lam : Fin n → R) (S : Finset (Fin n)) :
    bpf (shiftS a c k lam S) c = bpf a c := by
  classical
  induction S using Finset.induction_on with
  | empty => congr 1; ext i j; simp [shiftS]
  | insert w S hw ih => rw [bpf_shiftS_insert ha c k lam hw, ih]

/-- **(R2)** of Theorem R in `q_rank_two.md` (border shift): for an alternating `a` on `Fin n`,
a list `c` of `s` border columns, `k < s` and `λ : Fin n → R`, the matrix
`a'(i, j) := a(i, j) + λ_i·c_k(j) − λ_j·c_k(i)` is alternating and `bpf(a'; c) = bpf(a; c)`. -/
theorem R2 {n s : ℕ} (a : Matrix (Fin n) (Fin n) R) (ha : IsAlt a) (c : Fin s → Fin n → R)
    (k : Fin s) (lam : Fin n → R) :
    IsAlt (fun i j => a i j + lam i * c k j - lam j * c k i) ∧
    bpf (fun i j => a i j + lam i * c k j - lam j * c k i) c = bpf a c := by
  have e : (fun i j => a i j + lam i * c k j - lam j * c k i) = shiftS a c k lam univ := by
    ext i j; simp [shiftS]
  rw [e]
  exact ⟨shiftS_isAlt ha c k lam univ, bpf_shiftS ha c k lam univ⟩

end RankTwo
