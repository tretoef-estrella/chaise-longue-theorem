module

public import RequestProject.RankTwo.Shift

/-!
# Part R of `q_rank_two.md`: (R4), the rank-two update

**(R4)** of Theorem R in `q_rank_two.md`: for an alternating `a` on `Fin n`, a list `c` of `s`
border columns and two more columns `E, O`, with `M(i, j) = E_i·O_j − E_j·O_i`,
`bpf(a − M; c) = bpf(a; c) + bpf(a; c, E, O)` and `bpf(a + M; c) = bpf(a; c) − bpf(a; c, E, O)`.

The proof is the one of the file. With `K := n + s` and `B := B(a; c)`, the matrix `X_θ` of the
file (on `Fin (K + 2)`) is written `ext2 B Ẽ Õ θ := B(B(B; Ẽ); (Õ, θ))`, where `Ẽ, Õ` are the
columns `E, O` extended by `0` on the borders of `c`: the index `K` is the border `E`, the index
`K + 1` the border `O`, and the entry at `(K, K + 1)` is `θ`.
* Step 1 (`pf_ext2_theta`): `pf(X_θ) = pf(X_0) + θ·pf(B)` (by (A5) along the last index), and
  `X_0 = B(a; c, E, O)` (`bmat_snoc_snoc`).
* Step 2: the elementary operations of the file with `x := N − 1` are one border shift (R2) of
  `B(B(B; Ẽ); (Õ, 1))` (seen as a bordered matrix with the single border `O`), which gives
  `B(B(B'; 0); (Õ, 1))` with `B' = B(a − M; c)`; the second series of operations is replaced by
  the expansion (A4) along the index `K`, whose row is `0` except for the entry `1` at `K + 1`
  (`pf_ext2_zero`).
-/

@[expose] public section

namespace RankTwo

open Finset Pfaffian

variable {R : Type*} [CommRing R]

/-- Auxiliary for (R4) of `q_rank_two.md`: (A4) when the row `x` has a single nonzero entry,
at `z = x.succAbove z'`: `pf(A) = ε(x, z)·A(x, z)·pf(A^{x,z})`. -/
theorem pf_single_row {m : ℕ} (A : Matrix (Fin (m + 2)) (Fin (m + 2)) R) (hA : IsAlt A)
    (x : Fin (m + 2)) (z : Fin (m + 1)) (h : ∀ k, k ≠ x.succAbove z → A x k = 0) :
    pf (m + 2) A = eps (x : ℕ) (x.succAbove z : ℕ) * A x (x.succAbove z) *
      pf m (A.submatrix (fun i => x.succAbove (z.succAbove i))
        (fun i => x.succAbove (z.succAbove i))) := by
  rw [pf_expand A hA x, Finset.sum_eq_single z]
  · intro b _ hb
    rw [h _ (fun e => hb (Fin.succAbove_right_injective e)), mul_zero, zero_mul]
  · intro hz; exact absurd (mem_univ z) hz

section one

variable {K : ℕ} (a : Matrix (Fin K) (Fin K) R) (c : Fin 1 → Fin K → R)

/-- Auxiliary for (R4) of `q_rank_two.md`: entries of a bordered matrix with one border, written
with `Fin.castSucc` and `Fin.last`. -/
@[simp] theorem b1_cc (i j : Fin K) : bmat a c (Fin.castSucc i) (Fin.castSucc j) = a i j :=
  bmat_cc a c i j

/-- Auxiliary for (R4) of `q_rank_two.md`: see `b1_cc`. -/
@[simp] theorem b1_cl (i : Fin K) : bmat a c (Fin.castSucc i) (Fin.last K) = c 0 i :=
  bmat_cn a c i 0

/-- Auxiliary for (R4) of `q_rank_two.md`: see `b1_cc`. -/
@[simp] theorem b1_lc (j : Fin K) : bmat a c (Fin.last K) (Fin.castSucc j) = -c 0 j :=
  bmat_nc a c 0 j

/-- Auxiliary for (R4) of `q_rank_two.md`: see `b1_cc`. -/
@[simp] theorem b1_ll : bmat a c (Fin.last K) (Fin.last K) = 0 :=
  bmat_nn a c 0 0

end one

/-- Auxiliary for (R4) of `q_rank_two.md`: the matrix `X_θ` of the proof of (R4) on
`Fin (K + 2)`: `B` on the first `K` indices, the column `u` at the index `K`, the column `v` at
the index `K + 1`, and `θ` at `(K, K + 1)`. -/
def ext2 {K : ℕ} (B : Matrix (Fin K) (Fin K) R) (u v : Fin K → R) (θ : R) :
    Matrix (Fin (K + 2)) (Fin (K + 2)) R :=
  bmat (n := K + 1) (s := 1) (bmat (n := K) (s := 1) B (fun _ : Fin 1 => u))
    (fun _ : Fin 1 => Fin.snoc (α := fun _ => R) v θ)

/-- Auxiliary for (R4) of `q_rank_two.md`: `X_θ` is alternating. -/
theorem ext2_isAlt {K : ℕ} {B : Matrix (Fin K) (Fin K) R} (hB : IsAlt B) (u v : Fin K → R)
    (θ : R) : IsAlt (ext2 B u v θ) :=
  (hB.bmat _).bmat _

/-- Auxiliary for (R4) of `q_rank_two.md`: `pf(X_θ)` when the row of the index `K` is `0`
except for the entry `θ` at `K + 1`: it is `θ·pf(B)`. -/
theorem pf_ext2_zero {K : ℕ} (B : Matrix (Fin K) (Fin K) R) (hB : IsAlt B) (v : Fin K → R)
    (θ : R) : pf (K + 2) (ext2 B (fun _ => 0) v θ) = θ * pf K B := by
  rw [pf_single_row _ (ext2_isAlt hB _ v θ) (Fin.castSucc (Fin.last K)) (Fin.last K)]
  · rw [Fin.succAbove_castSucc_self, Fin.succ_last]
    have e1 : (ext2 B (fun _ => 0) v θ).submatrix
        (fun i => (Fin.castSucc (Fin.last K)).succAbove ((Fin.last K).succAbove i))
        (fun i => (Fin.castSucc (Fin.last K)).succAbove ((Fin.last K).succAbove i)) = B := by
      ext i j
      simp [ext2]
    rw [e1]
    have e2 : ext2 B (fun _ => 0) v θ (Fin.castSucc (Fin.last K)) (Fin.last (K + 1)) = θ := by
      simp [ext2]
    rw [e2]
    unfold eps
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [if_pos (by omega), show K + (K + 1) + 1 = 2 * (K + 1) by ring, pow_mul]
    simp
  · intro k hk
    rw [Fin.succAbove_castSucc_self, Fin.succ_last] at hk
    induction k using Fin.lastCases with
    | last => exact absurd rfl hk
    | cast k =>
      simp only [ext2, b1_cc]
      induction k using Fin.lastCases with
      | last => simp
      | cast k => simp

/-- Auxiliary for (R4) of `q_rank_two.md`, Step 1 of the proof: `pf(X_θ) = pf(X_0) + θ·pf(B)`
(by (A5) along the last index `K + 1`, and (A4) for the matrix whose last row is `0` except
for the entry `−1` at `K`). -/
theorem pf_ext2_theta {K : ℕ} (B : Matrix (Fin K) (Fin K) R) (hB : IsAlt B) (u v : Fin K → R)
    (θ : R) : pf (K + 2) (ext2 B u v θ) = pf (K + 2) (ext2 B u v 0) + θ * pf K B := by
  have hout : ∀ (v' : Fin K → R) (θ' : R) (i j : Fin (K + 2)), i ≠ Fin.last (K + 1) →
      j ≠ Fin.last (K + 1) → ext2 B u v' θ' i j = ext2 B u v θ i j := by
    intro v' θ' i j hi hj
    obtain ⟨i, rfl⟩ := Fin.exists_castSucc_eq.2 hi
    obtain ⟨j, rfl⟩ := Fin.exists_castSucc_eq.2 hj
    simp [ext2]
  have h1 := pf_add_row (ext2 B u v θ) (ext2 B u v 0) (ext2 B u (fun _ => 0) 1)
    (ext2_isAlt hB _ _ _) (ext2_isAlt hB _ _ _) (ext2_isAlt hB _ _ _) (Fin.last (K + 1)) θ
    (fun i j hi hj => ⟨hout _ _ i j hi hj, hout _ _ i j hi hj⟩)
    (fun k => by
      induction k using Fin.lastCases with
      | last => simp [ext2]
      | cast k =>
        simp only [ext2, b1_lc]
        induction k using Fin.lastCases with
        | last => simp
        | cast k => simp)
  rw [h1]
  congr 2
  rw [pf_single_row _ (ext2_isAlt hB _ _ _) (Fin.last (K + 1)) (Fin.last K)]
  · have e1 : (ext2 B u (fun _ => 0) 1).submatrix
        (fun i => (Fin.last (K + 1)).succAbove ((Fin.last K).succAbove i))
        (fun i => (Fin.last (K + 1)).succAbove ((Fin.last K).succAbove i)) = B := by
      ext i j
      simp [ext2, Fin.succAbove_last]
    rw [e1, Fin.succAbove_last]
    have e2 : ext2 B u (fun _ => 0) 1 (Fin.last (K + 1)) (Fin.castSucc (Fin.last K)) = -1 := by
      simp [ext2]
    rw [e2]
    unfold eps
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [if_neg (by omega), show K + 1 + K = 2 * K + 1 by ring, pow_succ, pow_mul]
    simp
  · intro k hk
    rw [Fin.succAbove_last] at hk
    induction k using Fin.lastCases with
    | last => simp [ext2]
    | cast k =>
      simp only [ext2, b1_lc]
      induction k using Fin.lastCases with
      | last => exact absurd rfl hk
      | cast k => simp

/-- Auxiliary for (R4) of `q_rank_two.md`: appending one border `w` to `B(a; c)` is bordering
`B(a; c)` once more by the column `w` extended by `0` on the borders of `c`. -/
theorem bmat_snoc {n s : ℕ} (a : Matrix (Fin n) (Fin n) R) (c : Fin s → Fin n → R)
    (w : Fin n → R) :
    bmat a (Fin.snoc (α := fun _ => Fin n → R) c w) =
      bmat (bmat a c) (fun _ : Fin 1 => Fin.addCases (motive := fun _ => R) w (fun _ => 0)) := by
  have i1 : ∀ i : Fin n, (Fin.castSucc (Fin.castAdd s i) : Fin (n + (s + 1))) =
      Fin.castAdd (s + 1) i := fun _ => rfl
  have i2 : ∀ k : Fin s, (Fin.castSucc (Fin.natAdd n k) : Fin (n + (s + 1))) =
      Fin.natAdd n (Fin.castSucc k) := fun _ => rfl
  have i3 : (Fin.last (n + s) : Fin (n + (s + 1))) = Fin.natAdd n (Fin.last s) := rfl
  refine funext fun (p : Fin (n + s + 1)) => funext fun (q : Fin (n + s + 1)) => ?_
  induction p using Fin.lastCases with
  | last =>
    induction q using Fin.lastCases with
    | last => simp only [b1_ll]; rw [i3, bmat_nn]
    | cast q =>
      induction q using Fin.addCases with
      | left j => simp only [b1_lc, Fin.addCases_left]; rw [i3, i1, bmat_nc, Fin.snoc_last]
      | right k => simp only [b1_lc, Fin.addCases_right, neg_zero]; rw [i3, i2, bmat_nn]
  | cast p =>
    induction p using Fin.addCases with
    | left i =>
      induction q using Fin.lastCases with
      | last => simp only [b1_cl, Fin.addCases_left]; rw [i3, i1, bmat_cn, Fin.snoc_last]
      | cast q =>
        induction q using Fin.addCases with
        | left j => simp only [b1_cc, bmat_cc]; rw [i1, i1, bmat_cc]
        | right k =>
          simp only [b1_cc, bmat_cn]; rw [i1, i2, bmat_cn, Fin.snoc_castSucc]
    | right k =>
      induction q using Fin.lastCases with
      | last => simp only [b1_cl, Fin.addCases_right]; rw [i3, i2, bmat_nn]
      | cast q =>
        induction q using Fin.addCases with
        | left j => simp only [b1_cc, bmat_nc]; rw [i1, i2, bmat_nc, Fin.snoc_castSucc]
        | right k' => simp only [b1_cc, bmat_nn]; rw [i2, i2, bmat_nn]

/-- Auxiliary for (R4) of `q_rank_two.md`: `B(a; c, E, O) = X_0` with `B = B(a; c)` and the
columns `E, O` extended by `0` on the borders of `c`. -/
theorem bmat_snoc_snoc {n s : ℕ} (a : Matrix (Fin n) (Fin n) R) (c : Fin s → Fin n → R)
    (E O : Fin n → R) :
    bmat a (Fin.snoc (α := fun _ => Fin n → R) (Fin.snoc (α := fun _ => Fin n → R) c E) O) =
      ext2 (bmat a c) (Fin.addCases (motive := fun _ => R) E (fun _ => 0))
        (Fin.addCases (motive := fun _ => R) O (fun _ => 0)) 0 := by
  rw [bmat_snoc, bmat_snoc]
  unfold ext2
  congr 2
  refine funext fun _ => funext fun (p : Fin (n + s + 1)) => ?_
  induction p using Fin.lastCases with
  | last =>
    rw [Fin.snoc_last]
    exact Fin.addCases_right (motive := fun _ => R) (m := n) (n := s + 1) (Fin.last s)
  | cast p =>
    rw [Fin.snoc_castSucc]
    induction p using Fin.addCases with
    | left i =>
      rw [Fin.addCases_left]
      exact Fin.addCases_left (motive := fun _ => R) (m := n) (n := s + 1) i
    | right k =>
      rw [Fin.addCases_right]
      exact Fin.addCases_right (motive := fun _ => R) (m := n) (n := s + 1) (Fin.castSucc k)

/-- **(R4)** of Theorem R in `q_rank_two.md` (rank-two update), first form: for an alternating
`a` on `Fin n`, a list `c` of `s` border columns and two columns `E, O : Fin n → R`, with
`M(i, j) := E_i·O_j − E_j·O_i`,
`bpf(a − M; c) = bpf(a; c) + bpf(a; c, E, O)`, where `(c, E, O)` is `Fin.snoc (Fin.snoc c E) O`.
There is no sign depending on `n` or `s`. -/
theorem R4 {n s : ℕ} (a : Matrix (Fin n) (Fin n) R) (ha : IsAlt a) (c : Fin s → Fin n → R)
    (E O : Fin n → R) :
    bpf (a - Matrix.of fun i j => E i * O j - E j * O i) c =
      bpf a c + bpf a (Fin.snoc (α := fun _ => Fin n → R)
        (Fin.snoc (α := fun _ => Fin n → R) c E) O) := by
  set B := bmat a c with hBdef
  have hB : IsAlt B := ha.bmat c
  set u : Fin (n + s) → R := Fin.addCases (motive := fun _ => R) E (fun _ => 0) with hu
  set v : Fin (n + s) → R := Fin.addCases (motive := fun _ => R) O (fun _ => 0) with hv
  -- Step 1
  have step1 : pf (n + s + 2) (ext2 B u v 1) =
      bpf a (Fin.snoc (α := fun _ => Fin n → R) (Fin.snoc (α := fun _ => Fin n → R) c E) O) +
        bpf a c := by
    rw [pf_ext2_theta B hB u v 1, one_mul]
    unfold bpf
    rw [bmat_snoc_snoc]
    rfl
  -- Step 2: one border shift (R2)
  set B' : Matrix (Fin (n + s)) (Fin (n + s)) R := fun p q => B p q - u p * v q + u q * v p
    with hB'
  have hB'eq : B' = bmat (a - Matrix.of fun i j => E i * O j - E j * O i) c := by
    ext p q
    induction p using Fin.addCases with
    | left i =>
      induction q using Fin.addCases with
      | left j => simp [hB', hBdef, hu, hv]; ring
      | right k => simp [hB', hBdef, hu, hv]
    | right k =>
      induction q using Fin.addCases with
      | left j => simp [hB', hBdef, hu, hv]
      | right k' => simp [hB', hBdef, hu, hv]
  have hB'alt : IsAlt B' :=
    ⟨fun p => by simp [hB', hB.1], fun p q => by simp only [hB', hB.2 p q]; ring⟩
  have hR2 := (R2 (bmat B (fun _ : Fin 1 => u)) (hB.bmat _)
    (fun _ : Fin 1 => Fin.snoc (α := fun _ => R) v 1) 0
    (Fin.snoc (α := fun _ => R) (fun p => -u p) 0)).2
  have e3 : (fun i j => bmat B (fun _ : Fin 1 => u) i j +
      Fin.snoc (α := fun _ => R) (fun p => -u p) 0 i * Fin.snoc (α := fun _ => R) v 1 j -
      Fin.snoc (α := fun _ => R) (fun p => -u p) 0 j * Fin.snoc (α := fun _ => R) v 1 i) =
      bmat B' (fun _ : Fin 1 => fun _ => 0) := by
    refine funext fun (p : Fin (n + s + 1)) => funext fun (q : Fin (n + s + 1)) => ?_
    induction p using Fin.lastCases with
    | last =>
      induction q using Fin.lastCases with
      | last => simp
      | cast q => simp
    | cast p =>
      induction q using Fin.lastCases with
      | last => simp
      | cast q => simp only [b1_cc, Fin.snoc_castSucc, hB']; ring
  calc bpf (a - Matrix.of fun i j => E i * O j - E j * O i) c = pf (n + s) B' := by
        rw [hB'eq]; rfl
    _ = pf (n + s + 2) (ext2 B' (fun _ => 0) v 1) := by rw [pf_ext2_zero B' hB'alt v 1, one_mul]
    _ = pf (n + s + 2) (ext2 B u v 1) := by
        unfold ext2
        rw [← e3]
        exact hR2
    _ = _ := step1.trans (add_comm _ _)

/-- **(R4)** of Theorem R in `q_rank_two.md` (rank-two update), second form: with the same
notation, `bpf(a + M; c) = bpf(a; c) − bpf(a; c, E, O)` (the first form for the columns `E` and
`−O`, and (B2)). -/
theorem R4' {n s : ℕ} (a : Matrix (Fin n) (Fin n) R) (ha : IsAlt a) (c : Fin s → Fin n → R)
    (E O : Fin n → R) :
    bpf (a + Matrix.of fun i j => E i * O j - E j * O i) c =
      bpf a c - bpf a (Fin.snoc (α := fun _ => Fin n → R)
        (Fin.snoc (α := fun _ => Fin n → R) c E) O) := by
  have hneg : bpf a (Fin.snoc (α := fun _ => Fin n → R)
      (Fin.snoc (α := fun _ => Fin n → R) c E) (fun i => -O i)) =
      -bpf a (Fin.snoc (α := fun _ => Fin n → R) (Fin.snoc (α := fun _ => Fin n → R) c E) O) := by
    have h := bpf_snoc_add a ha (Fin.snoc (α := fun _ => Fin n → R) c E) (fun _ => 0) O (-1)
    rw [bpf_snoc_zero _ ha] at h
    have e : (fun i => (0 : R) + -1 * O i) = fun i => -O i := by funext i; ring
    rw [e] at h
    rw [h]; ring
  have h := R4 a ha c E (fun i => -O i)
  have e : (a - Matrix.of fun i j => E i * -O j - E j * -O i) =
      a + Matrix.of fun i j => E i * O j - E j * O i := by
    ext i j; simp; ring
  rw [e, hneg] at h
  rw [h]; ring

end RankTwo
