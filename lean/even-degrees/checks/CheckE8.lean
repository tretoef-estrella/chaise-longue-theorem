import RequestProject.Pfaffian.Main

-- Check file for run E8 (q_pfaffian.md). Grepy Mandalay, 2 Oct 2026.
-- Run from proyecto_lean/output-final_aristotle:  lake env lean ../../checks/CheckE8.lean

#print Pfaffian.IsAlt
#print Pfaffian.pf
#print Pfaffian.eps
#print Pfaffian.IsMatching
#print Pfaffian.crossings
#print Pfaffian.bmat
#print Pfaffian.bpf
#print Pfaffian.ay
#print Pfaffian.Pf
#print Pfaffian.Pfe
#print ColOne.Dab

#check @Pfaffian.pf_odd
#check @Pfaffian.pf_two
#check @Pfaffian.pf_four
#check @Pfaffian.pf_eq_sum_matchings
#check @Pfaffian.pf_perm
#check @Pfaffian.pf_eq_zero_of_rows
#check @Pfaffian.pf_expand
#check @Pfaffian.pf_expand_gen
#check @Pfaffian.pf_expand_fam
#check @Pfaffian.pf_add_row
#check @Pfaffian.IsAlt.bmat
#check @Pfaffian.bpf_odd
#check @Pfaffian.bpf_eq_zero_of_lt
#check @Pfaffian.bpf_perm_vars
#check @Pfaffian.bpf_perm_borders
#check @Pfaffian.bpf_add_border
#check @Pfaffian.bpf_eq_zero_of_border_eq
#check @Pfaffian.bpf_expand_last
#check @Pfaffian.bpf_square
#check @Pfaffian.bpf_expand_var
#check @Pfaffian.bpf_expand_var_zero
#check @Pfaffian.bpf_laplace
#check @Pfaffian.Dab_self
#check @Pfaffian.ay_isAlt
#check @Pfaffian.C1
#check @Pfaffian.C2
#check @Pfaffian.C3
#check @Pfaffian.C4_eq_zero
#check @Pfaffian.C4
#check @Pfaffian.C5
#check @Pfaffian.C6
#check @Pfaffian.C6_e

#print axioms Pfaffian.pf_odd
#print axioms Pfaffian.pf_two
#print axioms Pfaffian.pf_four
#print axioms Pfaffian.pf_eq_sum_matchings
#print axioms Pfaffian.pf_perm
#print axioms Pfaffian.pf_eq_zero_of_rows
#print axioms Pfaffian.pf_expand
#print axioms Pfaffian.pf_expand_gen
#print axioms Pfaffian.pf_expand_fam
#print axioms Pfaffian.pf_add_row
#print axioms Pfaffian.IsAlt.bmat
#print axioms Pfaffian.bpf_odd
#print axioms Pfaffian.bpf_eq_zero_of_lt
#print axioms Pfaffian.bpf_perm_vars
#print axioms Pfaffian.bpf_perm_borders
#print axioms Pfaffian.bpf_add_border
#print axioms Pfaffian.bpf_eq_zero_of_border_eq
#print axioms Pfaffian.bpf_expand_last
#print axioms Pfaffian.bpf_square
#print axioms Pfaffian.bpf_expand_var
#print axioms Pfaffian.bpf_expand_var_zero
#print axioms Pfaffian.bpf_laplace
#print axioms Pfaffian.Dab_self
#print axioms Pfaffian.ay_isAlt
#print axioms Pfaffian.C1
#print axioms Pfaffian.C2
#print axioms Pfaffian.C3
#print axioms Pfaffian.C4_eq_zero
#print axioms Pfaffian.C4
#print axioms Pfaffian.C5
#print axioms Pfaffian.C6
#print axioms Pfaffian.C6_e

-- Statements restated by hand, with the definitions unfolded where it matters
-- (they must typecheck as written).

-- (A3): equal rows, no hypothesis on the ring; «alternating» spelled out.
example {R : Type*} [CommRing R] {m : ℕ} (A : Matrix (Fin m) (Fin m) R)
    (h0 : ∀ i, A i i = 0) (h1 : ∀ i j, A j i = -A i j) {x z : Fin m} (hxz : x ≠ z)
    (hrow : ∀ k, A x k = A z k) : Pfaffian.pf m A = 0 :=
  Pfaffian.pf_eq_zero_of_rows A ⟨h0, h1⟩ hxz hrow

-- (A1): the sum over perfect matchings.
open Pfaffian Finset in
example {R : Type*} [CommRing R] (m : ℕ) (A : Matrix (Fin m) (Fin m) R) :
    pf m A = ∑ π ∈ univ.filter (fun π : Fin m → Fin m => IsMatching π),
      (-1) ^ (crossings π) * ∏ x ∈ univ.filter (fun x => x < π x), A x (π x) :=
  pf_eq_sum_matchings m A

-- (B3): as many borders as variables, with bpf unfolded.
example {R : Type*} [CommRing R] {s : ℕ} (a : Matrix (Fin s) (Fin s) R) (ha : Pfaffian.IsAlt a)
    (c : Fin s → Fin s → R) :
    Pfaffian.pf (s + s) (Pfaffian.bmat a c) =
      (-1) ^ (s * (s - 1) / 2) * (Matrix.of fun i k => c k i).det :=
  Pfaffian.bpf_square a ha c

-- (B4): expansion along a variable (n + 1 variables, s + 1 borders).
example {R : Type*} [CommRing R] {n s : ℕ} (a : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (ha : Pfaffian.IsAlt a) (c : Fin (s + 1) → Fin (n + 1) → R) (x : Fin (n + 1)) :
    Pfaffian.bpf a c = (-1) ^ ((x : ℕ) + (n + 1) + (s + 1)) *
        Pfaffian.bpf (a.submatrix x.succAbove x.succAbove)
          (Fin.snoc (α := fun _ => Fin n → R) (fun k i => c k (x.succAbove i))
            (fun i => a x (x.succAbove i)))
      + ∑ k : Fin (s + 1), (-1) ^ ((x : ℕ) + (n + 1) + (k : ℕ) + 1) * c k x *
        Pfaffian.bpf (a.submatrix x.succAbove x.succAbove)
          (fun j i => c (k.succAbove j) (x.succAbove i)) :=
  Pfaffian.bpf_expand_var a ha c x

-- (B5): Laplace, with any proof of the cardinality of the complement.
example {R : Type*} [CommRing R] {n s : ℕ} (a : Matrix (Fin n) (Fin n) R) (ha : Pfaffian.IsAlt a)
    (c : Fin s → Fin n → R)
    (hc : ∀ S : {S : Finset (Fin n) // S.card = s}, (S.1ᶜ).card = n - s) :
    Pfaffian.bpf a c = (-1) ^ (s * (s - 1) / 2) * ∑ S : {S : Finset (Fin n) // S.card = s},
      (-1) ^ ((∑ i ∈ S.1, (i : ℕ)) - s * (s - 1) / 2) *
        (Matrix.of fun i k => c k (S.1.orderEmbOfFin S.2 i)).det *
        Pfaffian.pf (n - s) (a.submatrix (S.1ᶜ.orderEmbOfFin (hc S)) (S.1ᶜ.orderEmbOfFin (hc S))) :=
  Pfaffian.bpf_laplace a ha c

-- (C5): the Vandermonde, with D^- = ColOne.Dab r written out.
open Finset in
example {A : Type*} [CommRing A] {r : ℕ} (hr : Odd r) {s : ℕ} (y : Fin s → A) :
    Pfaffian.bpf (fun i j => ColOne.Dab r (y i) (y j) : Matrix (Fin s) (Fin s) A)
        (fun (k : Fin s) (i : Fin s) => y i ^ (k : ℕ)) =
      (-1) ^ (s * (s - 1) / 2) * ∏ i : Fin s, ∏ j ∈ Ioi i, (y j - y i) :=
  Pfaffian.C5 hr y
