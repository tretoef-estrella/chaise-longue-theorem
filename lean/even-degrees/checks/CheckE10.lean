import RequestProject.Membership.Main

-- Check file for run E10 (q_membership.md). Grepy Mandalay, 2 Oct 2026.
-- Run from proyecto_lean/output-final_aristotle:  lake env lean ../../checks/CheckE10.lean
-- Rule: every hand-restated example carries every type written out; the ideals are written
-- unfolded (Ideal.span of the generators), so that the definitions themselves are checked.

#print Membership.PolyIn
#print Membership.pairDy
#print Membership.DPy
#print Membership.UB
#print Membership.U
#print Membership.pairsOf
#print Tight.vand
#print Odd3.IsPairs
#print Odd3.supp
#print Pfaffian.Pfe

#check @Membership.V1
#check @Membership.vand_map
#check @Membership.V2
#check @Membership.polyIn_pow
#check @Membership.polyIn_Ev
#check @Membership.polyIn_Od
#check @Membership.V3
#check @Membership.H1
#check @Membership.H2
#check @Membership.H3
#check @Membership.pairDy_pair
#check @Membership.isPairs_pairsOf
#check @Membership.supp_pairsOf
#check @Membership.DPy_pairsOf
#check @Membership.pairDy_map
#check @Membership.U_le_UB
#check @Membership.M1
#check @Membership.M2a
#check @Membership.M2b
#check @Membership.M3_pos
#check @Membership.M3_zero
#check @Membership.M4a
#check @Membership.M4b

#print axioms Membership.V1
#print axioms Membership.vand_map
#print axioms Membership.V2
#print axioms Membership.polyIn_pow
#print axioms Membership.polyIn_Ev
#print axioms Membership.polyIn_Od
#print axioms Membership.V3
#print axioms Membership.H1
#print axioms Membership.H2
#print axioms Membership.H3
#print axioms Membership.pairDy_pair
#print axioms Membership.isPairs_pairsOf
#print axioms Membership.supp_pairsOf
#print axioms Membership.DPy_pairsOf
#print axioms Membership.pairDy_map
#print axioms Membership.U_le_UB
#print axioms Membership.M1
#print axioms Membership.M2a
#print axioms Membership.M2b
#print axioms Membership.M3_pos
#print axioms Membership.M3_zero
#print axioms Membership.M4a
#print axioms Membership.M4b

-- Hand-restated examples (the statements as the auditor reads them in q_membership.md).

-- (V1): any commutative ring, no hypothesis.
example {R : Type*} [CommRing R] {m : ℕ} (x : Fin m → R) (p : Fin m → Polynomial R) :
    (∏ i : Fin m, ∏ j ∈ Finset.Ioi i, (x j - x i)) ∣
      (Matrix.of fun (i : Fin m) (k : Fin m) => Polynomial.eval (x i) (p k)).det :=
  Membership.V1 x p

-- (V2)
example {A : Type*} [CommRing A] {n m : ℕ} (y : Fin n → A) (S : Finset (Fin n))
    (hS : S.card = m) :
    Tight.vand y S = ∏ i : Fin m, ∏ j ∈ Finset.Ioi i,
      (y (S.orderEmbOfFin hS j) - y (S.orderEmbOfFin hS i)) :=
  Membership.V2 y S hS

-- (V3) with "polynomial in y" written out.
example {A : Type*} [CommRing A] {n m : ℕ} (y : Fin n → A) (S : Finset (Fin n))
    (hS : S.card = m) (c' : Fin m → Fin n → Polynomial A)
    (hc : ∀ k : Fin m, ∃ P : Polynomial (Polynomial A),
      ∀ i : Fin n, c' k i = Polynomial.eval (Polynomial.C (y i)) P) :
    Polynomial.C (Tight.vand y S) ∣
      (Matrix.of fun (i : Fin m) (k : Fin m) => c' k (S.orderEmbOfFin hS i)).det :=
  Membership.V3 y S hS c' hc

-- (H1): only y j ^ (2h+1) = 0 is used; Od at the second index.
example {A : Type*} [CommRing A] (h : ℕ) {n : ℕ} (y : Fin n → A) (i : Fin n) (j : Fin n)
    (hj : y j ^ (2 * h + 1) = 0) :
    RankTwo.Hm h y i j =
      Polynomial.C (ColOne.Dab (2 * h + 2) (y i) (y j)) * RankTwo.Od h y j :=
  Membership.H1 h y i j hj

-- (H3): sign (-1)^crossings, D at (x, π x) with x < π x, Od at the larger element π x.
example {A : Type*} [CommRing A] (h : ℕ) {m : ℕ} (z : Fin m → A)
    (hz : ∀ i : Fin m, z i ^ (2 * h + 1) = 0) :
    Pfaffian.pf m (RankTwo.Hm h z) =
      ∑ π ∈ Finset.univ.filter (fun π : Fin m → Fin m => Pfaffian.IsMatching π),
        (-1 : Polynomial A) ^ (Pfaffian.crossings π) *
          Polynomial.C (∏ x ∈ Finset.univ.filter (fun x : Fin m => x < π x),
            ColOne.Dab (2 * h + 2) (z x) (z (π x))) *
          ∏ x ∈ Finset.univ.filter (fun x : Fin m => x < π x), RankTwo.Od h z (π x) :=
  Membership.H3 h z hz

-- The definitions, unfolded: IsPairs, supp, and the ideal UB.
example {m : ℕ} (P : Finset (Finset (Fin m))) :
    Odd3.IsPairs P ↔
      ((∀ e ∈ P, e.card = 2) ∧ (P : Set (Finset (Fin m))).PairwiseDisjoint id) :=
  Iff.rfl

example {m : ℕ} (P : Finset (Finset (Fin m))) : Odd3.supp P = P.sup id := rfl

example {A : Type*} [CommRing A] (r p : ℕ) {n : ℕ} (y : Fin n → A) (B : Finset (Fin n)) :
    Membership.UB r p y B =
      Ideal.span {g : A | ∃ (S : Finset (Fin n)) (P : Finset (Finset (Fin n))),
        S ⊆ B ∧ S.card = p ∧ Odd3.IsPairs P ∧ Odd3.supp P = B \ S ∧
        g = Tight.vand y S * ∏ e ∈ P,
          (if hne : e.Nonempty then ColOne.Dab (r + 1) (y (e.min' hne)) (y (e.max' hne))
           else 1)} :=
  rfl

example {A : Type*} [CommRing A] (r p : ℕ) {n : ℕ} (y : Fin n → A) :
    Membership.U r p y = Membership.UB r p y Finset.univ := rfl

-- (M2)(a): n = s + 2(t+1), ideal with s + 2 fixed points, written unfolded.
example {A : Type*} [CommRing A] {h : ℕ} (hh : 1 ≤ h) {n s : ℕ} (t : ℕ)
    (hn : n = s + 2 * (t + 1)) (y : Fin n → A) (hy : ∀ i : Fin n, y i ^ (2 * h + 1) = 0)
    (e : Fin s → ℕ) :
    Pfaffian.Pf (2 * h + 1) y (fun (k : Fin s) (i : Fin n) => y i ^ e k) ∈
      Ideal.span {g : A | ∃ (S : Finset (Fin n)) (P : Finset (Finset (Fin n))),
        S ⊆ Finset.univ ∧ S.card = s + 2 ∧ Odd3.IsPairs P ∧
        Odd3.supp P = Finset.univ \ S ∧
        g = Tight.vand y S * ∏ e ∈ P,
          (if hne : e.Nonempty then
            ColOne.Dab (2 * h + 1 + 1) (y (e.min' hne)) (y (e.max' hne))
           else 1)} :=
  Membership.M2a hh t hn y hy e

-- (M2)(b): n = s + 1 + 2t, last border y^(2h) appended by Fin.snoc, ideal with s + 1.
example {A : Type*} [CommRing A] {h : ℕ} (hh : 1 ≤ h) {n s : ℕ} (t : ℕ)
    (hn : n = s + 1 + 2 * t) (y : Fin n → A) (hy : ∀ i : Fin n, y i ^ (2 * h + 1) = 0)
    (e : Fin s → ℕ) :
    Pfaffian.Pf (2 * h + 1) y
        (Fin.snoc (α := fun _ => Fin n → A) (fun (k : Fin s) (i : Fin n) => y i ^ e k)
          (fun i : Fin n => y i ^ (2 * h))) ∈
      Membership.UB (2 * h + 1) (s + 1) y Finset.univ :=
  Membership.M2b hh t hn y hy e

-- (M3), the paper's Lemma 8.7, case ℓ = l + 1 ≥ 1: n = ℓ + 1 + 2t, exponents 0..ℓ-2.
example {A : Type*} [CommRing A] {h : ℕ} (hh : 1 ≤ h) {n l : ℕ} (t : ℕ)
    (hn : n = (l + 1) + 1 + 2 * t) (y : Fin n → A)
    (hy : ∀ i : Fin n, y i ^ (2 * h + 1) = 0) :
    Pfaffian.Pfe (2 * h + 1) y (fun k : Fin l => (k : ℕ)) ∈
      Membership.UB (2 * h + 1) ((l + 1) + 1) y Finset.univ :=
  Membership.M3_pos hh t (by omega) y hy

-- (M3), case ℓ = 0: n = 1 + 2t, the single border y^(r-1) = y^(2h).
example {A : Type*} [CommRing A] {h : ℕ} (hh : 1 ≤ h) {n : ℕ} (t : ℕ) (hn : n = 1 + 2 * t)
    (y : Fin n → A) (hy : ∀ i : Fin n, y i ^ (2 * h + 1) = 0) :
    Pfaffian.Pf (2 * h + 1) y (fun (_ : Fin 1) (i : Fin n) => y i ^ (2 * h)) ∈
      Membership.UB (2 * h + 1) 1 y Finset.univ :=
  Membership.M3_zero hh t hn y hy

-- (M4)(a): on a set B of indices of a larger ring; the ideal is UB of the big ring's y.
example {A : Type*} [CommRing A] {h : ℕ} (hh : 1 ≤ h) {m n s : ℕ} (t : ℕ) (y : Fin m → A)
    (hy : ∀ i : Fin m, y i ^ (2 * h + 1) = 0) (B : Finset (Fin m)) (hB : B.card = n)
    (hn : n = s + 2 * (t + 1)) (e : Fin s → ℕ) :
    Pfaffian.Pfe (2 * h + 1) (fun i : Fin n => y (B.orderEmbOfFin hB i)) e ∈
      Ideal.span {g : A | ∃ (S : Finset (Fin m)) (P : Finset (Finset (Fin m))),
        S ⊆ B ∧ S.card = s + 2 ∧ Odd3.IsPairs P ∧ Odd3.supp P = B \ S ∧
        g = Tight.vand y S * ∏ e ∈ P,
          (if hne : e.Nonempty then
            ColOne.Dab (2 * h + 1 + 1) (y (e.min' hne)) (y (e.max' hne))
           else 1)} :=
  Membership.M4a hh t y hy B hB hn e

-- (M4)(b)
example {A : Type*} [CommRing A] {h : ℕ} (hh : 1 ≤ h) {m n s : ℕ} (t : ℕ) (y : Fin m → A)
    (hy : ∀ i : Fin m, y i ^ (2 * h + 1) = 0) (B : Finset (Fin m)) (hB : B.card = n)
    (hn : n = s + 1 + 2 * t) (e : Fin s → ℕ) :
    Pfaffian.Pf (2 * h + 1) (fun i : Fin n => y (B.orderEmbOfFin hB i))
        (Fin.snoc (α := fun _ => Fin n → A)
          (fun (k : Fin s) (i : Fin n) => y (B.orderEmbOfFin hB i) ^ e k)
          (fun i : Fin n => y (B.orderEmbOfFin hB i) ^ (2 * h))) ∈
      Membership.UB (2 * h + 1) (s + 1) y B :=
  Membership.M4b hh t y hy B hB hn e
