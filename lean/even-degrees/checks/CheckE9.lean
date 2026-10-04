import RequestProject.RankTwo.Main

-- Check file for run E9 (q_rank_two.md). Grepy Mandalay, 2 Oct 2026.
-- Run from proyecto_lean/output-final_aristotle:  lake env lean ../../checks/CheckE9.lean
-- Rule (third failure, E2/E6/E8): every hand-restated example carries every type written out.

#print RankTwo.elemOp
#print RankTwo.ext2
#print RankTwo.omega
#print RankTwo.Wm
#print RankTwo.Lm
#print RankTwo.Hm
#print RankTwo.Ev
#print RankTwo.Od
#print Pfaffian.Pf
#print Pfaffian.ay
#print ColOne.Dab

#check @RankTwo.elemOp_isAlt
#check @RankTwo.R1
#check @RankTwo.R2
#check @RankTwo.R3_pf
#check @RankTwo.R3_bpf
#check @RankTwo.R4
#check @RankTwo.R4'
#check @RankTwo.R5_pf
#check @RankTwo.R5_bpf
#check @RankTwo.omega_swap
#check @RankTwo.omega_self
#check @RankTwo.Wm_isAlt
#check @RankTwo.Lm_isAlt
#check @RankTwo.Hm_isAlt
#check @RankTwo.S1
#check @RankTwo.S1_Wm
#check @RankTwo.S1_top
#check @RankTwo.S3
#check @RankTwo.S2_scalar
#check @RankTwo.S2
#check @RankTwo.S4_i
#check @RankTwo.S4_ii
#check @RankTwo.S5a
#check @RankTwo.S5a_of_le
#check @RankTwo.S5a_of_ge
#check @RankTwo.S5b
#check @RankTwo.S5b_of_le
#check @RankTwo.S5b_of_gt

#print axioms RankTwo.elemOp_isAlt
#print axioms RankTwo.R1
#print axioms RankTwo.R2
#print axioms RankTwo.R3_pf
#print axioms RankTwo.R3_bpf
#print axioms RankTwo.R4
#print axioms RankTwo.R4'
#print axioms RankTwo.R5_pf
#print axioms RankTwo.R5_bpf
#print axioms RankTwo.omega_swap
#print axioms RankTwo.omega_self
#print axioms RankTwo.Wm_isAlt
#print axioms RankTwo.Lm_isAlt
#print axioms RankTwo.Hm_isAlt
#print axioms RankTwo.S1
#print axioms RankTwo.S1_Wm
#print axioms RankTwo.S1_top
#print axioms RankTwo.S3
#print axioms RankTwo.S2_scalar
#print axioms RankTwo.S2
#print axioms RankTwo.S4_i
#print axioms RankTwo.S4_ii
#print axioms RankTwo.S5a
#print axioms RankTwo.S5a_of_le
#print axioms RankTwo.S5a_of_ge
#print axioms RankTwo.S5b
#print axioms RankTwo.S5b_of_le
#print axioms RankTwo.S5b_of_gt

-- Hand-restated examples (the statements as the auditor reads them in q_rank_two.md).

-- (R1): both the row and the column of w change; x ≠ w.
example {R : Type*} [CommRing R] {m : ℕ} (A : Matrix (Fin m) (Fin m) R) (hA : Pfaffian.IsAlt A)
    (x : Fin m) (w : Fin m) (hxw : x ≠ w) (lam : R) :
    Pfaffian.pf m (fun (i : Fin m) (j : Fin m) =>
        A i j + lam * ((if i = w then A x j else 0) + (if j = w then A i x else 0))) =
      Pfaffian.pf m A :=
  (RankTwo.R1 A hA hxw lam).2

-- (R2): border shift along the border k of the list.
example {R : Type*} [CommRing R] {n s : ℕ} (a : Matrix (Fin n) (Fin n) R) (ha : Pfaffian.IsAlt a)
    (c : Fin s → Fin n → R) (k : Fin s) (lam : Fin n → R) :
    Pfaffian.bpf (fun (i : Fin n) (j : Fin n) => a i j + lam i * c k j - lam j * c k i) c =
      Pfaffian.bpf a c :=
  (RankTwo.R2 a ha c k lam).2

-- (R3): homogeneity, n = s + 2κ.
example {R : Type*} [CommRing R] {n s : ℕ} (κ : ℕ) (hn : n = s + 2 * κ) (t : R)
    (a : Matrix (Fin n) (Fin n) R) (ha : Pfaffian.IsAlt a) (c : Fin s → Fin n → R) :
    Pfaffian.bpf (t • a) c = t ^ κ * Pfaffian.bpf a c :=
  RankTwo.R3_bpf κ hn t a ha c

-- (R4): the rank-two update, borders (c, E, O) in this order, sign + for a − M, no other factor;
-- the left side with bpf unfolded.
example {R : Type*} [CommRing R] {n s : ℕ} (a : Matrix (Fin n) (Fin n) R) (ha : Pfaffian.IsAlt a)
    (c : Fin s → Fin n → R) (E : Fin n → R) (O : Fin n → R) :
    Pfaffian.pf (n + s)
        (Pfaffian.bmat (a - Matrix.of fun (i : Fin n) (j : Fin n) => E i * O j - E j * O i) c) =
      Pfaffian.bpf a c +
        Pfaffian.bpf a (Fin.snoc (α := fun _ => Fin n → R)
          (Fin.snoc (α := fun _ => Fin n → R) c E) O) :=
  RankTwo.R4 a ha c E O

-- (R4), second form: sign − for a + M.
example {R : Type*} [CommRing R] {n s : ℕ} (a : Matrix (Fin n) (Fin n) R) (ha : Pfaffian.IsAlt a)
    (c : Fin s → Fin n → R) (E : Fin n → R) (O : Fin n → R) :
    Pfaffian.bpf (a + Matrix.of fun (i : Fin n) (j : Fin n) => E i * O j - E j * O i) c =
      Pfaffian.bpf a c -
        Pfaffian.bpf a (Fin.snoc (α := fun _ => Fin n → R)
          (Fin.snoc (α := fun _ => Fin n → R) c E) O) :=
  RankTwo.R4' a ha c E O

-- (R5): the degrees are bounds, the coefficient is at κ·d + Σ d_k.
example {R : Type*} [CommRing R] (κ : ℕ) (d : ℕ) {n s : ℕ} (hn : n = s + 2 * κ)
    (a : Matrix (Fin n) (Fin n) (Polynomial R)) (ha : Pfaffian.IsAlt a)
    (c : Fin s → Fin n → Polynomial R) (dk : Fin s → ℕ)
    (hd : ∀ (i : Fin n) (j : Fin n), (a i j).natDegree ≤ d)
    (hc : ∀ (k : Fin s) (i : Fin n), (c k i).natDegree ≤ dk k) :
    (Pfaffian.bpf a c).coeff (κ * d + ∑ k : Fin s, dk k) =
      Pfaffian.bpf (fun (i : Fin n) (j : Fin n) => (a i j).coeff d)
        (fun (k : Fin s) (i : Fin n) => (c k i).coeff (dk k)) :=
  (RankTwo.R5_bpf κ d hn a ha c dk hd hc).2

-- The definition of omega: both conditions.
example {A : Type*} [CommRing A] (r : ℕ) (s : ℕ) (a : A) (b : A) :
    RankTwo.omega r s a b =
      ∑ u ∈ Finset.range r, if u ≤ s ∧ s - u < r then (-1) ^ u * a ^ u * b ^ (s - u) else 0 :=
  rfl

-- (S1): omega_{r−2} = D^− = ColOne.Dab r, r = 2h + 1.
example {A : Type*} [CommRing A] {h : ℕ} (hh : 1 ≤ h) (a : A) (b : A) :
    RankTwo.omega (2 * h + 1) (2 * h - 1) a b = ColOne.Dab (2 * h + 1) a b :=
  RankTwo.S1 hh a b

-- (S3), the statement of q_rank_two.md (special case of Aristotle's more general form):
-- a^r = 0, b^r = 0, i odd, 1 ≤ i ≤ r − 2; omega_{r−1+i}(a, b) = b^i · D(a, b), D = Dab (r+1).
-- Here r = 2h + 1, so r − 1 + i = 2h + i and r + 1 = 2h + 2 (written so, to need no arithmetic).
example {A : Type*} [CommRing A] (h : ℕ) (i : ℕ) (a : A) (b : A)
    (_ha : a ^ (2 * h + 1) = 0) (hb : b ^ (2 * h + 1) = 0) (_hi : Odd i) (_h1 : 1 ≤ i)
    (_h2 : i ≤ 2 * h + 1 - 2) :
    RankTwo.omega (2 * h + 1) (2 * h + i) a b = b ^ i * ColOne.Dab (2 * h + 2) a b :=
  RankTwo.S3 h i a b hb

-- (S2): the key fact, with Lm, Hm, Ev, Od written out.
example {A : Type*} [CommRing A] (h : ℕ) {n : ℕ} (y : Fin n → A) (i : Fin n) (j : Fin n) :
    (∑ σ ∈ Finset.range h, (Polynomial.X : Polynomial A) ^ σ *
          Polynomial.C (RankTwo.omega (2 * h + 1) (2 * σ + 1) (y i) (y j))) +
        (Polynomial.X : Polynomial A) ^ h *
          (∑ τ ∈ Finset.range h, (Polynomial.X : Polynomial A) ^ τ *
            Polynomial.C (RankTwo.omega (2 * h + 1) (2 * (h + τ) + 1) (y i) (y j))) =
      (∑ α ∈ Finset.range (h + 1), (Polynomial.X : Polynomial A) ^ α *
            Polynomial.C (y i ^ (2 * α))) *
          (∑ β ∈ Finset.range h, (Polynomial.X : Polynomial A) ^ β *
            Polynomial.C (y j ^ (2 * β + 1))) -
        (∑ α ∈ Finset.range (h + 1), (Polynomial.X : Polynomial A) ^ α *
            Polynomial.C (y j ^ (2 * α))) *
          (∑ β ∈ Finset.range h, (Polynomial.X : Polynomial A) ^ β *
            Polynomial.C (y i ^ (2 * β + 1))) :=
  RankTwo.S2 h y i j

-- (S4)(i).
example {A : Type*} [CommRing A] (h : ℕ) {n s : ℕ} (y : Fin n → A)
    (c : Fin s → Fin n → Polynomial A) :
    Pfaffian.bpf (RankTwo.Lm h y) c =
      Pfaffian.bpf ((-(Polynomial.X : Polynomial A) ^ h) • RankTwo.Hm h y) c -
        Pfaffian.bpf ((-(Polynomial.X : Polynomial A) ^ h) • RankTwo.Hm h y)
          (Fin.snoc (α := fun _ => Fin n → Polynomial A)
            (Fin.snoc (α := fun _ => Fin n → Polynomial A) c (RankTwo.Ev h y))
            (RankTwo.Od h y)) :=
  RankTwo.S4_i h y c

-- (S4)(ii).
example {A : Type*} [CommRing A] (h : ℕ) {n s : ℕ} (y : Fin n → A)
    (c : Fin s → Fin n → Polynomial A) :
    Pfaffian.bpf (RankTwo.Lm h y)
        (Fin.snoc (α := fun _ => Fin n → Polynomial A) c (RankTwo.Ev h y)) =
      Pfaffian.bpf ((-(Polynomial.X : Polynomial A) ^ h) • RankTwo.Hm h y)
        (Fin.snoc (α := fun _ => Fin n → Polynomial A) c (RankTwo.Ev h y)) :=
  RankTwo.S4_ii h y c

-- (S5)(a), t ≤ h − 1: the left side with Pf and a_y unfolded (D^− = ColOne.Dab (2h+1)).
example {A : Type*} [CommRing A] {h : ℕ} (hh : 1 ≤ h) {n s : ℕ} (t : ℕ)
    (hn : n = s + 2 * (t + 1)) (ht : t + 1 ≤ h) (y : Fin n → A) (c : Fin s → Fin n → A) :
    Pfaffian.bpf (fun (i : Fin n) (j : Fin n) => ColOne.Dab (2 * h + 1) (y i) (y j) :
        Matrix (Fin n) (Fin n) A) c =
      (-1) ^ (t + 1) *
        (Pfaffian.bpf (RankTwo.Hm h y)
          (Fin.snoc (α := fun _ => Fin n → Polynomial A)
            (Fin.snoc (α := fun _ => Fin n → Polynomial A)
              (fun (k : Fin s) (i : Fin n) => Polynomial.C (c k i)) (RankTwo.Ev h y))
            (RankTwo.Od h y))).coeff (h - 1 - t) :=
  RankTwo.S5a_of_le hh t hn ht y c

-- (S5)(a), t ≥ h: zero.
example {A : Type*} [CommRing A] {h : ℕ} (hh : 1 ≤ h) {n s : ℕ} (t : ℕ)
    (hn : n = s + 2 * (t + 1)) (ht : h ≤ t) (y : Fin n → A) (c : Fin s → Fin n → A) :
    Pfaffian.bpf (fun (i : Fin n) (j : Fin n) => ColOne.Dab (2 * h + 1) (y i) (y j) :
        Matrix (Fin n) (Fin n) A) c = 0 :=
  RankTwo.S5a_of_ge hh t hn ht y c

-- (S5)(b), t ≤ h: last border y^{2h}.
example {A : Type*} [CommRing A] {h : ℕ} (hh : 1 ≤ h) {n s : ℕ} (t : ℕ)
    (hn : n = s + 1 + 2 * t) (ht : t ≤ h) (y : Fin n → A) (c : Fin s → Fin n → A) :
    Pfaffian.bpf (fun (i : Fin n) (j : Fin n) => ColOne.Dab (2 * h + 1) (y i) (y j) :
        Matrix (Fin n) (Fin n) A)
        (Fin.snoc (α := fun _ => Fin n → A) c (fun (i : Fin n) => y i ^ (2 * h))) =
      (-1) ^ t *
        (Pfaffian.bpf (RankTwo.Hm h y)
          (Fin.snoc (α := fun _ => Fin n → Polynomial A)
            (fun (k : Fin s) (i : Fin n) => Polynomial.C (c k i)) (RankTwo.Ev h y))).coeff
          (h - t) :=
  RankTwo.S5b_of_le hh t hn ht y c

-- (S5)(b), t > h: zero.
example {A : Type*} [CommRing A] {h : ℕ} (hh : 1 ≤ h) {n s : ℕ} (t : ℕ)
    (hn : n = s + 1 + 2 * t) (ht : h < t) (y : Fin n → A) (c : Fin s → Fin n → A) :
    Pfaffian.bpf (fun (i : Fin n) (j : Fin n) => ColOne.Dab (2 * h + 1) (y i) (y j) :
        Matrix (Fin n) (Fin n) A)
        (Fin.snoc (α := fun _ => Fin n → A) c (fun (i : Fin n) => y i ^ (2 * h))) = 0 :=
  RankTwo.S5b_of_gt hh t hn ht y c
