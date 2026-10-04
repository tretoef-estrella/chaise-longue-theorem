import RequestProject.OddPatterns.Main

-- Check file for run E11 (q_oddbox_patterns.md). Grepy Mandalay, 2-3 Oct 2026.
-- Run from proyecto_lean/output-final_aristotle:  lake env lean ../../checks/CheckE11.lean
-- Rule: every hand-restated example carries every type written out; the definitions are
-- written unfolded (rfl), so that the definitions themselves are checked.

set_option synthInstance.maxHeartbeats 200000

#print OddPatterns.mPf
#print OddPatterns.markedPf
#print OddPatterns.MarkedPattern
#print OddPatterns.MarkedPattern.prod
#print OddPatterns.VS
#print OddPatterns.VSAll
#print OddPatterns.MarkedPattern.relabel
#print Tight.VLam
#print Tight.PM
#print OddShapes.comp
#print Membership.UB

#check @OddPatterns.odd_two_mul_add_one
#check @OddPatterns.A1
#check @OddPatterns.A2
#check @OddPatterns.A3
#check @OddPatterns.A4
#check @OddPatterns.A5
#check @OddPatterns.A6
#check @OddPatterns.A7
#check @OddPatterns.map_pf
#check @OddPatterns.map_mPf
#check @OddPatterns.mPf_cast
#check @OddPatterns.card_sup_of_disjoint
#check @OddPatterns.colLen_one
#check @OddPatterns.sum_colLen_two
#check @OddPatterns.B3
#check @OddPatterns.B4_tight
#check @OddPatterns.B4_marked
#check @OddPatterns.B5_mono
#check @OddPatterns.B5_empty
#check @OddPatterns.B5_no_marked
#check @OddPatterns.VLam_comp_false_singleton_true
#check @OddPatterns.comp_singleton_true
#check @OddPatterns.B6_empty_prod
#check @OddPatterns.B6_empty
#check @OddPatterns.B6_one_prod
#check @OddPatterns.B6_one
#check @OddPatterns.PM_sign_mul
#check @OddPatterns.C1
#check @OddPatterns.relabel_markedProd_PM
#check @OddPatterns.C2
#check @OddPatterns.exists_marked_of_eq
#check @OddPatterns.map_relabel_marked
#check @OddPatterns.C3
#check @OddPatterns.C3_all
#check @OddPatterns.D1
#check @OddPatterns.D2_DPy
#check @OddPatterns.D2_vand
#check @OddPatterns.D3

#print axioms OddPatterns.odd_two_mul_add_one
#print axioms OddPatterns.A1
#print axioms OddPatterns.A2
#print axioms OddPatterns.A3
#print axioms OddPatterns.A4
#print axioms OddPatterns.A5
#print axioms OddPatterns.A6
#print axioms OddPatterns.A7
#print axioms OddPatterns.map_pf
#print axioms OddPatterns.map_mPf
#print axioms OddPatterns.mPf_cast
#print axioms OddPatterns.card_sup_of_disjoint
#print axioms OddPatterns.colLen_one
#print axioms OddPatterns.sum_colLen_two
#print axioms OddPatterns.B3
#print axioms OddPatterns.B4_tight
#print axioms OddPatterns.B4_marked
#print axioms OddPatterns.B5_mono
#print axioms OddPatterns.B5_empty
#print axioms OddPatterns.B5_no_marked
#print axioms OddPatterns.VLam_comp_false_singleton_true
#print axioms OddPatterns.comp_singleton_true
#print axioms OddPatterns.B6_empty_prod
#print axioms OddPatterns.B6_empty
#print axioms OddPatterns.B6_one_prod
#print axioms OddPatterns.B6_one
#print axioms OddPatterns.PM_sign_mul
#print axioms OddPatterns.C1
#print axioms OddPatterns.relabel_markedProd_PM
#print axioms OddPatterns.C2
#print axioms OddPatterns.exists_marked_of_eq
#print axioms OddPatterns.map_relabel_marked
#print axioms OddPatterns.C3
#print axioms OddPatterns.C3_all
#print axioms OddPatterns.D1
#print axioms OddPatterns.D2_DPy
#print axioms OddPatterns.D2_vand
#print axioms OddPatterns.D3

-- Hand-restated examples (the statements as the auditor reads them in q_oddbox_patterns.md).

-- (A0), unfolded: for l = 0 ONE border with exponent 2h; for l >= 1 the l - 1 borders with
-- exponents 0, ..., l - 2; r = 2h + 1.
example {A : Type*} [CommRing A] (h : ℕ) (l : ℕ) {n : ℕ} (z : Fin n → A) :
    OddPatterns.mPf h l z =
      if l = 0 then Pfaffian.Pfe (2 * h + 1) z (fun _ : Fin 1 => 2 * h)
      else Pfaffian.Pfe (2 * h + 1) z (fun k : Fin (l - 1) => (k : ℕ)) :=
  rfl

-- (A1)
example {A : Type*} [CommRing A] (h : ℕ) (z : Fin 1 → A) :
    OddPatterns.mPf h 0 z = z 0 ^ (2 * h) :=
  OddPatterns.A1 h z

-- (A2)
example {A : Type*} [CommRing A] (h : ℕ) (z : Fin 2 → A) :
    OddPatterns.mPf h 1 z = ColOne.Dab (2 * h + 1) (z 0) (z 1) :=
  OddPatterns.A2 h z

-- (A3): signs + - +, the power on the index left out.
example {A : Type*} [CommRing A] (h : ℕ) (z : Fin 3 → A) :
    OddPatterns.mPf h 0 z =
      z 2 ^ (2 * h) * ColOne.Dab (2 * h + 1) (z 0) (z 1) -
        z 1 ^ (2 * h) * ColOne.Dab (2 * h + 1) (z 0) (z 2) +
        z 0 ^ (2 * h) * ColOne.Dab (2 * h + 1) (z 1) (z 2) :=
  OddPatterns.A3 h z

-- (A4)
example {A : Type*} [CommRing A] (h : ℕ) (z : Fin 3 → A) :
    OddPatterns.mPf h 2 z =
      ColOne.Dab (2 * h + 1) (z 0) (z 1) - ColOne.Dab (2 * h + 1) (z 0) (z 2) +
        ColOne.Dab (2 * h + 1) (z 1) (z 2) :=
  OddPatterns.A4 h z

-- (A5)
example {A : Type*} [CommRing A] (h : ℕ) (l : ℕ) {n : ℕ} (z : Fin n → A)
    (hev : Even (n + l)) : OddPatterns.mPf h l z = 0 :=
  OddPatterns.A5 h l z hev

-- (A6)
example {A : Type*} [CommRing A] (h : ℕ) (l : ℕ) {n : ℕ} (z : Fin n → A) (hl : 1 ≤ l)
    (hn : n + 1 < l) : OddPatterns.mPf h l z = 0 :=
  OddPatterns.A6 h l z hl hn

-- (A7): the sign of σ, as an integer cast into A.
example {A : Type*} [CommRing A] (h : ℕ) (l : ℕ) {n : ℕ} (z : Fin n → A)
    (σ : Equiv.Perm (Fin n)) :
    OddPatterns.mPf h l (fun i : Fin n => z (σ i)) =
      ((Equiv.Perm.sign σ : ℤ) : A) * OddPatterns.mPf h l z :=
  OddPatterns.A7 h l z σ

-- (B0), unfolded: the INCREASING enumeration of B, y of the ring C_m with q = 2h + 2.
example (F : Type*) [Field F] (h : ℕ) (l : ℕ) {m : ℕ} (B : Finset (Fin m)) :
    OddPatterns.markedPf F h l B =
      OddPatterns.mPf h l
        (fun i : Fin B.card => Tight.y F (2 * h + 2) (B.orderEmbOfFin rfl i)) :=
  rfl

-- (B1), the product, unfolded: pairD on the pairs, markedPf with lam.len on the marked block,
-- Delta on the blocks c = 2, ..., lam.row 1 (no first block).
example (F : Type*) [Field F] (h : ℕ) {m : ℕ} {lam : ChainLemma.Partition}
    {I : Finset (Fin m)} (T : OddPatterns.MarkedPattern lam I) :
    T.prod F h =
      (∏ e ∈ T.pairs, Tight.pairD F (2 * h + 2) e) *
          OddPatterns.markedPf F h lam.len T.marked *
        ∏ c ∈ Finset.Icc 2 (lam.row 1), Tight.Delta F (2 * h + 2) (T.blocks c) :=
  rfl

-- (B1), the fields of the structure, read off one by one.
example {m : ℕ} {lam : ChainLemma.Partition} {I : Finset (Fin m)}
    (T : OddPatterns.MarkedPattern lam I) :
    (∀ e ∈ T.pairs, e.card = 2) ∧
    (T.pairs : Set (Finset (Fin m))).PairwiseDisjoint id ∧
    (∀ c ∈ Finset.Icc 2 (lam.row 1), (T.blocks c).card = Tight.colLen lam c) ∧
    ((↑(Finset.Icc 2 (lam.row 1)) : Set ℕ).PairwiseDisjoint T.blocks) ∧
    (∀ e ∈ T.pairs, ∀ c ∈ Finset.Icc 2 (lam.row 1), Disjoint e (T.blocks c)) ∧
    (∀ e ∈ T.pairs, Disjoint e T.marked) ∧
    (∀ c ∈ Finset.Icc 2 (lam.row 1), Disjoint (T.blocks c) T.marked) ∧
    (∃ t : ℕ, T.marked.card = lam.len + 1 + 2 * t) ∧
    (T.pairs.sup id ∪ (Finset.Icc 2 (lam.row 1)).sup T.blocks ∪ T.marked = I) :=
  ⟨T.card_pair, T.pairs_disjoint, T.card_block, T.blocks_disjoint, T.pairs_blocks_disjoint,
    T.pairs_marked_disjoint, T.blocks_marked_disjoint, T.marked_card, T.cover⟩

-- (B2), unfolded: unmarked part = the tight patterns at q = 2h + 2 of the λ with (λ, false) ∈ Λ;
-- marked part = the marked patterns of the λ with (λ, true) ∈ Λ.
example (F : Type*) [Field F] (h : ℕ) {m : ℕ} (Lam : Set OddShapes.Shape)
    (I : Finset (Fin m)) :
    OddPatterns.VS F h Lam I =
      Ideal.span {g : Peel.C F (2 * h + 2) m |
          ∃ lam : ChainLemma.Partition, (lam, false) ∈ Lam ∧
            ∃ T : Tight.TightPattern lam I, T.prod F (2 * h + 2) = g} ⊔
        Ideal.span {g : Peel.C F (2 * h + 2) m |
          ∃ lam : ChainLemma.Partition, (lam, true) ∈ Lam ∧
            ∃ T : OddPatterns.MarkedPattern lam I, T.prod F h = g} :=
  rfl

example (F : Type*) [Field F] (h : ℕ) (m : ℕ) (Lam : Set OddShapes.Shape) :
    OddPatterns.VSAll F h m Lam = OddPatterns.VS F h Lam (Finset.univ : Finset (Fin m)) :=
  rfl

-- (B3)
example {m : ℕ} {lam : ChainLemma.Partition} {I : Finset (Fin m)}
    (T : OddPatterns.MarkedPattern lam I) (t : ℕ)
    (ht : T.marked.card = lam.len + 1 + 2 * t) :
    I.card = 2 * T.pairs.card + 2 * t + lam.size + 1 :=
  OddPatterns.B3 T t ht

-- (B4), both parts
example {F : Type*} [Field F] {h : ℕ} {m : ℕ} {Lam : Set OddShapes.Shape}
    {lam : ChainLemma.Partition} (hlam : (lam, false) ∈ Lam) {I : Finset (Fin m)}
    (T : Tight.TightPattern lam I) :
    T.prod F (2 * h + 2) ∈ OddPatterns.VS F h Lam I :=
  OddPatterns.B4_tight hlam T

example {F : Type*} [Field F] {h : ℕ} {m : ℕ} {Lam : Set OddShapes.Shape}
    {lam : ChainLemma.Partition} (hlam : (lam, true) ∈ Lam) {I : Finset (Fin m)}
    (T : OddPatterns.MarkedPattern lam I) :
    T.prod F h ∈ OddPatterns.VS F h Lam I :=
  OddPatterns.B4_marked hlam T

-- (B5)
example {F : Type*} [Field F] {h : ℕ} {m : ℕ} {Lam Lam' : Set OddShapes.Shape}
    (hsub : Lam ⊆ Lam') (I : Finset (Fin m)) :
    OddPatterns.VS F h Lam I ≤ OddPatterns.VS F h Lam' I :=
  OddPatterns.B5_mono hsub I

example {F : Type*} [Field F] {h : ℕ} {m : ℕ} (I : Finset (Fin m)) :
    OddPatterns.VS F h (∅ : Set OddShapes.Shape) I = ⊥ :=
  OddPatterns.B5_empty I

example {F : Type*} [Field F] {h : ℕ} {m : ℕ} {Lam : Set OddShapes.Shape}
    (hLam : ∀ lam : ChainLemma.Partition, (lam, true) ∉ Lam) (I : Finset (Fin m)) :
    OddPatterns.VS F h Lam I =
      Tight.VLam F (2 * h + 2) (OddShapes.comp Lam false) I :=
  OddPatterns.B5_no_marked (Set.eq_empty_iff_forall_notMem.2 hLam) I

-- (B6): the two examples, as equalities of ideals.
example {F : Type*} [Field F] {h : ℕ} :
    OddPatterns.VSAll F h 1 ({(OddShapes.emptyPart, true)} : Set OddShapes.Shape) =
      Ideal.span ({Tight.y F (2 * h + 2) (0 : Fin 1) ^ (2 * h)} :
        Set (Peel.C F (2 * h + 2) 1)) :=
  OddPatterns.B6_empty

example {F : Type*} [Field F] {h : ℕ} :
    OddPatterns.VSAll F h 2 ({(OddShapes.onePart, true)} : Set OddShapes.Shape) =
      Ideal.span ({ColOne.Dab (2 * h + 1) (Tight.y F (2 * h + 2) (0 : Fin 2))
        (Tight.y F (2 * h + 2) (1 : Fin 2))} : Set (Peel.C F (2 * h + 2) 2)) :=
  OddPatterns.B6_one

example : OddShapes.emptyPart.parts = [] := rfl
example : OddShapes.onePart.parts = [1] := rfl

-- (C1), with "plus or minus" written out.
example {F : Type*} [Field F] {h : ℕ} {m : ℕ} (σ : Equiv.Perm (Fin m)) (l : ℕ)
    (B : Finset (Fin m)) :
    Tight.relabel F (2 * h + 2) σ (OddPatterns.markedPf F h l B) =
        OddPatterns.markedPf F h l (B.map σ.toEmbedding) ∨
      Tight.relabel F (2 * h + 2) σ (OddPatterns.markedPf F h l B) =
        -OddPatterns.markedPf F h l (B.map σ.toEmbedding) :=
  OddPatterns.C1 σ l B

-- (C2)
example {F : Type*} [Field F] {h : ℕ} {m : ℕ} (σ : Equiv.Perm (Fin m))
    {lam : ChainLemma.Partition} {I : Finset (Fin m)} (T : OddPatterns.MarkedPattern lam I) :
    ∃ T' : OddPatterns.MarkedPattern lam (I.map σ.toEmbedding),
      Tight.relabel F (2 * h + 2) σ (T.prod F h) = T'.prod F h ∨
        Tight.relabel F (2 * h + 2) σ (T.prod F h) = -T'.prod F h :=
  OddPatterns.C2 σ T

-- (C3): an EQUALITY of ideals.
example {F : Type*} [Field F] {h : ℕ} {m : ℕ} (σ : Equiv.Perm (Fin m))
    (Lam : Set OddShapes.Shape) (I : Finset (Fin m)) :
    Ideal.map (Tight.relabel F (2 * h + 2) σ) (OddPatterns.VS F h Lam I) =
      OddPatterns.VS F h Lam (I.map σ.toEmbedding) :=
  OddPatterns.C3 σ Lam I

example {F : Type*} [Field F] {h : ℕ} {m : ℕ} (σ : Equiv.Perm (Fin m))
    (Lam : Set OddShapes.Shape) :
    Ideal.map (Tight.relabel F (2 * h + 2) σ) (OddPatterns.VSAll F h m Lam) =
      OddPatterns.VSAll F h m Lam :=
  OddPatterns.C3_all σ Lam

-- (D1)
example {F : Type*} [Field F] {h : ℕ} {m : ℕ} (i : Fin m) :
    Tight.y F (2 * h + 2) i ^ (2 * h + 1) = (0 : Peel.C F (2 * h + 2) m) :=
  OddPatterns.D1 i

-- (D2)
example {F : Type*} [Field F] {h : ℕ} {m : ℕ} (P : Finset (Finset (Fin m))) :
    Membership.DPy (2 * h + 1) (Tight.y F (2 * h + 2)) P =
      ∏ e ∈ P, Tight.pairD F (2 * h + 2) e :=
  OddPatterns.D2_DPy P

example {F : Type*} [Field F] {h : ℕ} {m : ℕ} (S : Finset (Fin m)) :
    Tight.vand (Tight.y F (2 * h + 2)) S = Tight.Delta F (2 * h + 2) S :=
  OddPatterns.D2_vand S

-- (D3) = Lemma 8.7 in C_m, with the ideal UB written unfolded and its generators in the
-- language of C_m (Delta and pairD), through (D2).
example {F : Type*} [Field F] {h : ℕ} (hh : 1 ≤ h) {m : ℕ} (l : ℕ) (B : Finset (Fin m))
    (t : ℕ) (hB : B.card = l + 1 + 2 * t) :
    OddPatterns.markedPf F h l B ∈
      Ideal.span {g : Peel.C F (2 * h + 2) m |
        ∃ (S : Finset (Fin m)) (P : Finset (Finset (Fin m))),
          S ⊆ B ∧ S.card = l + 1 ∧ Odd3.IsPairs P ∧ Odd3.supp P = B \ S ∧
          g = Tight.Delta F (2 * h + 2) S * ∏ e ∈ P, Tight.pairD F (2 * h + 2) e} :=
  OddPatterns.D3 hh l B t hB
