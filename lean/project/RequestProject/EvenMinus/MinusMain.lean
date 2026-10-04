module

public import RequestProject.EvenMinus.MinusGen
public import RequestProject.EvenMinus.PairIdeal
public import RequestProject.EvenMinus.OneBlock
public import RequestProject.OddTheorem.Main

/-!
# Part M, (M5)–(M7), and Part S of `q_even_block_minus.md`

* (M5) `EvenMinus.lemmaM5`: `0 ∈ 𝒞_{−1}`, `|𝒞_{−1}| = 2j + 2`:
  `dim I_{c,−1} = dim TheoremB.DIdeal F (q + 1) j` and `Q^e_j(q + 1) ≤ dim I_{c,−1}`
  (Theorem O, `OddTheorem.theoremO` with `h = (q − 1)/2`).
* (M6) `EvenMinus.lemmaM6`: `0 ∉ 𝒞_{−1}`, `|𝒞_{−1}| = 2j + 2`:
  `dim I_{c,−1} = dim OddPatterns.VSAll F h (2j + 2) {(∅, false)}` and
  `Q^e_j(q + 1) ≤ dim I_{c,−1}` (Theorem 8.11 with `OddShapes.isInterlaced_root_even` and
  `OddLayers.card_ZS_root_even`).
* (M7) `EvenMinus.lemma99`: Lemma 9.9, `NS S (−1) |𝒞_{−1}| ≤ dim I_{c,−1}`.
* (S1) `EvenMinus.S1`: the summary.
-/

@[expose] public section

open MvPolynomial

namespace EvenMinus

open ColSplit ColSurv ColComp ColTensor ColDecomp EvenBlocks Peel

open scoped Classical

variable {F : Type*} [Field F] (S : ColSetting F) {k : ℕ}

/-! ### The increasing enumerations of `𝒞_ζ` (model: `ColOne.succW1`, `ColOne.ebar`) -/

/-- **Part M, (M5), (M6)** of `q_even_block_minus.md` (proof; model `ColOne.succW1`): the increasing
map `W_ζ^S → 𝒞_ζ`, `s ↦ s + 1`. -/
def succWS (c : Fin (2 * k + 1) → S.μ) (ζ : F) (s : WS S c ζ) : cls (cExt c) ζ :=
  ⟨s.1.succ, (mem_WS S).1 s.2⟩

/-- **Part M, (M5), (M6)** of `q_even_block_minus.md` (proof): `s ↦ s + 1` is increasing. -/
theorem succWS_strictMono (c : Fin (2 * k + 1) → S.μ) (ζ : F) : StrictMono (succWS S c ζ) := by
  intro a b h
  change a.1.succ < b.1.succ
  exact Fin.succ_lt_succ_iff.2 h

/-- **Part M, (M5), (M6)** of `q_even_block_minus.md` (proof): `W_ζ^S = 𝒞_ζ ∖ {0}` (shifted). -/
theorem map_WS (c : Fin (2 * k + 1) → S.μ) (ζ : F) :
    (WS S c ζ).map (Fin.succEmb _) = (cls (cExt c) ζ).erase 0 := by
  ext x
  simp only [Finset.mem_map, Fin.coe_succEmb, Finset.mem_erase]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨Fin.succ_ne_zero j, (mem_WS S).1 hj⟩
  · rintro ⟨hx0, hx⟩
    obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.2 hx0
    exact ⟨j, (mem_WS S).2 hx, rfl⟩

/-- **Part M, (M5)** of `q_even_block_minus.md` (proof): if `0 ∈ 𝒞_ζ` then `|W_ζ^S| + 1 = |𝒞_ζ|`. -/
theorem card_WS_of_mem (c : Fin (2 * k + 1) → S.μ) (ζ : F)
    (h0 : (0 : Fin (2 * k + 2)) ∈ cls (cExt c) ζ) :
    (WS S c ζ).card + 1 = (cls (cExt c) ζ).card := by
  rw [← Finset.card_map (Fin.succEmb _), map_WS, Finset.card_erase_of_mem h0]
  have := Finset.card_pos.2 ⟨_, h0⟩
  omega

/-- **Part M, (M6)** of `q_even_block_minus.md` (proof): if `0 ∉ 𝒞_ζ` then `|W_ζ^S| = |𝒞_ζ|`. -/
theorem card_WS_of_notMem (c : Fin (2 * k + 1) → S.μ) (ζ : F)
    (h0 : (0 : Fin (2 * k + 2)) ∉ cls (cExt c) ζ) : (WS S c ζ).card = (cls (cExt c) ζ).card := by
  rw [← Finset.card_map (Fin.succEmb _), map_WS, Finset.erase_eq_of_notMem h0]

/-- **Part M, (M5)** of `q_even_block_minus.md` (proof; model `ColOne.ebar`): the extension
`ē : {0, …, n} → 𝒞_ζ` of `e : [n] → W_ζ^S` by `ē(0) := 0`. -/
def ebarS (c : Fin (2 * k + 1) → S.μ) (ζ : F) (h0 : (0 : Fin (2 * k + 2)) ∈ cls (cExt c) ζ)
    {n : ℕ} (e : Fin n → WS S c ζ) : Fin (n + 1) → cls (cExt c) ζ :=
  Fin.cases ⟨0, h0⟩ fun i => succWS S c ζ (e i)

/-- **Part M, (M5)** of `q_even_block_minus.md` (proof): `ē` is increasing if `e` is. -/
theorem ebarS_strictMono (c : Fin (2 * k + 1) → S.μ) (ζ : F)
    (h0 : (0 : Fin (2 * k + 2)) ∈ cls (cExt c) ζ) {n : ℕ} (e : Fin n ≃o WS S c ζ) :
    StrictMono (ebarS S c ζ h0 e) := by
  intro a b hab
  induction a using Fin.cases with
  | zero =>
    induction b using Fin.cases with
    | zero => exact absurd hab (lt_irrefl _)
    | succ j =>
      change (0 : Fin (2 * k + 2)) < (e j).1.succ
      exact Fin.succ_pos _
  | succ i =>
    induction b using Fin.cases with
    | zero => exact absurd hab (not_lt.2 (Fin.zero_le _))
    | succ j =>
      exact succWS_strictMono S c ζ (e.strictMono (Fin.succ_lt_succ_iff.1 hab))

/-- **Part M, (M5)** of `q_even_block_minus.md` (proof): `ē` is onto `𝒞_ζ` if `e` is onto. -/
theorem ebarS_surjective (c : Fin (2 * k + 1) → S.μ) (ζ : F)
    (h0 : (0 : Fin (2 * k + 2)) ∈ cls (cExt c) ζ) {n : ℕ} (e : Fin n ≃o WS S c ζ) :
    Function.Surjective (ebarS S c ζ h0 e) := by
  intro x
  by_cases hx : x.1 = 0
  · exact ⟨0, Subtype.ext hx.symm⟩
  · obtain ⟨j, hj⟩ := Fin.exists_succ_eq.2 hx
    have hjW : j ∈ WS S c ζ := (mem_WS S).2 (hj ▸ x.2)
    refine ⟨(e.symm ⟨j, hjW⟩).succ, Subtype.ext ?_⟩
    change (e (e.symm ⟨j, hjW⟩)).1.succ = x.1
    rw [e.apply_symm_apply]
    exact hj

/-- **Part M, (M6)** of `q_even_block_minus.md` (proof): if `0 ∉ 𝒞_ζ`, `s ↦ s + 1` is onto. -/
theorem succWS_surjective (c : Fin (2 * k + 1) → S.μ) (ζ : F)
    (h0 : (0 : Fin (2 * k + 2)) ∉ cls (cExt c) ζ) : Function.Surjective (succWS S c ζ) := by
  intro x
  have hx : x.1 ≠ 0 := fun h => h0 (h ▸ x.2)
  obtain ⟨j, hj⟩ := Fin.exists_succ_eq.2 hx
  exact ⟨⟨j, (mem_WS S).2 (hj ▸ x.2)⟩, Subtype.ext hj⟩

/-! ### Changing the name of the exponent -/

omit S in
/-- **Part M, (M5)** of `q_even_block_minus.md` (proof): Theorem O (`OddTheorem.theoremO`) for any
`Q = 2h + 2`. -/
theorem theoremO_of_eq {h : ℕ} (hh : 1 ≤ h) (j : ℕ) {Q : ℕ} (hQ : Q = 2 * h + 2) :
    EvenCount.QkEven j Q ≤ Module.finrank F ((TheoremB.DIdeal F Q j).restrictScalars F) := by
  subst hQ
  exact OddTheorem.theoremO F hh j

omit S in
/-- **Part M, (M6)** of `q_even_block_minus.md` (proof): `dim V_Λ` does not depend on how the
exponent is written. -/
theorem finrank_VLamAll_of_eq {Q Q' m : ℕ} (hQ : Q = Q') (Λ : Set ChainLemma.Partition) :
    Module.finrank F ((Tight.VLamAll F Q m Λ).restrictScalars F) =
      Module.finrank F ((Tight.VLamAll F Q' m Λ).restrictScalars F) := by
  subst hQ; rfl

omit S in
/-- **Part M, (M6)** of `q_even_block_minus.md`: the ideal `V_{{(∅,0)}}` of
`q_oddbox_patterns.md` is the ideal of the tight patterns of `∅`, i.e. (by
`ColOne.VLamAll_empty_eq`) the ideal generated by the products `Π_{{i,l} ∈ P} D(y_i, y_l)` over the
perfect matchings `P` (`OddPatterns.B5_no_marked`). -/
theorem VSAll_root_even_eq (h m : ℕ) :
    OddPatterns.VSAll F h m {(OddShapes.emptyPart, false)} =
      Tight.VLamAll F (2 * h + 2) m {Bip.Partition'.empty} := by
  have h1 : OddShapes.comp {(OddShapes.emptyPart, false)} true = ∅ := by
    ext lam; simp [OddShapes.comp]
  have h2 : OddShapes.comp {(OddShapes.emptyPart, false)} false = {Bip.Partition'.empty} := by
    ext lam; simp [OddShapes.comp]; rfl
  rw [OddPatterns.VSAll, OddPatterns.B5_no_marked h1, h2]
  rfl

/-! ### (M5) -/

/-- **Part M, (M5)** of `q_even_block_minus.md`: if `(−1 : F) ≠ 1`, `0 ∈ 𝒞_{−1}` and
`|𝒞_{−1}| = 2j + 2`, then `dim_F I_{c,−1} = dim_F TheoremB.DIdeal F (q + 1) j`, hence
`Q^e_j(q + 1) ≤ dim_F I_{c,−1}` (Theorem O with `h = (q − 1)/2`, `2h + 2 = q + 1`, `1 ≤ h`). -/
theorem lemmaM5 (hneg : (-1 : F) ≠ 1) (c : Fin (2 * k + 1) → S.μ) {j : ℕ}
    (h0 : (0 : Fin (2 * k + 2)) ∈ cls (cExt c) (-1)) (hs : (cls (cExt c) (-1)).card = 2 * j + 2) :
    Module.finrank F (IcS S c (-1)) =
        Module.finrank F ((TheoremB.DIdeal F (S.q + 1) j).restrictScalars F) ∧
      EvenCount.QkEven j (S.q + 1) ≤ Module.finrank F (IcS S c (-1)) := by
  have hp := EvenColours.p_ne_two_of_neg_one_ne_one S hneg
  have hW : (WS S c (-1)).card = 2 * j + 1 := by have := card_WS_of_mem S c (-1) h0; omega
  set e := (WS S c (-1)).orderIsoOfFin hW
  set ē : Fin (2 * j + 2) ≃o cls (cExt c) (-1) :=
    StrictMono.orderIsoOfSurjective (ebarS S c (-1) h0 e) (ebarS_strictMono S c (-1) h0 e)
      (ebarS_surjective S c (-1) h0 e)
  have hē : ∀ a, ē a = ebarS S c (-1) h0 e a := fun a => rfl
  have hē0 : ∀ a, (ē a).1 ≠ 0 ↔ a ≠ 0 := by
    intro a
    rw [hē]
    induction a using Fin.cases with
    | zero => simp [ebarS]
    | succ i => simp [ebarS, succWS, Fin.succ_ne_zero]
  have hκ : ∀ a, (ē a).1 ≠ 0 → (e.toEquiv (TheoremB.idx a)).1.succ = (ē a).1 := by
    intro a ha
    rw [hē0] at ha
    obtain ⟨i, rfl⟩ := Fin.exists_succ_eq.2 ha
    have hi : TheoremB.idx i.succ = i := by ext; simp [TheoremB.idx]
    rw [hē, hi]
    rfl
  have key := finrank_IcS_eq S hneg ē e.toEquiv TheoremB.idx hκ
  have hspan : Ideal.span (Set.range fun P : PerfMatch (Fin (2 * j + 2)) =>
      Ideal.Quotient.mk (powIdeal F (S.q + 1) (2 * j + 1)) (fpolyM S ē TheoremB.idx P)) =
        TheoremB.DIdeal F (S.q + 1) j := by
    rw [TheoremB.DIdeal]
    congr 1
    ext g
    have hpt : ∀ J : BallotBound.Matching j,
        Ideal.Quotient.mk (powIdeal F (S.q + 1) (2 * j + 1)) (fpolyM S ē TheoremB.idx J) =
          TheoremB.DJ F (S.q + 1) J := by
      intro J
      rw [fpolyM, map_prod, TheoremB.DJ]
      have hfil : Finset.univ.filter (fun a => (ē a).1 ≠ 0 ∧ a < J.1 a) =
          Finset.univ.filter (fun a => a ≠ 0 ∧ J.1 a ≠ 0 ∧ a < J.1 a) := by
        ext a
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, hē0]
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨h1, ne_of_gt (lt_of_le_of_lt (Fin.zero_le _) h2), h2⟩
        · rintro ⟨h1, -, h2⟩
          exact ⟨h1, h2⟩
      rw [hfil]
      refine Finset.prod_congr rfl fun a _ => ?_
      rw [ColOne.map_Dab, ColOne.D_eq_Dab]
      rfl
    constructor
    · rintro ⟨J, rfl⟩
      exact ⟨J, (hpt J).symm⟩
    · rintro ⟨J, rfl⟩
      exact ⟨J, hpt J⟩
  rw [hspan] at key
  refine ⟨key, key ▸ theoremO_of_eq (ColOne.one_le_h hp) j ?_⟩
  obtain ⟨t, ht⟩ := ColOne.odd_q hp
  omega

/-! ### (M6) -/

/-- **Part M, (M6)** of `q_even_block_minus.md`: if `(−1 : F) ≠ 1`, `0 ∉ 𝒞_{−1}` and
`|𝒞_{−1}| = 2j + 2`, then `dim_F I_{c,−1}` is the dimension of the ideal of
`Peel.C F (q + 1) (2j + 2)` generated by the `Π_{{i,l} ∈ P} D(y_i, y_l)` over the perfect matchings
`P` of `Fin (2j + 2)`, which is `OddPatterns.VSAll F h (2j + 2) {(∅, false)}` with
`h = (q − 1)/2` (`2h + 2 = q + 1`); hence `Q^e_j(q + 1) ≤ dim_F I_{c,−1}` (Theorem 8.11 with
`isInterlaced_root_even` and `card_ZS_root_even` for `stdOddSetting h`). -/
theorem lemmaM6 (hneg : (-1 : F) ≠ 1) (c : Fin (2 * k + 1) → S.μ) {j : ℕ}
    (h0 : (0 : Fin (2 * k + 2)) ∉ cls (cExt c) (-1)) (hs : (cls (cExt c) (-1)).card = 2 * j + 2) :
    Module.finrank F (IcS S c (-1)) =
        Module.finrank F ((OddPatterns.VSAll F ((S.q - 1) / 2) (2 * j + 2)
          {(OddShapes.emptyPart, false)}).restrictScalars F) ∧
      EvenCount.QkEven j (S.q + 1) ≤ Module.finrank F (IcS S c (-1)) := by
  have hp := EvenColours.p_ne_two_of_neg_one_ne_one S hneg
  have hh := ColOne.one_le_h hp
  have hq2 : S.q + 1 = 2 * ((S.q - 1) / 2) + 2 := by
    obtain ⟨t, ht⟩ := ColOne.odd_q hp
    omega
  have hW : (WS S c (-1)).card = 2 * j + 2 := by rw [card_WS_of_notMem S c (-1) h0, hs]
  set e := (WS S c (-1)).orderIsoOfFin hW
  set ψ : WS S c (-1) ≃o cls (cExt c) (-1) :=
    StrictMono.orderIsoOfSurjective (succWS S c (-1)) (succWS_strictMono S c (-1))
      (succWS_surjective S c (-1) h0)
  set ē : Fin (2 * j + 2) ≃o cls (cExt c) (-1) := e.trans ψ
  have hκ : ∀ a, (ē a).1 ≠ 0 → (e.toEquiv (id a)).1.succ = (ē a).1 := fun a _ => rfl
  have key := finrank_IcS_eq S hneg ē e.toEquiv id hκ
  have hspan : Ideal.span (Set.range fun P : PerfMatch (Fin (2 * j + 2)) =>
      Ideal.Quotient.mk (powIdeal F (S.q + 1) (2 * j + 2)) (fpolyM S ē id P)) =
        Tight.VLamAll F (S.q + 1) (2 * j + 2) {Bip.Partition'.empty} := by
    rw [ColOne.VLamAll_empty_eq]
    congr 1
    ext g
    have hpt : ∀ P : PerfMatch (Fin (2 * j + 2)),
        Ideal.Quotient.mk (powIdeal F (S.q + 1) (2 * j + 2)) (fpolyM S ē id P) =
          ColOne.DPn F (S.q + 1) P := by
      intro P
      rw [fpolyM, map_prod, ColOne.DPn]
      have hfil : Finset.univ.filter (fun a => (ē a).1 ≠ 0 ∧ a < P.1 a) =
          Finset.univ.filter (fun a => a < P.1 a) := by
        ext a
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_iff_right_iff_imp]
        intro _
        exact Fin.succ_ne_zero _
      rw [hfil]
      refine Finset.prod_congr rfl fun a _ => ?_
      rw [ColOne.map_Dab, ColOne.D_eq_Dab]
      rfl
    constructor
    · rintro ⟨P, rfl⟩
      exact ⟨P, (hpt P).symm⟩
    · rintro ⟨P, rfl⟩
      exact ⟨P, hpt P⟩
  rw [hspan, finrank_VLamAll_of_eq hq2, ← VSAll_root_even_eq] at key
  refine ⟨key, ?_⟩
  rw [key, hq2, ← OddLayers.card_ZS_root_even (OddTheorem.stdOddSetting _ hh) j]
  exact OddTheorem.theorem811 F (OddTheorem.stdOddSetting _ hh) (2 * j + 2) _
    (OddShapes.isInterlaced_root_even _ (2 * j + 2) ⟨j + 1, by ring⟩)

/-! ### (M7) Lemma 9.9 -/

/-- **Part M, (M7)** of `q_even_block_minus.md` (size `0`): if `𝒞_{−1} = ∅`, then
`I_{c,−1} = B(∅)` has dimension `1` (the empty matching gives the generator `1`). -/
theorem finrank_IcS_of_card_eq_zero (c : Fin (2 * k + 1) → S.μ)
    (hs : (cls (cExt c) (-1)).card = 0) : Module.finrank F (IcS S c (-1)) = 1 := by
  have hcls : cls (cExt c) (-1) = ∅ := Finset.card_eq_zero.1 hs
  have hW : WS S c (-1) = ∅ := by
    ext j
    simp [mem_WS, hcls]
  haveI : IsEmpty (cls (cExt c) (-1)) := ⟨fun x => by simpa [hcls] using x.2⟩
  have htop : IcS S c (-1) = ⊤ := by
    rw [Ideal.eq_top_iff_one]
    let P : PerfMatch (cls (cExt c) (-1)) := ⟨fun x => x, fun x => isEmptyElim x⟩
    have hP : gPS S c (-1) P = 1 := by
      rw [gPS, Finset.univ_eq_empty, Finset.filter_empty, Finset.prod_empty]
    rw [← hP]
    exact Ideal.subset_span ⟨P, rfl⟩
  rw [htop, ColTensor.finrank_top_ideal]
  exact (boxS S c).finrank_box_of_eq_empty hW

/-- **Part M, (M7)** of `q_even_block_minus.md`: **Lemma 9.9.** If `(−1 : F) ≠ 1`, then
`NS S (−1) |𝒞_{−1}| ≤ dim_F I_{c,−1}`, `I_{c,−1} = EvenBlocks.IcS S c (−1)` (size `0`: both
sides are `1`; even size `2j + 2`: `EvenColours.C3_c` with (M5) or (M6); odd size:
`EvenColours.C3_d`). -/
theorem lemma99 (hneg : (-1 : F) ≠ 1) (c : Fin (2 * k + 1) → S.μ) :
    EvenColours.NS S (-1) (cls (cExt c) (-1)).card ≤ Module.finrank F (IcS S c (-1)) := by
  rcases Nat.even_or_odd (cls (cExt c) (-1)).card with ⟨j, hj⟩ | hodd
  · rcases Nat.eq_zero_or_pos j with rfl | hjpos
    · have hs : (cls (cExt c) (-1)).card = 0 := by omega
      rw [hs, (EvenColours.C3_c S hneg).1, finrank_IcS_of_card_eq_zero S c hs]
    · have hs : (cls (cExt c) (-1)).card = 2 * (j - 1) + 2 := by omega
      rw [hs, (EvenColours.C3_c S hneg).2]
      by_cases h0 : (0 : Fin (2 * k + 2)) ∈ cls (cExt c) (-1)
      · exact (lemmaM5 S hneg c h0 hs).2
      · exact (lemmaM6 S hneg c h0 hs).2
  · rw [EvenColours.C3_d S (-1) hodd]
    exact Nat.zero_le _

/-! ### Part S -/

/-- **Part S, (S1)** of `q_even_block_minus.md`: for every prime `p`, every `R` with
`IsReps2 S R` and every colouring `c` admitting a compatible matching, every factor of the product
of `EvenColours.C2` is at most the corresponding factor of `EvenBlocks.lemma95`, except possibly
the factor of colour `1` when `p = 2`:
`(p ≠ 2 → NS S 1 |𝒞_1| ≤ dim IcS S c 1)`, `(−1 ≠ 1 → NS S (−1) |𝒞_{−1}| ≤ dim IcS S c (−1))` and
`(∀ ζ ∈ R, N_{bal}(|𝒞_ζ|, q) ≤ dim Icz S c ζ)`. (Only the third part uses the compatible
matching, through `|𝒞_ζ| = |𝒞_{ζ^{−1}}|`, `EvenBlocks.existsA9`.) -/
theorem S1 {R : Finset F} (hR : IsReps2 S R) (c : Fin (2 * k + 1) → S.μ)
    (hcomp : ∃ J : BallotBound.Matching k, Compatible (cExt c) J) :
    (S.p ≠ 2 → EvenColours.NS S 1 (cls (cExt c) 1).card ≤ Module.finrank F (IcS S c 1)) ∧
      ((-1 : F) ≠ 1 →
        EvenColours.NS S (-1) (cls (cExt c) (-1)).card ≤ Module.finrank F (IcS S c (-1))) ∧
      ∀ ζ ∈ R, Bip.Nbal (cls (cExt c) ζ).card S.q ≤ Module.finrank F (Icz S c ζ) := by
  have hsz := ((existsA9 hR (cExt_mem c)).1 hcomp).2
  exact ⟨fun hp => lemma98 hp c, fun hneg => lemma99 S hneg c,
    fun ζ hζ => lemma97 hR hζ c (hsz ζ hζ)⟩

end EvenMinus

end
