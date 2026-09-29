module

public import RequestProject.Support.SupportLemma

/-!
# Theorem (equality, Theorem 5.9) of `q_support.md`

Formalization of the **Theorem (equality, Theorem 5.9 of the paper)** of `q_support.md`: in the
Setting (`F` a field, `q ≥ 3` odd, `T ⊆ F` with `|T| = q − 1` and
`Π_{u∈T}(y − u) = y^{q−1} − 1`, with the involution `u ↦ −u`, bundled as
`Support.fibreSetting`), for every `m ≥ 0` and every down-set `Λ` of `Par_m`,
`dim_F V_Λ = |Z_Λ|`.

As in `q_induction.md`, `dim_F V_Λ` is the `F`-dimension of the ideal `V_Λ = Tight.VLamAll F q m Λ`
regarded as an `F`-subspace of `C_m`, `Z_Λ` is `(fibreSetting …).ZLam m Λ`, and "down-set of
`Par_m`" is `Lifts.IsDownSetPar ((q - 1) / 2) m Λ` of `q_P3_lifts.md`.
-/

@[expose] public section

open MvPolynomial

namespace Support

open ChainLemma ChainLemma.Partition Tight Fibres Lifts

set_option synthInstance.maxHeartbeats 200000

variable {F : Type*} [Field F]

/-- **Proof** of the Theorem of `q_support.md` (`λ(M) ∈ Par_m`): `|λ(M)| ≤ m`, since
`|λ(M)| = Σ_u (a_u − ā_u)` (truncated differences) `≤ Σ_u #{i : M_i = u} = m`. -/
theorem size_resPart_le {T : Type*} [Fintype T] [DecidableEq T] {h : ℕ} (S : FibreSetting T h)
    {m : ℕ} (M : Fin m → T) : (S.resPart M).size ≤ m := by
  rw [FibreSetting.resPart, size_ofMultiset, ← Finset.sum_eq_multiset_sum]
  have hm : m = ∑ u, cnt M u := by
    have := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Fin m))) (f := M)
      (t := Finset.univ) (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))
    rw [Finset.card_univ, Fintype.card_fin] at this
    exact this
  exact (Finset.sum_le_sum fun u _ => Nat.sub_le _ _).trans hm.ge

/-- **Proof** of the Theorem of `q_support.md`: `λ(M) ∈ Par_m` for every `M ∈ T^m` (part (i) of
`q_P1_fibres.md`, and `|λ(M)| ≤ m`). -/
theorem resPart_mem_Par {T : Type*} [Fintype T] [DecidableEq T] {h : ℕ} (S : FibreSetting T h)
    {m : ℕ} (M : Fin m → T) : S.resPart M ∈ Par h m := by
  obtain ⟨hlen, hmod⟩ := resPart_len_le_and_size_mod S M
  exact ⟨size_resPart_le S M, hmod, hlen⟩

/-- **Proof** of the Theorem of `q_support.md`, inequality `≤`: apply the Proposition of
`q_degeneration.md` to finitely many tight-pattern products of the elements of `Λ` generating
`V_Λ` (lifted to homogeneous polynomials `prodP`): `dim V_Λ ≤ |Σ|`; by the support lemma and since
`Λ` is a down-set of `Par_m`, `Σ ⊆ Z_Λ`. -/
theorem finrank_VLamAll_le_card_ZLam [DecidableEq F] {q : ℕ} (hq : 3 ≤ q) (hodd : Odd q)
    (T : Finset F) (hT : T.card = q - 1)
    (hprod : ∏ u ∈ T, (Polynomial.X - Polynomial.C u) = Polynomial.X ^ (q - 1) - 1)
    (m : ℕ) (Λ : Set Partition) (hΛ : IsDownSetPar ((q - 1) / 2) m Λ) :
    Module.finrank F ((VLamAll F q m Λ).restrictScalars F) ≤
      ((fibreSetting hq hodd T hT hprod).ZLam m Λ).card := by
  set S := fibreSetting hq hodd T hT hprod
  set G : Set (Peel.C F q m) :=
    {g | ∃ lam ∈ Λ, ∃ Tp : TightPattern lam (Finset.univ : Finset (Fin m)), Tp.prod F q = g}
  have hV : VLamAll F q m Λ = Ideal.span G := rfl
  -- finitely many products generate `V_Λ` (`C_m` is Noetherian)
  have hfg : (Ideal.span G).FG := IsNoetherian.noetherian _
  obtain ⟨s', hs'G, hspan⟩ := (Submodule.fg_span_iff_fg_span_finset_subset G).1 hfg
  have hG : ∀ x : s', ∃ lam ∈ Λ, ∃ Tp : TightPattern lam (Finset.univ : Finset (Fin m)),
      Tp.prod F q = x := fun x => hs'G x.2
  choose lamOf hlamOf TpOf hTpOf using hG
  let e := s'.equivFin
  let g : Fin s'.card → MvPolynomial (Fin m) F := fun i => prodP F q (TpOf (e.symm i))
  have hgen : Degeneration.genIdeal q g = VLamAll F q m Λ := by
    rw [hV, Degeneration.genIdeal]
    show Ideal.span _ = Submodule.span (Peel.C F q m) G
    rw [hspan]
    congr 1
    ext x
    simp only [Set.mem_range, Finset.mem_coe, g, mk_prodP, hTpOf]
    constructor
    · rintro ⟨i, rfl⟩; exact (e.symm i).2
    · intro hx; exact ⟨e ⟨x, hx⟩, by simp⟩
  have hdeg := Degeneration.finrank_genIdeal_le_card_supportSet hq m T hT hprod g
    (fun i => prodP_isHomogeneous F q _)
  rw [hgen] at hdeg
  refine hdeg.trans (Finset.card_le_card ?_)
  intro M hM
  simp only [Degeneration.supportSet, Finset.mem_filter, Finset.mem_univ, true_and] at hM
  obtain ⟨i, hi⟩ := hM
  have hdom := resPart_weakDom_of_eval_prodP_ne_zero hq hodd T hT hprod _ M hi
  simp only [FibreSetting.ZLam, Finset.mem_filter, Finset.mem_univ, true_and]
  exact hΛ.2 _ _ (resPart_mem_Par S M) hdom (hlamOf _)

/-- **Theorem (equality, Theorem 5.9 of the paper)** of `q_support.md`: let `F` be a field,
`q ≥ 3` odd, and `T ⊆ F` a set of `q − 1` elements with `Π_{u∈T}(y − u) = y^{q−1} − 1`, with the
involution `u ↦ −u` (the Setting, `fibreSetting`).  For every `m ≥ 0` and every down-set `Λ` of
`Par_m`: `dim_F V_Λ = |Z_Λ|`.

`≥` is the Theorem of `q_induction.md` (`Induction.finrank_VLamAll_ge_card_ZLam`), and `≤` is
`finrank_VLamAll_le_card_ZLam` (the Proposition of `q_degeneration.md` with the support lemma).
(The instance `DecidableEq F` is only used to decide equality in `T`, which is needed to define
the counts `#{i : M_i = u}` of `λ(M)`.) -/
theorem finrank_VLamAll_eq_card_ZLam [DecidableEq F] {q : ℕ} (hq : 3 ≤ q) (hodd : Odd q)
    (T : Finset F) (hT : T.card = q - 1)
    (hprod : ∏ u ∈ T, (Polynomial.X - Polynomial.C u) = Polynomial.X ^ (q - 1) - 1)
    (m : ℕ) (Λ : Set Partition) (hΛ : IsDownSetPar ((q - 1) / 2) m Λ) :
    Module.finrank F ((VLamAll F q m Λ).restrictScalars F) =
      ((fibreSetting hq hodd T hT hprod).ZLam m Λ).card :=
  le_antisymm (finrank_VLamAll_le_card_ZLam hq hodd T hT hprod m Λ hΛ)
    (Induction.finrank_VLamAll_ge_card_ZLam F hq hodd _ m Λ hΛ)

end Support

end
