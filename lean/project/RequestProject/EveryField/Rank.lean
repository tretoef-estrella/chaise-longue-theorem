module

public import Mathlib

/-!
# Part (ii) of the Theorem of `q_every_field.md`: rank under a ring map from `ℤ`

Formalization of **part (ii)** of the Theorem of `q_every_field.md`: for an integer matrix `A`
and a field `F`, `rank_F(A) ≤ rank_ℚ(A)`, with equality when `char F = 0`.  Here `rank_F(A)` is
the rank (`Matrix.rank`) of the image `A.map (Int.castRingHom F)` of `A` over `F`.

The proof does not go through minors: the rows of `A` span a free `ℤ`-module `L ⊆ ℤ^n` of some
rank `r`; the images of a `ℤ`-basis of `L` span the row space of the image of `A` over every field
(so `rank_F(A) ≤ r`), and they are linearly independent over every field of characteristic `0`
(so `rank_F(A) = r` there, in particular `rank_ℚ(A) = r`).  The independence is proved with the
Gram matrix `W Wᵀ` of the basis, whose determinant is a non-zero integer.
-/

@[expose] public section

namespace EveryField

open Matrix

variable {m n : Type*} [Fintype n]

/-- **Part (ii)** of `q_every_field.md`: the rank `rank_F(A)` of an integer matrix `A` over a
field `F`, i.e. the rank of its image under the ring map `ℤ → F`. -/
noncomputable def rankOver (F : Type*) [Field F] (A : Matrix m n ℤ) : ℕ :=
  (A.map (Int.castRingHom F)).rank

/-- **Proof of part (ii)** of `q_every_field.md` (auxiliary): the map `ℤ^n → F^n` induced by the
ring map `ℤ → F`, as a `ℤ`-linear map. -/
noncomputable def castLin (F : Type*) [Field F] (n : Type*) : (n → ℤ) →ₗ[ℤ] (n → F) :=
  LinearMap.compLeft (Int.castAddHom F).toIntLinearMap n

omit [Fintype n] in
@[simp] theorem castLin_apply (F : Type*) [Field F] (v : n → ℤ) (i : n) :
    castLin F n v i = (v i : F) := rfl

/-- **Proof of part (ii)** of `q_every_field.md` (auxiliary): images over a field of
characteristic `0` of `ℤ`-linearly independent integer vectors are linearly independent (the
Gram determinant `det (W Wᵀ)` is a non-zero integer, hence non-zero in `F`). -/
theorem linearIndependent_castLin {F : Type*} [Field F] [CharZero F] {r : ℕ}
    {W : Fin r → n → ℤ} (hW : LinearIndependent ℤ W) :
    LinearIndependent F (castLin F n ∘ W) := by
  classical
  let Wm : Matrix (Fin r) n ℤ := Matrix.of W
  let G : Matrix (Fin r) (Fin r) ℤ := Wm * Wmᵀ
  have hdet : G.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv, hGv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    have h1 : (Wmᵀ *ᵥ v) ⬝ᵥ (Wmᵀ *ᵥ v) = 0 := by
      have : v ⬝ᵥ (G *ᵥ v) = 0 := by rw [hGv, dotProduct_zero]
      rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose] at this
      exact this
    have h2 : Wmᵀ *ᵥ v = 0 := dotProduct_self_eq_zero.1 h1
    apply hv
    have h3 : ∑ i, v i • W i = 0 := by
      rw [← h2]
      ext j
      simp [Matrix.mulVec, dotProduct, Wm, Finset.sum_apply, mul_comm]
    exact funext (Fintype.linearIndependent_iff.1 hW v h3)
  let GK : Matrix (Fin r) (Fin r) F := G.map (Int.castRingHom F)
  have hdetK : GK.det ≠ 0 := by
    rw [show GK.det = Int.castRingHom F G.det from (RingHom.map_det _ _).symm]
    simpa using hdet
  rw [Fintype.linearIndependent_iff]
  intro c hc
  let WK : Matrix (Fin r) n F := Wm.map (Int.castRingHom F)
  have hvec : c ᵥ* WK = 0 := by
    rw [← hc]
    ext j
    simp [Matrix.vecMul, dotProduct, WK, Wm, Finset.sum_apply]
  have hGK : GK = WK * WKᵀ := by
    simp only [GK, G, WK, Matrix.map_mul, Matrix.transpose_map]
  have : GK *ᵥ c = 0 := by
    rw [hGK, ← Matrix.mulVec_mulVec, Matrix.mulVec_transpose, hvec, Matrix.mulVec_zero]
  exact congrFun (Matrix.eq_zero_of_mulVec_eq_zero hdetK this)

/-- **Proof of part (ii)** of `q_every_field.md` (auxiliary): the `ℤ`-span `L ⊆ ℤ^n` of the rows
of an integer matrix `A`. -/
noncomputable def rowLattice (A : Matrix m n ℤ) : Submodule ℤ (n → ℤ) :=
  Submodule.span ℤ (Set.range A.row)

/-- **Proof of part (ii)** of `q_every_field.md` (auxiliary): the images over `F` of a `ℤ`-basis
of the row lattice `L` span the row space of the image of `A` over `F`. -/
theorem span_rows_map_eq (F : Type*) [Field F] (A : Matrix m n ℤ) :
    Submodule.span F (Set.range (A.map (Int.castRingHom F)).row) =
      Submodule.span F (Set.range (castLin F n ∘ (↑) ∘ Module.finBasis ℤ (rowLattice A))) := by
  set b := Module.finBasis ℤ (rowLattice A)
  -- every element of the lattice maps into the span of the images of the basis
  have hL : ∀ x ∈ rowLattice A, castLin F n x ∈
      Submodule.span F (Set.range (castLin F n ∘ (↑) ∘ b)) := by
    intro x hx
    have : x = ∑ i, b.repr ⟨x, hx⟩ i • (b i : n → ℤ) := by
      conv_lhs => rw [show x = ((⟨x, hx⟩ : rowLattice A) : n → ℤ) from rfl,
        ← b.sum_repr ⟨x, hx⟩]
      simp only [Submodule.coe_sum, Submodule.coe_smul]
    rw [this, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [map_zsmul]
    exact Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hL _ (Submodule.subset_span ⟨i, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have hb : (b i : n → ℤ) ∈ rowLattice A := (b i).2
    simp only [Function.comp_apply, SetLike.mem_coe]
    refine Submodule.span_induction (p := fun x _ => castLin F n x ∈
      Submodule.span F (Set.range (A.map (Int.castRingHom F)).row)) ?_ ?_ ?_ ?_ hb
    · rintro _ ⟨j, rfl⟩
      exact Submodule.subset_span ⟨j, by ext; simp [Matrix.row]⟩
    · simp
    · intro x y _ _ hx hy
      rw [map_add]; exact Submodule.add_mem _ hx hy
    · intro a x _ hx
      rw [map_zsmul]; exact Submodule.smul_of_tower_mem _ _ hx

variable [Finite m]

/-- **Proof of part (ii)** of `q_every_field.md` (auxiliary): `rank_F(A) ≤ r`, where `r` is the
rank of the row lattice `L`. -/
theorem rankOver_le_finrank (F : Type*) [Field F] (A : Matrix m n ℤ) :
    rankOver F A ≤ Module.finrank ℤ (rowLattice A) := by
  rw [rankOver, Matrix.rank_eq_finrank_span_row, span_rows_map_eq]
  exact (finrank_range_le_card _).trans (by simp)

/-- **Proof of part (ii)** of `q_every_field.md` (auxiliary): `rank_F(A) = r` when
`char F = 0`, where `r` is the rank of the row lattice `L`. -/
theorem rankOver_eq_finrank (F : Type*) [Field F] [CharZero F] (A : Matrix m n ℤ) :
    rankOver F A = Module.finrank ℤ (rowLattice A) := by
  rw [rankOver, Matrix.rank_eq_finrank_span_row, span_rows_map_eq,
    finrank_span_eq_card (linearIndependent_castLin _), Fintype.card_fin]
  have := (Module.finBasis ℤ (rowLattice A)).linearIndependent.map' (rowLattice A).subtype
    (Submodule.ker_subtype _)
  exact this

/-- **Part (ii)** of the Theorem of `q_every_field.md` (inequality): for an integer matrix `A`
and a field `F`, `rank_F(A) ≤ rank_ℚ(A)`. -/
theorem rankOver_le_rankOver_rat (F : Type*) [Field F] (A : Matrix m n ℤ) :
    rankOver F A ≤ rankOver ℚ A := by
  rw [rankOver_eq_finrank ℚ A]
  exact rankOver_le_finrank F A

/-- **Part (ii)** of the Theorem of `q_every_field.md` (equality): for an integer matrix `A` and
a field `F` with `char F = 0`, `rank_F(A) = rank_ℚ(A)`. -/
theorem rankOver_eq_rankOver_rat (F : Type*) [Field F] [CharZero F] (A : Matrix m n ℤ) :
    rankOver F A = rankOver ℚ A := by
  rw [rankOver_eq_finrank F A, rankOver_eq_finrank ℚ A]

end EveryField

end
