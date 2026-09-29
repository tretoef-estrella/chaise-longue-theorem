module

public import RequestProject.EveryField.Rank

/-!
# Part (a) of the proof of the Theorem (every field) of `q_col_assembly.md`

*Field extensions*: for fields `K ⊆ L` and a matrix `M` over `K`, `rank_K(M) = rank_L(M)`
(`ColAssembly.rank_map_algebraMap`). Consequently, for an integer matrix `A`, `rank_F(A)` only
depends on the prime field of `F` (`ColAssembly.rankOver_eq_of_algebra`,
`ColAssembly.rankOver_eq_rankOver_zmod`).

The proof uses linear independence instead of minors: an `F`-basis of `L` shows that vectors of
`K^n` which are linearly independent over `K` stay linearly independent over `L`.
-/

@[expose] public section

namespace ColAssembly

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- **Proof of the Theorem (every field)**, part (a), in `q_col_assembly.md` (auxiliary): vectors
of `K^n` which are linearly independent over `K` stay linearly independent over `L ⊇ K`. -/
theorem linearIndependent_map_algebraMap {ι n : Type*} [Fintype ι] {v : ι → n → K}
    (hv : LinearIndependent K v) :
    LinearIndependent L (fun i => fun j => algebraMap K L (v i j)) := by
  classical
  rw [Fintype.linearIndependent_iff] at hv ⊢
  intro c hc i
  let b := Module.Free.chooseBasis K L
  refine b.repr.injective ?_
  ext t
  simp only [map_zero, Finsupp.coe_zero, Pi.zero_apply]
  refine hv (fun i => b.repr (c i) t) ?_ i
  funext j
  have h := congrArg (fun x => b.repr x t) (congrFun hc j)
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, Finsupp.coe_finset_sum,
    Finset.sum_apply, map_zero, Finsupp.coe_zero, Pi.zero_apply] at h
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
  rw [← h]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_comm (c i), ← Algebra.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul, mul_comm]

/-- **Proof of the Theorem (every field)**, part (a), in `q_col_assembly.md`: the rank of a matrix
over a field `K` does not change under extension of scalars to a field `L ⊇ K`. -/
theorem rank_map_algebraMap {m n : Type*} [Finite m] [Fintype n] (M : Matrix m n K) :
    (M.map (algebraMap K L)).rank = M.rank := by
  classical
  rw [Matrix.rank_eq_finrank_span_row, Matrix.rank_eq_finrank_span_row]
  obtain ⟨b, hbsub, hbspan, hbind⟩ := exists_linearIndependent K (Set.range M.row)
  have hbfin : b.Finite := (Set.finite_range _).subset hbsub
  haveI : Fintype b := hbfin.fintype
  let φ : (n → K) →ₗ[K] (n → L) := LinearMap.compLeft (Algebra.linearMap K L) n
  have hind : LinearIndependent L (fun x : b => φ x) :=
    linearIndependent_map_algebraMap (v := fun x : b => (x : n → K)) hbind
  have hspan : Submodule.span L (Set.range (M.map (algebraMap K L)).row) =
      Submodule.span L (Set.range fun x : b => φ x) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      have hi : M.row i ∈ Submodule.span K b := by
        rw [hbspan]; exact Submodule.subset_span ⟨i, rfl⟩
      have h1 : φ (M.row i) ∈ (Submodule.span K b).map φ := Submodule.mem_map_of_mem hi
      rw [Submodule.map_span] at h1
      have h2 : Submodule.span K (φ '' b) ≤
          (Submodule.span L (Set.range fun x : b => φ x)).restrictScalars K := by
        rw [Submodule.span_le]
        rintro _ ⟨x, hx, rfl⟩
        exact Submodule.subset_span ⟨⟨x, hx⟩, rfl⟩
      exact h2 h1
    · rw [Submodule.span_le]
      rintro _ ⟨⟨x, hx⟩, rfl⟩
      obtain ⟨i, rfl⟩ := hbsub hx
      exact Submodule.subset_span ⟨i, rfl⟩
  rw [hspan, finrank_span_eq_card hind, ← finrank_span_eq_card hbind, Subtype.range_coe, hbspan]

/-- **Proof of the Theorem (every field)**, part (a), in `q_col_assembly.md`: for fields `K ⊆ L`
and an integer matrix `A`, `rank_K(A) = rank_L(A)`. -/
theorem rankOver_eq_of_algebra {m n : Type*} [Finite m] [Fintype n] (A : Matrix m n ℤ) :
    EveryField.rankOver L A = EveryField.rankOver K A := by
  unfold EveryField.rankOver
  have : Int.castRingHom L = (algebraMap K L).comp (Int.castRingHom K) := RingHom.ext_int _ _
  rw [this, RingHom.coe_comp, ← Matrix.map_map]
  exact rank_map_algebraMap _

/-- **Proof of the Theorem (every field)**, part (a), in `q_col_assembly.md`: for a field `F` of
characteristic `p > 0` and an integer matrix `A`, `rank_F(A) = rank_{F_p}(A)`, so `rank_F(A)`
depends only on the prime field of `F`. -/
theorem rankOver_eq_rankOver_zmod (F : Type*) [Field F] (p : ℕ) [Fact p.Prime] [CharP F p]
    {m n : Type*} [Finite m] [Fintype n] (A : Matrix m n ℤ) :
    EveryField.rankOver F A = EveryField.rankOver (ZMod p) A := by
  letI := ZMod.algebra F p
  exact rankOver_eq_of_algebra A

end ColAssembly

end
