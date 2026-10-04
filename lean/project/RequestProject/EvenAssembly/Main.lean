module

public import RequestProject.EvenAssembly.EveryField
public import RequestProject.ColAssembly.Main

/-!
# Part (iii) of the Theorem of `q_quartic_assembly.md`: Main Theorem′ for an even degree

Let `m ≥ 2` be even and assume `H(m, k)` (`EvenAssembly.HypH m k`). Then `R/I_ℤ` is a free
`ℤ`-module of rank `m^{2k+1} − Q^e_k(m)`, and for every field `F`,
`dim_F F[G]/I_F = m^{2k+1} − Q^e_k(m)` (`EvenAssembly.theorem_iii`).

This is the copy, for even `m` with `EvenCount.QkEven`, of `RequestProject/ColAssembly/Main.lean`:
the lemmas `finrank_span_map_L`, `free_quotient_L`, `mainTheorem'_Z`, `mainTheorem'_field` are
re-proved here with the hypotheses `Even m`, `2 ≤ m`, `H(m, k)`.
-/

@[expose] public section

namespace EvenAssembly

open ColSplit ColUpper ColAssembly EvenCount EveryField

set_option synthInstance.maxHeartbeats 200000

variable {m : ℕ} {k : ℕ}

/-- **Proof of (iii)** in `q_quartic_assembly.md`: for even `m ≥ 2` with `H(m, k)` and every
field `F`, the image of `L` (the `ℤ`-span of the rows of `A`) in `F^n` has dimension
`rank_F(A) = Q^e_k(m)`, by (ii). -/
theorem finrank_span_map_L_even (F : Type*) [Field F] (heven : Even m) (h2 : 2 ≤ m)
    (hH : HypH m k) :
    Module.finrank F (Submodule.span F
        (((Submodule.span ℤ (Set.range (intMatU m k).row)).map
          (castLin F (Fin (2 * k + 1) → Fin m)) : Submodule ℤ ((Fin (2 * k + 1) → Fin m) → F)) :
          Set ((Fin (2 * k + 1) → Fin m) → F))) = QkEven k m := by
  rw [finrank_span_map_rowLattice, rankOver_intMatU_of_H F heven h2 hH]

/-- **Proof of (iii)** in `q_quartic_assembly.md`: for even `m ≥ 2` with `H(m, k)`, `ℤ^n/L` is
free of rank `n − Q^e_k(m) = m^{2k+1} − Q^e_k(m)`, by the Lemma of `q_free_Z.md`. -/
theorem free_quotient_L_even (heven : Even m) (h2 : 2 ≤ m) (hH : HypH m k) :
    Module.Free ℤ (((Fin (2 * k + 1) → Fin m) → ℤ) ⧸ Submodule.span ℤ (Set.range (intMatU m k).row))
      ∧ Module.finrank ℤ
          (((Fin (2 * k + 1) → Fin m) → ℤ) ⧸ Submodule.span ℤ (Set.range (intMatU m k).row)) =
        m ^ (2 * k + 1) - QkEven k m := by
  obtain ⟨hfree, hrank⟩ := FreeZ.quotient_free_of_finrank_image
    (Submodule.span ℤ (Set.range (intMatU m k).row))
    (fun p _ => by
      rw [finrank_span_map_L_even _ heven h2 hH, finrank_span_map_L_even _ heven h2 hH])
  refine ⟨hfree, ?_⟩
  rw [hrank, finrank_span_map_L_even _ heven h2 hH]
  simp

/-- **Theorem (iii)** of `q_quartic_assembly.md`, integral part: for even `m ≥ 2` with `H(m, k)`,
`R/I_ℤ` is a free `ℤ`-module of rank `m^{2k+1} − Q^e_k(m)`. -/
theorem mainTheorem'_Z_even (heven : Even m) (h2 : 2 ≤ m) (hH : HypH m k) :
    Module.Free ℤ (RZ (2 * k + 1) m ⧸ IZ m k) ∧
      Module.finrank ℤ (RZ (2 * k + 1) m ⧸ IZ m k) = m ^ (2 * k + 1) - QkEven k m := by
  obtain ⟨hfree, hrank⟩ := free_quotient_L_even heven h2 hH
  let e := quotientEquivZ (k := k) (m := m) (by omega)
  exact ⟨Module.Free.of_equiv e.symm, e.finrank_eq.trans hrank⟩

/-- **Theorem (iii)** of `q_quartic_assembly.md`, field part: for even `m ≥ 2` with `H(m, k)` and
every field `F`, `dim_F F[G]/I_F = m^{2k+1} − Q^e_k(m)`, by (0) of `q_col_upper.md` and (ii). -/
theorem mainTheorem'_field_even (heven : Even m) (h2 : 2 ≤ m) (hH : HypH m k)
    (F : Type*) [Field F] :
    Module.finrank F (GA F (2 * k + 1) m ⧸ IK F m k) = m ^ (2 * k + 1) - QkEven k m := by
  haveI := finite_GA (F := F) (2 * k + 1) m (by omega)
  have h := Submodule.finrank_quotient_add_finrank ((IK F m k).restrictScalars F)
  rw [(theorem_ii F heven h2 hH).2, finrank_GA F _ _ (by omega)] at h
  rw [← (Submodule.Quotient.restrictScalarsEquiv F (IK F m k)).finrank_eq]
  omega

/-- **Theorem (iii)** of `q_quartic_assembly.md` (Main Theorem′ for an even degree, under `H`):
let `m ≥ 2` be even and assume `H(m, k)`. Then `R/I_ℤ` is a free `ℤ`-module of rank
`m^{2k+1} − Q^e_k(m)`, and for every field `F`, `dim_F F[G]/I_F = m^{2k+1} − Q^e_k(m)`.
(The field part is stated for `F` in any universe.) -/
theorem theorem_iii (heven : Even m) (h2 : 2 ≤ m) (hH : HypH m k) :
    (Module.Free ℤ (RZ (2 * k + 1) m ⧸ IZ m k) ∧
      Module.finrank ℤ (RZ (2 * k + 1) m ⧸ IZ m k) = m ^ (2 * k + 1) - QkEven k m) ∧
    ∀ (F : Type*) [Field F],
      Module.finrank F (GA F (2 * k + 1) m ⧸ IK F m k) = m ^ (2 * k + 1) - QkEven k m :=
  ⟨mainTheorem'_Z_even heven h2 hH, fun F _ => mainTheorem'_field_even heven h2 hH F⟩

end EvenAssembly

end
