module

public import RequestProject.ColOne.Empty

/-!
# Definitions for `q_oddbox_equality.md`

The ideal `ℳ = Σ_P D_P·C_N` of **(A1)** and the ideals `I_P·C` and `⋂_P I_P·C` of **(B2)** of
`q_oddbox_equality.md`. They are defined for every box `q` and every number `n` of variables; the
file uses `q = 2h + 2` (box `r = 2h + 1`) and `n = N = 2k + 2`.
-/

@[expose] public section

namespace OddEquality

variable (F : Type*) [Field F] (q : ℕ)

/-- **(A1)** of `q_oddbox_equality.md`: the ideal `ℳ := Σ_P D_P·C_n ⊆ C_n = Peel.C F q n`, spanned by
the products `D_P = Π_{{a<b} ∈ P} D(y_a, y_b)` (`ColOne.DPn`) over the perfect matchings `P` of
`Fin n`. (The file takes `q = 2h + 2` and `n = 2k + 2`.) -/
noncomputable def Mideal (n : ℕ) : Ideal (Peel.C F q n) :=
  Ideal.span (Set.range fun P : ColComp.PerfMatch (Fin n) => ColOne.DPn F q P)

/-- **(B2)** of `q_oddbox_equality.md`: for a perfect matching `P` of `Fin n`, the ideal
`I_P·C := (y_a + y_b : {a, b} ∈ P)·C ⊆ C = Peel.C F q n`. -/
noncomputable def IPC {n : ℕ} (P : ColComp.PerfMatch (Fin n)) : Ideal (Peel.C F q n) :=
  Ideal.span (Set.range fun a : Fin n => Tight.y F q a + Tight.y F q (P.1 a))

/-- **(B2)** of `q_oddbox_equality.md`: the intersection `⋂_P I_P·C` over all perfect matchings `P`
of `Fin n`. -/
noncomputable def Kint (n : ℕ) : Ideal (Peel.C F q n) :=
  ⨅ P : ColComp.PerfMatch (Fin n), IPC F q P

end OddEquality

end
