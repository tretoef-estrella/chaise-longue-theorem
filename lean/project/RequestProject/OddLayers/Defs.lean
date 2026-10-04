module

public import RequestProject.OddShapes.Main

/-!
# Definition of the layers (`q_oddbox_layers.md`, Part L)

This file formalizes the **Definition (layers)** of Part L of `q_oddbox_layers.md`.

Everything else is reused unchanged from `RequestProject/OddShapes/` (the formalization of
`q_oddbox_shapes.md`): `OddSetting`, `Shape`, `Sh`, `optS`, `comp`, `FS`, `ZS`, `IsInterlaced`.
-/

@[expose] public section

namespace OddLayers

open ChainLemma ChainLemma.Partition Fibres OddShapes

/-- **Part L, Definition (layers)** of `q_oddbox_layers.md`: for a set `Λ` of shapes, `m ≥ 1`
and `i ≥ 0`, the layer `Λ_i := {σ ∈ Sh_{m−1} : F_Λ(σ) > i}`. -/
def layerS (h m : ℕ) (Λ : Set Shape) (i : ℕ) : Set Shape :=
  {σ | σ ∈ Sh h (m - 1) ∧ i < FS h Λ σ}

end OddLayers
