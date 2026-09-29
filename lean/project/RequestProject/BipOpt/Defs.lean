module

public import RequestProject.Bip.Main
public import RequestProject.Lifts.Options

/-!
# The Setting of `q_bip_options.md`

Formalization of the **Setting** section of `q_bip_options.md` (§7.3 of the paper), reusing
unchanged:

* `q_bip_setting.md` (`RequestProject/Bip/`): shapes `λ(ξ, η)` (`Bip.shape`), `BPar_q(α, β)`
  (`Bip.BPar`), the product order `≼` (`Bip.BWeakDom`), down-sets (`Bip.IsDownSetB`), `Z_Λ`
  (`Bip.ZLam`), the fibres and the sets `Z_{>i}` of Lemma 7.1 (iv) (`Peel.fiber`, `Peel.Zgt`
  taken through `Bip.toTuple`) and Lemma 7.2 (0) (`Bip.lemma72_0`);
* `q_chain_lemma.md` (`RequestProject/Chain/`): partitions (`ChainLemma.Partition`), `S_t`,
  `≼` (`ChainLemma.WeakDom`), the operations `μ − e_j` (`subE`), `μ + e_j` (`addE`), `μ ⊔ 1`
  (`addOne`) and its parts (a), (b).

Encoding conventions.
* A tail `M' = (ξ', η) ∈ Ω^{α−1} × Ω^β` is a pair of functions `Fin (α - 1) → Ω`, `Fin β → Ω`;
  the point `(u, M')` is `consPt hα u M'`.
* Lemma 7.1 (iv) of `q_bip_setting.md` takes the fibres over the tuples `Fin (α + β - 1) → Ω`
  (all coordinates but `ξ_1` of `(ξ_1, …, ξ_α, η_1, …, η_β)`); the tail `M'` corresponds to the
  tuple `tailToTuple M' = (ξ'_1, …, ξ'_{α−1}, η_1, …, η_β)`.
-/

@[expose] public section

namespace Bip

open ChainLemma

/-- **Setting** of `q_bip_options.md`: the options `opt_p(μ)`, `p = 1, …, q`, of a pair of
partitions `μ = (μ_+, μ_−)` with `ℓ_+ = ℓ(μ_+)`, `ℓ_− = ℓ(μ_−)`:
* `opt_p(μ) := (μ_+, μ_− − e_p)` for `1 ≤ p ≤ ℓ_−` (the removals);
* `opt_p(μ) := (μ_+ ⊔ 1, μ_−)` for `ℓ_− < p ≤ q − ℓ_+` (the middle positions);
* `opt_p(μ) := (μ_+ + e_{q+1−p}, μ_−)` for `q − ℓ_+ < p ≤ q` (the additions).

(The values at `p = 0` or `p > q` are irrelevant; the hypothesis `ℓ_+ + ℓ_− ≤ q` is carried by
the theorems.) -/
def bopt (q : ℕ) (μ : Partition × Partition) (p : ℕ) : Partition × Partition :=
  if p ≤ μ.2.len then (μ.1, μ.2.subE p)
  else if p ≤ q - μ.1.len then (μ.1.addOne, μ.2)
  else (μ.1.addE (q + 1 - p), μ.2)

open Classical in
/-- **Setting** of `q_bip_options.md`: for a down-set `Λ` of `BPar_q(α, β)`,
`F_Λ(μ) := #{p ∈ {1, …, q} : opt_p(μ) ∈ Λ}`. -/
noncomputable def FLamB (q : ℕ) (Λ : Set (Partition × Partition)) (μ : Partition × Partition) :
    ℕ :=
  ((Finset.Icc 1 q).filter fun p => bopt q μ p ∈ Λ).card

/-- **Lemma 7.3 (ii)** of `q_bip_options.md`: the layers
`Λ_i := {ν ∈ BPar_q(α − 1, β) : F_Λ(ν) > i}`. -/
def LamLayer (q α β : ℕ) (Λ : Set (Partition × Partition)) (i : ℕ) :
    Set (Partition × Partition) :=
  {ν | ν ∈ BPar q (α - 1) β ∧ i < FLamB q Λ ν}

/-- **Setting** of `q_bip_options.md`: for a tail `M' = (ξ', η) ∈ Ω^{α−1} × Ω^β` and `u ∈ Ω`,
the point `(u, M') = ((u, ξ'_1, …, ξ'_{α−1}), η) ∈ Ω^α × Ω^β` (for `α ≥ 1`). -/
def consPt {Ω : Type*} {α β : ℕ} (hα : 1 ≤ α) (u : Ω) (M' : (Fin (α - 1) → Ω) × (Fin β → Ω)) :
    (Fin α → Ω) × (Fin β → Ω) :=
  (fun i => if h : (i : ℕ) = 0 then u else M'.1 ⟨i - 1, by omega⟩, M'.2)

/-- **Setting** of `q_bip_options.md` (with Lemma 7.1 (iv) of `q_bip_setting.md`): the tail
`M' = (ξ', η)` written as the single tuple `(ξ'_1, …, ξ'_{α−1}, η_1, …, η_β) ∈ Ω^{α+β−1}`, over
which the fibres `F(M')` and the sets `Z_{>i}` of Lemma 7.1 (iv) are taken. -/
def tailToTuple {Ω : Type*} {α β : ℕ} (M' : (Fin (α - 1) → Ω) × (Fin β → Ω)) :
    Fin (α + β - 1) → Ω :=
  fun i => if h : (i : ℕ) < α - 1 then M'.1 ⟨i, h⟩ else M'.2 ⟨i - (α - 1), by omega⟩

end Bip

end
