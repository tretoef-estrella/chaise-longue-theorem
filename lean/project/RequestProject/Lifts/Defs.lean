module

public import RequestProject.Tight.Main
public import RequestProject.Fibres.Defs

/-!
# Definitions for `q_P3_lifts.md` (every generator of a layer lifts to the right slice)

This file formalizes the **Setting** section of `q_P3_lifts.md`.  Everything else is reused
unchanged:
* from `RequestProject/Peel/` (`q_peeling_lemma.md`): the rings `C_m` (`Peel.C`), the
  identification `C_m = C_{m−1}[y_1]/(y_1^{q−1})` (`Peel.peelEquiv`), the slices `W_j(V)`
  (`Peel.W`) and parts (i) (`Peel.W_isIdeal`) and (ii) (`Peel.W_mono`);
* from `RequestProject/Chain/` (`q_chain_lemma.md`): partitions, `≼` (`WeakDom`), the options
  `opt_p(μ)` (`opt`) and parts (a), (b), (c);
* from `RequestProject/Monotone/` (`q_P2_monotone_options.md`): the size `|μ|` (`size`);
* from `RequestProject/Fibres/` (`q_P1_fibres.md`): `F_Λ(μ)` (`Fibres.FLam`);
* from `RequestProject/Tight/` (`q_P3_identities.md`): `D`, `Δ` (`Delta`), column lengths
  (`colLen`), tight patterns (`TightPattern`), their products (`TightPattern.prod`), the ideals
  `V_Λ(I)` (`VLam`, `VLamAll`) and parts (i)–(iv) of its Lemma.

The integer `h = (q − 1)/2` is a parameter `h` of the definitions below; in the Proposition it
is instantiated with `(q - 1) / 2`.
-/

@[expose] public section

namespace Lifts

open ChainLemma

/-- **Setting, "The partitions `Par_n`"** of `q_P3_lifts.md`:
`Par_n := {λ : |λ| ≤ n, |λ| ≡ n (mod 2), ℓ(λ) ≤ h}` (here `h = (q − 1)/2` is a parameter). -/
def Par (h n : ℕ) : Set Partition :=
  {lam | lam.size ≤ n ∧ lam.size % 2 = n % 2 ∧ lam.len ≤ h}

/-- **Setting, "Down-sets"** of `q_P3_lifts.md`: a set `Λ ⊆ Par_m` is a *down-set of `Par_m`* if
`λ ∈ Par_m`, `λ ≼ μ` and `μ ∈ Λ` imply `λ ∈ Λ`.  (Both conditions — `Λ ⊆ Par_m` and the relative
closure property — are part of the definition, exactly as in the file.) -/
def IsDownSetPar (h m : ℕ) (Λ : Set Partition) : Prop :=
  Λ ⊆ Par h m ∧ ∀ lam μ, lam ∈ Par h m → lam ≼ μ → μ ∈ Λ → lam ∈ Λ

/-- **Setting, "The layers"** of `q_P3_lifts.md`: for a down-set `Λ` of `Par_m` and
`0 ≤ i ≤ q − 2`, `Λ_i := {μ ∈ Par_{m−1} : F_Λ(μ) > i}` (with `F_Λ` of `q_P1_fibres.md`, which
uses `L = 2h`). -/
def layer (h m : ℕ) (Λ : Set Partition) (i : ℕ) : Set Partition :=
  {μ | μ ∈ Par h (m - 1) ∧ i < Fibres.FLam h Λ μ}

end Lifts

end
