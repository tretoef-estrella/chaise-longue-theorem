module

public import RequestProject.Tight.Defs

/-!
# The Setting of `q_bip_setting.md`

Formalization of the **Setting** section of `q_bip_setting.md` (the bipartite setting,
§7.1–§7.2 of the paper), reusing unchanged:

* `q_peeling_lemma.md` (`RequestProject/Peel/`): the ring `C_m = Peel.C F q m`, its slices
  `Peel.W`, the fibres `Peel.fiber` and the sets `Peel.Zgt`;
* `q_chain_lemma.md` (`RequestProject/Chain/`): partitions `ChainLemma.Partition`, the partial
  sums `S_t` (`ChainLemma.Partition.S`), weak dominance `≼` (`ChainLemma.WeakDom`);
* `q_P2_monotone_options.md` (`RequestProject/Monotone/`): the size `|μ|`
  (`ChainLemma.Partition.size`);
* `q_P3_identities.md` (`RequestProject/Tight/`): the Vandermonde `Δ(B)` (`Tight.vand`) and the
  column lengths `λ'_c` (`Tight.colLen`).

Encoding conventions.
* `R_{α,β}` is `Peel.C F (q + 1) (α + β)`: the variable `y_i` of `q_peeling_lemma.md`
  is `X (i - 1)` with `i - 1 : Fin (α + β)`; the first `α` variables are named `x_1, …, x_α`
  (`x F q i = y_i` for `i : Fin α`, via `Fin.castAdd`) and the last `β` are named
  `z_1, …, z_β` (`z F q l = y_{α + l}` for `l : Fin β`, via `Fin.natAdd`).
* Index sets `[α]`, `[β]` are `Fin α`, `Fin β` (index `i` is `i - 1`).
* A point `(ξ, η) ∈ Ω^α × Ω^β` is a pair of functions `Fin α → Ω`, `Fin β → Ω`.
* The ring `R_{α−1,β}` receiving the slices is identified with `Peel.C F (q+1) (α+β−1)` through
  the renaming isomorphism `castC` (the two index sets `α + β − 1` and `(α − 1) + β` are equal
  for `α ≥ 1`, but not definitionally).
-/

@[expose] public section

open MvPolynomial

namespace Bip

open ChainLemma Tight

set_option synthInstance.maxHeartbeats 200000

/-! ### The ring -/

section Ring

variable (F : Type*) [Field F] (q : ℕ)

/-- **Setting, "The ring"** of `q_bip_setting.md`:
`R_{α,β} := F[x_1, …, x_α, z_1, …, z_β]/(x_i^q, z_l^q)`, which is the ring `C_{α+β}` of
`q_peeling_lemma.md` with `q + 1` in place of `q` (box exponent `(q + 1) − 1 = q`). -/
abbrev R (α β : ℕ) : Type _ := Peel.C F (q + 1) (α + β)

/-- **Setting, "The ring"** of `q_bip_setting.md`: the variable `x_i ∈ R_{α,β}` (`i ∈ [α]`),
i.e. the variable `y_i` of `C_{α+β}` (the class of `X (Fin.castAdd β i)`). -/
noncomputable def x {α β : ℕ} (i : Fin α) : R F q α β :=
  Ideal.Quotient.mk _ (X (Fin.castAdd β i))

/-- **Setting, "The ring"** of `q_bip_setting.md`: the variable `z_l ∈ R_{α,β}` (`l ∈ [β]`),
i.e. the variable `y_{α+l}` of `C_{α+β}` (the class of `X (Fin.natAdd α l)`). -/
noncomputable def z {α β : ℕ} (l : Fin β) : R F q α β :=
  Ideal.Quotient.mk _ (X (Fin.natAdd α l))

/-- The renaming isomorphism `C_m ≅ C_n` for `m = n` (used in **Lemma 7.1** of
`q_bip_setting.md` to regard the slices `W_j(V) ⊆ C_{α+β−1}` of `q_peeling_lemma.md` as
subspaces of `R_{α−1,β} = C_{(α−1)+β}`). -/
noncomputable def castC {m n : ℕ} (h : m = n) : Peel.C F (q + 1) m ≃ₐ[F] Peel.C F (q + 1) n := by
  subst h; exact AlgEquiv.refl

/-- **Lemma 7.1** of `q_bip_setting.md`: the slice `W_j(V) ⊆ R_{α−1,β}` of an ideal `V` of
`R_{α,β}` (for `α ≥ 1`): the slice `W_j(V) ⊆ C_{α+β−1}` of `q_peeling_lemma.md` with `q + 1` in
place of `q`, peeling the first variable `y_1 = x_1`, transported to `R_{α−1,β}` by `castC`. -/
noncomputable def Wslice {α β : ℕ} (hα : 1 ≤ α) (V : Ideal (R F q α β)) (j : ℕ) :
    Submodule F (R F q (α - 1) β) :=
  (Peel.W (m := α + β) (by omega) V j).map
    (castC F q (show α + β - 1 = α - 1 + β by omega)).toLinearMap

/-- **Lemma 7.1 (iv)** of `q_bip_setting.md`: the identification
`Ω^α × Ω^β ≅ Ω^{α+β}`, `(ξ, η) ↦ (ξ_1, …, ξ_α, η_1, …, η_β)`, under which the fibres `F(M')`
and the sets `Z_{>i}` of `q_peeling_lemma.md` (with the tail `M'` being all coordinates but
`ξ_1`) are taken. -/
def toTuple {Ω : Type*} {α β : ℕ} : (Fin α → Ω) × (Fin β → Ω) ↪ (Fin (α + β) → Ω) where
  toFun p := Fin.append p.1 p.2
  inj' := by
    intro p p' h
    have h1 := congrArg (fun f => fun i : Fin α => f (Fin.castAdd β i)) h
    have h2 := congrArg (fun f => fun l : Fin β => f (Fin.natAdd α l)) h
    simp only [Fin.append_left, Fin.append_right] at h1 h2
    exact Prod.ext h1 h2

end Ring

/-! ### Shapes -/

namespace Partition'

/-- The partition whose parts are the positive elements of a multiset `s` of naturals (sorted
into weakly decreasing order).  Used to form the partitions `λ_+`, `λ_−` in **Setting,
"Shapes"** of `q_bip_setting.md`. -/
def ofMultiset (s : Multiset ℕ) : Partition where
  parts := (s.filter (0 < ·)).sort (· ≥ ·)
  sorted := Multiset.pairwise_sort _ _
  pos := by
    intro a ha
    rw [Multiset.mem_sort, Multiset.mem_filter] at ha
    exact ha.2

/-- The empty partition `∅`, used in **Lemma 7.2 (i), (ii)** of `q_bip_setting.md` (the roots
`(∅, ∅)` and `((1), ∅)`). -/
def empty : Partition := ⟨[], List.Pairwise.nil, by simp⟩

/-- The one-part partition `(1)`, used in **Lemma 7.2 (ii)** of `q_bip_setting.md` (the root
`((1), ∅)`). -/
def one : Partition := ⟨[1], List.pairwise_singleton _ _, by simp⟩

end Partition'

section Shape

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- **Setting, "Shapes"** of `q_bip_setting.md`: the count `X(u) := #{i : ξ_i = u}` (and
likewise `Y(u) := cnt η u`) of a tuple. -/
def cnt {n : ℕ} (ξ : Fin n → Ω) (u : Ω) : ℕ := (Finset.univ.filter fun i => ξ i = u).card

/-- **Setting, "Shapes"** of `q_bip_setting.md`: `λ_+`, the partition whose parts are the numbers
`X(u) − Y(u)` for the `u ∈ Ω` with `X(u) > Y(u)` (with multiplicity). -/
def shapePlus {α β : ℕ} (ξ : Fin α → Ω) (η : Fin β → Ω) : Partition :=
  Partition'.ofMultiset
    ((Finset.univ.filter fun u => cnt η u < cnt ξ u).val.map fun u => cnt ξ u - cnt η u)

/-- **Setting, "Shapes"** of `q_bip_setting.md`: `λ_−`, the partition whose parts are the numbers
`Y(u) − X(u)` for the `u ∈ Ω` with `Y(u) > X(u)` (with multiplicity). -/
def shapeMinus {α β : ℕ} (ξ : Fin α → Ω) (η : Fin β → Ω) : Partition :=
  Partition'.ofMultiset
    ((Finset.univ.filter fun u => cnt ξ u < cnt η u).val.map fun u => cnt η u - cnt ξ u)

/-- **Setting, "Shapes"** of `q_bip_setting.md`: the shape `λ(ξ, η) := (λ_+, λ_−)` of a point
`(ξ, η) ∈ Ω^α × Ω^β`. -/
def shape {α β : ℕ} (ξ : Fin α → Ω) (η : Fin β → Ω) : Partition × Partition :=
  (shapePlus ξ η, shapeMinus ξ η)

end Shape

/-! ### Pairs of partitions -/

/-- **Setting, "Pairs of partitions"** of `q_bip_setting.md`: `BPar_q(α, β)`, the set of pairs
`(λ_+, λ_−)` of partitions with `|λ_+| − |λ_−| = α − β` (in `ℤ`), `|λ_+| + |λ_−| ≤ α + β` and
`ℓ(λ_+) + ℓ(λ_−) ≤ q`. -/
def BPar (q α β : ℕ) : Set (Partition × Partition) :=
  {p | (p.1.size : ℤ) - p.2.size = (α : ℤ) - β ∧ p.1.size + p.2.size ≤ α + β ∧
    p.1.len + p.2.len ≤ q}

/-- **Setting, "Pairs of partitions"** of `q_bip_setting.md`: the product order,
`(λ_+, λ_−) ≼ (μ_+, μ_−)` iff `λ_+ ≼ μ_+` and `λ_− ≼ μ_−`. -/
def BWeakDom (lam μ : Partition × Partition) : Prop := lam.1 ≼ μ.1 ∧ lam.2 ≼ μ.2

/-- **Setting, "Pairs of partitions"** of `q_bip_setting.md`: a down-set of `BPar_q(α, β)` is a
set `Λ ⊆ BPar_q(α, β)` such that `λ ∈ BPar_q(α, β)`, `λ ≼ μ` and `μ ∈ Λ` imply `λ ∈ Λ`. -/
def IsDownSetB (q α β : ℕ) (Λ : Set (Partition × Partition)) : Prop :=
  Λ ⊆ BPar q α β ∧ ∀ lam μ, lam ∈ BPar q α β → BWeakDom lam μ → μ ∈ Λ → lam ∈ Λ

/-- **Setting, "Pairs of partitions"** of `q_bip_setting.md`:
`Z_Λ := {(ξ, η) ∈ Ω^α × Ω^β : λ(ξ, η) ∈ Λ}`. -/
noncomputable def ZLam (Ω : Type*) [Fintype Ω] [DecidableEq Ω] (α β : ℕ)
    (Λ : Set (Partition × Partition)) : Finset ((Fin α → Ω) × (Fin β → Ω)) :=
  open Classical in Finset.univ.filter fun p => shape p.1 p.2 ∈ Λ

/-! ### Tight patterns -/

/-- **Setting, "Tight patterns"** of `q_bip_setting.md`: a tight pattern of
`λ = (λ_+, λ_−)` on `([α], [β])` consists of
* a set `P` (`pairs`) of `α − |λ_+|` pairs `(i, l) ∈ [α] × [β]`, with the `i` pairwise distinct
  and the `l` pairwise distinct;
* blocks `B^+_1, …, B^+_{λ_{+,1}}` (`blocksX c`, `c = 1, …, λ_{+,1}`) partitioning
  `[α] ∖ {i : (i, l) ∈ P}` (pairwise disjoint, with union this set), with `|B^+_c| = (λ_+)'_c`;
* blocks `B^−_1, …, B^−_{λ_{−,1}}` (`blocksZ c`, `c = 1, …, λ_{−,1}`) partitioning
  `[β] ∖ {l : (i, l) ∈ P}`, with `|B^−_c| = (λ_−)'_c`.

(The values of `blocksX`, `blocksZ` outside `1, …, λ_{±,1}` play no role.) -/
structure BTightPattern (lam : Partition × Partition) (α β : ℕ) where
  /-- The set `P` of pairs `(i, l)`. -/
  pairs : Finset (Fin α × Fin β)
  /-- There are `α − |λ_+|` pairs. -/
  card_pairs : pairs.card = α - lam.1.size
  /-- The `i` are pairwise distinct. -/
  inj_fst : Set.InjOn Prod.fst (pairs : Set (Fin α × Fin β))
  /-- The `l` are pairwise distinct. -/
  inj_snd : Set.InjOn Prod.snd (pairs : Set (Fin α × Fin β))
  /-- The `x`-blocks `B^+_c`. -/
  blocksX : ℕ → Finset (Fin α)
  /-- `|B^+_c| = (λ_+)'_c` for `c = 1, …, λ_{+,1}`. -/
  card_blockX : ∀ c ∈ Finset.Icc 1 (lam.1.row 1), (blocksX c).card = colLen lam.1 c
  /-- The `x`-blocks are pairwise disjoint. -/
  blocksX_disjoint : (↑(Finset.Icc 1 (lam.1.row 1)) : Set ℕ).PairwiseDisjoint blocksX
  /-- The `x`-blocks cover exactly `[α] ∖ {i : (i, l) ∈ P}`. -/
  coverX : (Finset.Icc 1 (lam.1.row 1)).sup blocksX = Finset.univ \ pairs.image Prod.fst
  /-- The `z`-blocks `B^−_c`. -/
  blocksZ : ℕ → Finset (Fin β)
  /-- `|B^−_c| = (λ_−)'_c` for `c = 1, …, λ_{−,1}`. -/
  card_blockZ : ∀ c ∈ Finset.Icc 1 (lam.2.row 1), (blocksZ c).card = colLen lam.2 c
  /-- The `z`-blocks are pairwise disjoint. -/
  blocksZ_disjoint : (↑(Finset.Icc 1 (lam.2.row 1)) : Set ℕ).PairwiseDisjoint blocksZ
  /-- The `z`-blocks cover exactly `[β] ∖ {l : (i, l) ∈ P}`. -/
  coverZ : (Finset.Icc 1 (lam.2.row 1)).sup blocksZ = Finset.univ \ pairs.image Prod.snd

variable (F : Type*) [Field F] (q : ℕ)

/-- **Setting, "Tight patterns"** of `q_bip_setting.md`: the **product** of a tight pattern,
`Π_{(i,l) ∈ P} (x_i − z_l)^{q−1} · Π_c Δ(x_{B^+_c}) · Π_c Δ(z_{B^−_c}) ∈ R_{α,β}`, where
`Δ(x_B) = Π_{c<c' in B}(x_{c'} − x_c)` is `Tight.vand` of `q_P3_identities.md`. -/
noncomputable def BTightPattern.prod {lam : Partition × Partition} {α β : ℕ}
    (T : BTightPattern lam α β) : R F q α β :=
  (∏ p ∈ T.pairs, (x F q p.1 - z F q p.2) ^ (q - 1)) *
    (∏ c ∈ Finset.Icc 1 (lam.1.row 1), vand (x F q) (T.blocksX c)) *
    ∏ c ∈ Finset.Icc 1 (lam.2.row 1), vand (z F q) (T.blocksZ c)

/-- **Setting, "Tight patterns"** of `q_bip_setting.md`: `V_Λ ⊆ R_{α,β}`, the ideal generated by
the products of all tight patterns of all elements of `Λ`. -/
noncomputable def VLamB (α β : ℕ) (Λ : Set (Partition × Partition)) : Ideal (R F q α β) :=
  Ideal.span {g | ∃ lam ∈ Λ, ∃ T : BTightPattern lam α β, T.prod F q = g}

/-! ### The root ideals and counts -/

/-- **Setting, "The root ideals and counts"** of `q_bip_setting.md`: `I^{bal}_a ⊆ R_{a,a}`, the
ideal generated by `Π_{i=1}^{a} (x_i − z_{σ(i)})^{q−1}`, `σ` a permutation of `[a]`. -/
noncomputable def Ibal (a : ℕ) : Ideal (R F q a a) :=
  Ideal.span (Set.range fun σ : Equiv.Perm (Fin a) =>
    ∏ i : Fin a, (x F q i - z F q (σ i)) ^ (q - 1))

/-- **Setting, "The root ideals and counts"** of `q_bip_setting.md`: `I^{ph}_a ⊆ R_{a+1,a}`, the
ideal generated by `Π_{i ≠ i_0} (x_i − z_{σ(i)})^{q−1}`, for `i_0 ∈ [a+1]` and
`σ : [a+1] ∖ {i_0} → [a]` a bijection. -/
noncomputable def Iph (a : ℕ) : Ideal (R F q (a + 1) a) :=
  Ideal.span {g | ∃ (i₀ : Fin (a + 1)) (σ : {i // i ≠ i₀} ≃ Fin a),
    g = ∏ i : {i // i ≠ i₀}, (x F q i.1 - z F q (σ i)) ^ (q - 1)}

/-- **Setting, "The root ideals and counts"** of `q_bip_setting.md`:
`N_{bal}(a, q) := #{(ξ, η) ∈ Ω^a × Ω^a : X = Y}` (the multisets of values of `ξ` and `η` are
equal), computed with the `q`-element set `Ω = Fin q`. -/
def Nbal (a q : ℕ) : ℕ :=
  (Finset.univ.filter fun p : (Fin a → Fin q) × (Fin a → Fin q) =>
    ∀ u, cnt p.1 u = cnt p.2 u).card

/-- **Setting, "The root ideals and counts"** of `q_bip_setting.md`:
`N_{ph}(a, q) := #{(ξ, η) ∈ Ω^{a+1} × Ω^a : Y(u) ≤ X(u) for every u}`, computed with the
`q`-element set `Ω = Fin q`. -/
def Nph (a q : ℕ) : ℕ :=
  (Finset.univ.filter fun p : (Fin (a + 1) → Fin q) × (Fin a → Fin q) =>
    ∀ u, cnt p.2 u ≤ cnt p.1 u).card

end Bip

end
