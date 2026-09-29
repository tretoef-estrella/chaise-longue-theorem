module

public import RequestProject.ColSplit.Main
public import RequestProject.ColSurv.Main
public import RequestProject.ColComp.Main
public import RequestProject.ColTensor.Blocks

/-!
# The tensor decomposition of each factor: Setting (`q_col_decomp.md`)

This file formalizes the **Setting** of `q_col_decomp.md` (§6.3 of the paper, before
Proposition 6.5): the ideal `I`, the **Identification** `R_c = B({1, …, d})`, the **Blocks of
variables** `W_1`, `W_ζ`, the **Pair factors** `f_{a,b}` and the **Block generators** `g_P`,
`g_σ` with the ideals `I_{c,1}`, `I_{c,ζ}`.

Conventions (reused unchanged from the earlier files):
* the data `F`, `p`, `q`, `r`, `μ` are bundled in `S : ColSplit.ColSetting F` (`q_col_splitting.md`);
* `d = 2k + 1`, the variables `t_1, …, t_d` are indexed by `Fin (2 * k + 1)` (the variable `t_a`,
  `1 ≤ a ≤ d`, being `X (a - 1)`), and `V = {0, 1, …, d}` is `Fin (2 * k + 2)`
  (`q_col_survivors.md`);
* a colouring is `c : Fin (2 * k + 1) → S.μ`, its extension by `c_0` is `ColSurv.cExt c`, and the
  classes `𝒞_ζ` are `ColComp.cls (ColSurv.cExt c) ζ` (`q_col_compatible.md`);
* the box rings `B(W)` and the maps `ι_{W',W}` are those of `q_col_tensor.md`, for the box
  setting `boxS S c` (exponent `q`, point `c`).
-/

@[expose] public section

open MvPolynomial

namespace ColDecomp

open ColSplit ColSurv ColComp ColTensor

open scoped Classical

variable {F : Type*} [Field F]

section Identification

variable {d : ℕ} (B : ColTensor.BoxSetting F d)

/-- **Identification** (Setting of `q_col_decomp.md`), forward map: `R_c → B({1, …, d})`,
`t_i ↦ t_i`, where `R_c = F[t_1, …, t_d]/((t_i − c_i)^q)`. -/
noncomputable def rcToBox : Rc F B.q B.c →ₐ[F] B.Box Finset.univ :=
  Ideal.Quotient.liftₐ _ (aeval fun i => B.t Finset.univ ⟨i, Finset.mem_univ i⟩) (by
    intro f hf
    have hle : Jc B.q B.c ≤ RingHom.ker
        (aeval fun i => B.t Finset.univ ⟨i, Finset.mem_univ i⟩ : MvPolynomial (Fin d) F →ₐ[F] _) := by
      rw [Jc, Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker]
      change aeval _ ((X i - C (B.c i)) ^ B.q) = 0
      rw [map_pow, map_sub, aeval_X, aeval_C]
      exact B.t_sub_pow Finset.univ ⟨i, Finset.mem_univ i⟩
    exact hle hf)

/-- **Identification** (Setting of `q_col_decomp.md`), backward map: `B({1, …, d}) → R_c`,
`t_i ↦ t_i`. -/
noncomputable def boxToRc : B.Box Finset.univ →ₐ[F] Rc F B.q B.c :=
  B.boxLift Finset.univ (fun i => Ideal.Quotient.mk _ (X i.1)) (by
    intro i
    rw [show algebraMap F (Rc F B.q B.c) (B.c i) = Ideal.Quotient.mk _ (C (B.c i)) from rfl,
      ← map_sub, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span ⟨i.1, rfl⟩)

/-- **Identification** of `q_col_decomp.md`: `R_c = B({1, …, d})` (both are
`F[t_1, …, t_d]/((t_i − c_i)^q)`), as an isomorphism of `F`-algebras sending `t_i` to `t_i`. -/
noncomputable def rcEquiv : Rc F B.q B.c ≃ₐ[F] B.Box Finset.univ :=
  AlgEquiv.ofAlgHom (rcToBox B) (boxToRc B)
    (B.box_algHom_ext fun i => by simp [rcToBox, boxToRc])
    (Ideal.Quotient.algHom_ext _ (MvPolynomial.algHom_ext fun i => by
      simp [rcToBox, boxToRc]))

/-- **Identification** of `q_col_decomp.md`: the isomorphism `R_c = B({1, …, d})` sends the
class of `t_i` to `t_i`. -/
@[simp] theorem rcEquiv_mk_X (i : Fin d) :
    rcEquiv B (Ideal.Quotient.mk _ (X i)) = B.t Finset.univ ⟨i, Finset.mem_univ i⟩ := by
  simp [rcEquiv, rcToBox]

end Identification

variable (S : ColSetting F) {k : ℕ}

/-- **Setting** of `q_col_decomp.md`: the box rings of `q_col_tensor.md` are taken with the
exponent `q` and the point `c = (c_1, …, c_d)` of the colouring. -/
def boxS (c : Fin (2 * k + 1) → S.μ) : BoxSetting F (2 * k + 1) where
  q := S.q
  one_le_q := Setting.one_le_q S
  c := fun j => (c j : F)

/-- **Setting** of `q_col_decomp.md`: the ideal `I := (ψ_J : J a matching) ⊆ F[G]`. -/
noncomputable def idealI (k : ℕ) : Ideal (GA F (2 * k + 1) S.m) :=
  Ideal.span (Set.range (psi S k))

/-- **Setting** of `q_col_decomp.md`: a subset `T ⊆ V = {0, …, d}` read as a set of variable
indices, i.e. `T ∖ {0} ⊆ {1, …, d}` (the index `a = j + 1` corresponds to the variable `X j`). -/
def varSet (T : Finset (Fin (2 * k + 2))) : Finset (Fin (2 * k + 1)) :=
  Finset.univ.filter fun j => j.succ ∈ T

/-- **Blocks of variables** (Setting of `q_col_decomp.md`): `W_1 := 𝒞_1 ∖ {0}`. -/
noncomputable def W1 (c : Fin (2 * k + 1) → S.μ) : Finset (Fin (2 * k + 1)) :=
  varSet (cls (cExt c) 1)

/-- **Blocks of variables** (Setting of `q_col_decomp.md`): for `ζ ∈ ℛ`,
`W_ζ := (𝒞_ζ ∪ 𝒞_{ζ^{−1}}) ∖ {0}`. -/
noncomputable def Wz (c : Fin (2 * k + 1) → S.μ) (ζ : F) : Finset (Fin (2 * k + 1)) :=
  varSet (cls (cExt c) ζ ∪ cls (cExt c) ζ⁻¹)

/-- **Setting** of `q_col_decomp.md`: the variables `t_a ∈ B(W)`, indexed by `a ∈ V`; for
`a = j + 1` with `j ∈ W` this is the class of `t_a`. (The value at `a = 0`, and at variables
outside `W`, is an unused dummy value `0`: `0` is never a variable, and all the variables that
occur in the block generators lie in the block.) -/
noncomputable def tB (c : Fin (2 * k + 1) → S.μ) (W : Finset (Fin (2 * k + 1))) :
    Fin (2 * k + 2) → (boxS S c).Box W :=
  Fin.cases 0 fun j => if h : j ∈ W then (boxS S c).t W ⟨j, h⟩ else 0

/-- **Pair factors** (Setting of `q_col_decomp.md`): for a pair `{a, b}` of elements of `V` with
`a < b`, `f_{a,b} := t_b − 1` if `a = 0`, and `f_{a,b} := (t_b − 1)·(t_a t_b − 1)^{q−1}` if
`a > 0`; here `t : V → A` gives the elements `t_a` of the ring `A` in which it is computed. -/
def pairF {A : Type*} [CommRing A] (q : ℕ) (t : Fin (2 * k + 2) → A) (a b : Fin (2 * k + 2)) :
    A :=
  if a = 0 then t b - 1 else (t b - 1) * (t a * t b - 1) ^ (q - 1)

/-- **Block generators** (Setting of `q_col_decomp.md`): for a perfect matching `P` of `𝒞_1` (a
fixed-point-free involution), `g_P ∈ B(W_1)` is the product of `f_{a,b}` over the pairs
`{a < b}` of `P` (each pair recorded by its smaller element `a`, with `b = P(a)`). -/
noncomputable def gP (c : Fin (2 * k + 1) → S.μ) (P : PerfMatch (cls (cExt c) 1)) :
    (boxS S c).Box (W1 S c) :=
  ∏ x ∈ Finset.univ.filter (fun x => x.1 < (P.1 x).1), pairF S.q (tB S c (W1 S c)) x.1 (P.1 x).1

/-- **Block generators** (Setting of `q_col_decomp.md`): for `ζ ∈ ℛ` and a bijection
`σ : 𝒞_ζ → 𝒞_{ζ^{−1}}`, `g_σ ∈ B(W_ζ)` is the product of `f_{min(a,σ(a)), max(a,σ(a))}` over
`a ∈ 𝒞_ζ`. -/
noncomputable def gσ (c : Fin (2 * k + 1) → S.μ) (ζ : F) (σ : cls (cExt c) ζ ≃ cls (cExt c) ζ⁻¹) :
    (boxS S c).Box (Wz S c ζ) :=
  ∏ a : cls (cExt c) ζ, pairF S.q (tB S c (Wz S c ζ)) (min a.1 (σ a).1) (max a.1 (σ a).1)

/-- **Block generators** (Setting of `q_col_decomp.md`): `I_{c,1} := (g_P : P) ⊆ B(W_1)`. -/
noncomputable def Ic1 (c : Fin (2 * k + 1) → S.μ) : Ideal ((boxS S c).Box (W1 S c)) :=
  Ideal.span (Set.range (gP S c))

/-- **Block generators** (Setting of `q_col_decomp.md`): `I_{c,ζ} := (g_σ : σ) ⊆ B(W_ζ)`. -/
noncomputable def Icz (c : Fin (2 * k + 1) → S.μ) (ζ : F) : Ideal ((boxS S c).Box (Wz S c ζ)) :=
  Ideal.span (Set.range (gσ S c ζ))

end ColDecomp

end
