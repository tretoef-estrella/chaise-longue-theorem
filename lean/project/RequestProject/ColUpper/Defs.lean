module

public import RequestProject.ColSurv.Defs

/-!
# Setting of `q_col_upper.md`

This file formalizes the **Setting** of `q_col_upper.md` (the upper bound (6.1)).

* `K` is any field, `m` any natural number (`m ≥ 1` is assumed where needed), `d = 2k + 1`, and
  `K[G] = K[t_1, …, t_d]/(t_1^m − 1, …, t_d^m − 1)` is `ColSplit.GA K (2 * k + 1) m`
  (`q_col_splitting.md`).
* `ColUpper.tU K m k a` is `t_a ∈ K[G]` for `a ∈ V = {0, …, 2k+1} = Fin (2 * k + 2)`
  (`t_0` is the dummy value `0`, which never occurs).
* `ColUpper.psiG K m J` is `ψ_J`, given by the same formula as `ColSurv.psi` of
  `q_col_survivors.md` (with `φ = ColSurv.phi m`), now for any field and any `m`;
  `ColUpper.psi_eq_psiG` checks that for a `ColSetting` it is `ColSurv.psi`.
* `ColUpper.IK K m k` is the ideal `I_K = (ψ_J : J a matching of V) ⊆ K[G]`.
-/

@[expose] public section

open MvPolynomial

namespace ColUpper

open ColSplit ColSurv

variable (K : Type*) [Field K]

/-- **Setting** of `q_col_upper.md`: the elements `t_a ∈ K[G]` for `a ∈ V = {0, 1, …, 2k+1}`
(`Fin (2 * k + 2)`): for `a = j + 1` the class of the variable `X j`; `t_0` is a dummy value `0`
that never occurs in `ψ_J`. -/
noncomputable def tU (m k : ℕ) : Fin (2 * k + 2) → GA K (2 * k + 1) m :=
  Fin.cases 0 (fun j => Ideal.Quotient.mk _ (X j))

/-- **Setting** of `q_col_upper.md`: for a matching `J` of `V`,
`ψ_J := Π_{a < J(a)} (t_{J(a)} − 1) · Π_{0 < a < J(a)} φ(t_a t_{J(a)}) ∈ K[G]`, with
`φ(u) = u^{m−1} + ⋯ + u + 1` (`ColSurv.phi`). This is the same formula as `ColSurv.psi` of
`q_col_survivors.md`, for any field `K` and any `m`. -/
noncomputable def psiG (m : ℕ) {k : ℕ} (J : BallotBound.Matching k) : GA K (2 * k + 1) m :=
  (∏ a ∈ Finset.univ.filter (fun a => a < J.1 a), (tU K m k (J.1 a) - 1)) *
    ∏ a ∈ Finset.univ.filter (fun a => 0 < a ∧ a < J.1 a), phi m (tU K m k a * tU K m k (J.1 a))

/-- **Setting** of `q_col_upper.md`: the ideal `I_K := (ψ_J : J a matching of V) ⊆ K[G]`. -/
noncomputable def IK (m k : ℕ) : Ideal (GA K (2 * k + 1) m) :=
  Ideal.span (Set.range (psiG K m (k := k)))

variable {K}

/-- **Setting** of `q_col_upper.md` (compatibility with `q_col_survivors.md`): for a
`ColSetting` `S` over `F`, the element `ψ_J` of `q_col_survivors.md` (`ColSurv.psi`) is
`psiG F S.m J`. -/
theorem psi_eq_psiG (S : ColSetting K) {k : ℕ} (J : BallotBound.Matching k) :
    ColSurv.psi S k J = psiG K S.m J := rfl

end ColUpper

end
