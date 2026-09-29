module

public import Mathlib

/-!
# The splitting of the group algebra by colourings (`q_col_splitting.md`, Lemma 6.1)

This file formalizes the **Setting** of `q_col_splitting.md` and part **(0)** of **Lemma 6.1**.

* The data of the Setting (`F`, `p`, `q = p^v`, `r`, `μ`) are bundled in `ColSplit.ColSetting`.
* `S = F[t_1, …, t_d]` is `MvPolynomial (Fin d) F`, the variable `t_i` being `X i`.
* `F[G] = S/(t_1^m − 1, …, t_d^m − 1)` is `ColSplit.GA F d m`.
* `J_c = ((t_1 − c_1)^q, …, (t_d − c_d)^q)` is `ColSplit.Jc q c` and `R_c = S/J_c` is
  `ColSplit.Rc F q c`.
* `π_c : F[G] → R_c` is `ColSplit.ColSetting.piC`.
-/

@[expose] public section

open MvPolynomial

namespace ColSplit

/-- **Setting** of `q_col_splitting.md`: a field `F` of characteristic `p` (a prime),
`q = p^v` with `v ≥ 1`, `r ≥ 1`, and a finite set `μ ⊆ F` with `|μ| = r` and
`X^r − 1 = Π_{ζ ∈ μ} (X − ζ)` in `F[X]`. (The number of variables `d ≥ 0` is kept separate.)
The fields `one_le_v`, `one_le_r` and `card_μ` are part of the Setting of the file, but are not
needed by the proofs of Lemma 6.1. -/
structure ColSetting (F : Type*) [Field F] where
  /-- The characteristic `p` of `F`. -/
  p : ℕ
  /-- `p` is a prime. -/
  hp : p.Prime
  /-- `F` has characteristic `p`. -/
  charP : CharP F p
  /-- The exponent `v` in `q = p^v`. -/
  v : ℕ
  /-- `v ≥ 1`. -/
  one_le_v : 1 ≤ v
  /-- The number `r` of roots of unity. -/
  r : ℕ
  /-- `r ≥ 1`. -/
  one_le_r : 1 ≤ r
  /-- The set `μ ⊆ F` of the `r`-th roots of unity. -/
  μ : Finset F
  /-- `|μ| = r`. -/
  card_μ : μ.card = r
  /-- `X^r − 1 = Π_{ζ ∈ μ} (X − ζ)` in `F[X]`. -/
  X_pow_sub_one : (Polynomial.X ^ r - 1 : Polynomial F) = ∏ ζ ∈ μ, (Polynomial.X - Polynomial.C ζ)

namespace ColSetting

variable {F : Type*} [Field F] (S : ColSetting F)

/-- **Setting** of `q_col_splitting.md`: `q = p^v`. -/
def q : ℕ := S.p ^ S.v

/-- **Setting** of `q_col_splitting.md`: `m := q·r`. -/
def m : ℕ := S.q * S.r

end ColSetting

variable (F : Type*) [Field F]

/-- **Setting** of `q_col_splitting.md`: the ideal `(t_1^m − 1, …, t_d^m − 1)` of
`S = F[t_1, …, t_d]`. -/
def gaIdeal (d m : ℕ) : Ideal (MvPolynomial (Fin d) F) :=
  Ideal.span (Set.range fun i : Fin d => (X i ^ m - 1 : MvPolynomial (Fin d) F))

/-- **Setting** of `q_col_splitting.md`: the group algebra `F[G] := S/(t_1^m − 1, …, t_d^m − 1)`. -/
abbrev GA (d m : ℕ) : Type _ := MvPolynomial (Fin d) F ⧸ gaIdeal F d m

variable {F}

/-- **Setting** of `q_col_splitting.md`: for a colouring `c`, the ideal
`J_c := ((t_1 − c_1)^q, …, (t_d − c_d)^q) ⊆ S`. -/
def Jc {d : ℕ} (q : ℕ) (c : Fin d → F) : Ideal (MvPolynomial (Fin d) F) :=
  Ideal.span (Set.range fun i : Fin d => ((X i - C (c i)) ^ q : MvPolynomial (Fin d) F))

variable (F)

/-- **Setting** of `q_col_splitting.md`: `R_c := S/J_c`. -/
abbrev Rc {d : ℕ} (q : ℕ) (c : Fin d → F) : Type _ := MvPolynomial (Fin d) F ⧸ Jc q c

variable {F}

namespace ColSetting

variable (S : ColSetting F)

/-- **Lemma 6.1 (0)**, first claim, of `q_col_splitting.md`:
`X^m − 1 = Π_{ξ ∈ μ} (X − ξ)^q` in `F[X]`. -/
theorem lemma61_0_poly :
    (Polynomial.X ^ S.m - 1 : Polynomial F) = ∏ ξ ∈ S.μ, (Polynomial.X - Polynomial.C ξ) ^ S.q := by
  haveI := S.charP
  haveI : Fact S.p.Prime := ⟨S.hp⟩
  rw [Finset.prod_pow, ← S.X_pow_sub_one, m, q, sub_pow_char_pow, one_pow, ← pow_mul,
    mul_comm]

/-- **Lemma 6.1 (0)**, second claim, of `q_col_splitting.md`: `t_i^m − 1 ∈ J_c` for every
colouring `c ∈ μ^d` and every `i`. -/
theorem lemma61_0_mem {d : ℕ} (c : Fin d → S.μ) (i : Fin d) :
    (X i ^ S.m - 1 : MvPolynomial (Fin d) F) ∈ Jc S.q (fun j => (c j : F)) := by
  have h := congrArg (Polynomial.aeval (X i : MvPolynomial (Fin d) F)) S.lemma61_0_poly
  simp only [map_sub, map_pow, Polynomial.aeval_X, map_one, map_prod, Polynomial.aeval_C,
    MvPolynomial.algebraMap_eq] at h
  rw [h]
  obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem
    (fun ξ => (X i - C ξ : MvPolynomial (Fin d) F) ^ S.q) (c i).2
  rw [hk]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩)

/-- **Lemma 6.1 (0)** of `q_col_splitting.md`: the `F`-algebra map `π_c : F[G] → R_c` induced by
the quotient map `S → R_c` (well defined since `(t_1^m − 1, …, t_d^m − 1) ⊆ J_c`). -/
noncomputable def piC {d : ℕ} (c : Fin d → S.μ) :
    GA F d S.m →ₐ[F] Rc F S.q (fun j => (c j : F)) :=
  Ideal.Quotient.factorₐ F (Ideal.span_le.2 (by
    rintro _ ⟨i, rfl⟩
    exact S.lemma61_0_mem c i))

/-- **Lemma 6.1 (0)** of `q_col_splitting.md`: `π_c` sends the class of `f ∈ S` to the class
of `f`. -/
theorem piC_mk {d : ℕ} (c : Fin d → S.μ) (f : MvPolynomial (Fin d) F) :
    S.piC c (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _ f := rfl

/-- **Lemma 6.1 (0)**, last claim, of `q_col_splitting.md`: `π_c : F[G] → R_c` is surjective. -/
theorem lemma61_0_surjective {d : ℕ} (c : Fin d → S.μ) : Function.Surjective (S.piC c) := by
  intro y
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact ⟨Ideal.Quotient.mk _ f, rfl⟩

end ColSetting

end ColSplit
