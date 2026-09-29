module

public import RequestProject.ColSplit.Basic
public import RequestProject.Ballot.Defs

/-!
# Setting and elementary facts for Lemma 6.2 (`q_col_survivors.md`)

This file formalizes the **Setting** of `q_col_survivors.md` together with the facts listed there
as *"Elementary facts used freely"* and the *Frobenius in `R_c`* and *Units* paragraphs of the
**Proof** of Lemma 6.2.

Conventions (reused from `q_col_splitting.md`, formalized in `RequestProject/ColSplit/Basic.lean`,
and from the ballot files `RequestProject/Ballot/Defs.lean`):
* `d = 2k + 1`, the variables of `S = F[t_1, …, t_d]` are indexed by `Fin (2 * k + 1)`, the
  variable `t_a` (`1 ≤ a ≤ 2k+1`) being `X (a - 1)`;
* the ground set `{0, 1, …, 2k+1}` of the matchings is `Fin (2 * k + 2)`, and a matching is a
  fixed-point-free involution `J` of it (`BallotBound.Matching k`);
* `F[G]` is `ColSplit.GA F (2 * k + 1) S.m`, `R_c` is `ColSplit.Rc F S.q c` and
  `π_c` is `S.piC c`.
-/

@[expose] public section

open MvPolynomial

namespace ColSurv

open ColSplit

variable {F : Type*} [Field F]

section general

/-- **Setting** of `q_col_survivors.md`: `φ(u) := u^{m−1} + ⋯ + u + 1` (for `u` in any ring). -/
def phi {A : Type*} [Semiring A] (m : ℕ) (u : A) : A := ∑ s ∈ Finset.range m, u ^ s

/-- `φ` commutes with ring homomorphisms (used implicitly in `q_col_survivors.md` whenever
`φ(t_a t_{J(a)})` is read in `F[G]` or in `R_c`). -/
theorem map_phi {A B H : Type*} [Semiring A] [Semiring B] [FunLike H A B] [RingHomClass H A B]
    (f : H) (m : ℕ) (u : A) :
    f (phi m u) = phi m (f u) := by
  simp [phi, map_sum, map_pow]

end general

namespace Setting

variable (S : ColSetting F)

/-- *Elementary facts* of the **Setting** of `q_col_survivors.md`: the elements of `μ` are exactly
the roots of `X^r − 1`. -/
theorem mem_μ_iff (x : F) : x ∈ S.μ ↔ x ^ S.r = 1 := by
  have h := congrArg (Polynomial.eval x) S.X_pow_sub_one
  simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one,
    Polynomial.eval_prod, Polynomial.eval_C] at h
  constructor
  · intro hx
    have : ∏ ζ ∈ S.μ, (x - ζ) = 0 := Finset.prod_eq_zero hx (sub_self x)
    rw [this] at h
    exact sub_eq_zero.1 h
  · intro hx
    rw [hx, sub_self, eq_comm, Finset.prod_eq_zero_iff] at h
    obtain ⟨ζ, hζ, h0⟩ := h
    rwa [sub_eq_zero.1 h0]

/-- *Elementary facts* of the **Setting** of `q_col_survivors.md`: `1 ∈ μ`. -/
theorem one_mem_μ : (1 : F) ∈ S.μ := (Setting.mem_μ_iff S 1).2 (one_pow _)

/-- *Elementary facts* of the **Setting** of `q_col_survivors.md`: `μ` is closed under products. -/
theorem mul_mem_μ {x y : F} (hx : x ∈ S.μ) (hy : y ∈ S.μ) : x * y ∈ S.μ := by
  rw [mem_μ_iff] at *
  rw [mul_pow, hx, hy, one_mul]

/-- *Elementary facts* of the **Setting** of `q_col_survivors.md`: every element of `μ` is
non-zero. -/
theorem ne_zero_of_mem_μ {x : F} (hx : x ∈ S.μ) : x ≠ 0 := by
  rintro rfl
  rw [mem_μ_iff, zero_pow (by have := S.one_le_r; omega)] at hx
  exact zero_ne_one hx

/-- *Elementary facts* of the **Setting** of `q_col_survivors.md`: `μ` is closed under
inverses. -/
theorem inv_mem_μ {x : F} (hx : x ∈ S.μ) : x⁻¹ ∈ S.μ := by
  rw [mem_μ_iff] at *
  rw [inv_pow, hx, inv_one]

/-- *Elementary facts* of the **Setting** of `q_col_survivors.md`: `μ` is closed under finite
products. -/
theorem prod_mem_μ {ι : Type*} (s : Finset ι) (f : ι → F) (hf : ∀ i ∈ s, f i ∈ S.μ) :
    ∏ i ∈ s, f i ∈ S.μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Setting.one_mem_μ S
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact Setting.mul_mem_μ S (hf a (Finset.mem_insert_self a s))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

/-- **Setting** of `q_col_survivors.md` (reused from `q_col_splitting.md`): `q = p^v ≥ 1`. -/
theorem one_le_q : 1 ≤ S.q := Nat.one_le_pow _ _ S.hp.pos

end Setting

section Colouring

variable (S : ColSetting F) (k : ℕ)

/-- **Setting** of `q_col_survivors.md`: for a colouring `c = (c_1, …, c_d) ∈ μ^d` (`d = 2k+1`),
`c_0 := (c_1 ⋯ c_d)^{−1}`. -/
noncomputable def c0 {S : ColSetting F} {k : ℕ} (c : Fin (2 * k + 1) → S.μ) : F :=
  (∏ i, (c i : F))⁻¹

/-- **Setting** of `q_col_survivors.md`: the colouring extended to the index set
`{0, 1, …, d} = Fin (2 * k + 2)`: index `0` gets `c_0`, index `a = j + 1` gets `c_a = c j`. -/
noncomputable def cExt {S : ColSetting F} {k : ℕ} (c : Fin (2 * k + 1) → S.μ) :
    Fin (2 * k + 2) → F :=
  Fin.cases (c0 c) (fun j => (c j : F))

/-- *Elementary facts* of the **Setting** of `q_col_survivors.md`: `c_0` lies in `μ`. -/
theorem c0_mem {S : ColSetting F} {k : ℕ} (c : Fin (2 * k + 1) → S.μ) : c0 c ∈ S.μ :=
  Setting.inv_mem_μ S (Setting.prod_mem_μ S _ _ fun i _ => (c i).2)

/-- **Setting** of `q_col_survivors.md`: `c_0 c_1 ⋯ c_d = 1`. -/
theorem prod_cExt {S : ColSetting F} {k : ℕ} (c : Fin (2 * k + 1) → S.μ) :
    ∏ a, cExt c a = 1 := by
  rw [Fin.prod_univ_succ]
  simp only [cExt, Fin.cases_zero, Fin.cases_succ, c0]
  exact inv_mul_cancel₀ (Setting.ne_zero_of_mem_μ S (Setting.prod_mem_μ S _ _ fun i _ => (c i).2))

/-- Every `c_a` (`0 ≤ a ≤ d`) lies in `μ` (*Elementary facts* of `q_col_survivors.md`). -/
theorem cExt_mem {S : ColSetting F} {k : ℕ} (c : Fin (2 * k + 1) → S.μ) (a : Fin (2 * k + 2)) :
    cExt c a ∈ S.μ := by
  cases a using Fin.cases with
  | zero => exact c0_mem c
  | succ j => exact (c j).2

/-- **Setting** of `q_col_survivors.md`: the elements `t_a ∈ F[G]` indexed by
`{0, 1, …, d} = Fin (2 * k + 2)`: for `a = j + 1` this is the class of the variable `X j`.
The value at `0` is an unused dummy value `0` (as in the ballot files; `t_0` never occurs). -/
noncomputable def tG : Fin (2 * k + 2) → GA F (2 * k + 1) S.m :=
  Fin.cases 0 (fun j => Ideal.Quotient.mk _ (X j))

/-- **Setting** of `q_col_survivors.md`: the images `t_a ∈ R_c` of the variables, indexed by
`Fin (2 * k + 2)` (for `a = j + 1` the class of `X j`; dummy value `0` at `a = 0`). -/
noncomputable def tR {S : ColSetting F} {k : ℕ} (c : Fin (2 * k + 1) → S.μ) :
    Fin (2 * k + 2) → Rc F S.q (fun j => (c j : F)) :=
  Fin.cases 0 (fun j => Ideal.Quotient.mk _ (X j))

/-- **Setting** of `q_col_survivors.md`: for a matching `J`,
`ψ_J := Π_{a < J(a)} (t_{J(a)} − 1) · Π_{0 < a < J(a)} φ(t_a t_{J(a)}) ∈ F[G]`. -/
noncomputable def psi (J : BallotBound.Matching k) : GA F (2 * k + 1) S.m :=
  (∏ a ∈ Finset.univ.filter (fun a => a < J.1 a), (tG S k (J.1 a) - 1)) *
    ∏ a ∈ Finset.univ.filter (fun a => 0 < a ∧ a < J.1 a), phi S.m (tG S k a * tG S k (J.1 a))

/-- `π_c(t_a) = t_a` (**Setting** of `q_col_survivors.md`: `t_a` denotes the variable and its
images in `F[G]` and `R_c`). -/
theorem piC_tG (c : Fin (2 * k + 1) → S.μ) (a : Fin (2 * k + 2)) :
    S.piC c (tG S k a) = tR c a := by
  cases a using Fin.cases with
  | zero => simp [tG, tR]
  | succ j => simp [tG, tR, ColSetting.piC_mk]

end Colouring

section Rc

variable (S : ColSetting F) {d : ℕ} (c : Fin d → S.μ)

/-- The evaluation `R_c → F`, `t_i ↦ c_i` (well defined since `(c_i − c_i)^q = 0`); it underlies
the *Units* paragraph of the **Proof** of Lemma 6.2 in `q_col_survivors.md`. -/
noncomputable def evalRc : Rc F S.q (fun j => (c j : F)) →ₐ[F] F :=
  Ideal.Quotient.liftₐ _ (MvPolynomial.aeval fun j => (c j : F)) (by
    intro f hf
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hf
    · rintro _ ⟨i, rfl⟩
      simp [zero_pow (Nat.one_le_iff_ne_zero.1 (Setting.one_le_q S))]
    · simp
    · intro x y _ _ hx hy; rw [map_add, hx, hy, add_zero]
    · intro a x _ hx; rw [smul_eq_mul, map_mul, hx, mul_zero])

/-- The evaluation `R_c → F` of the *Units* paragraph of the **Proof** of Lemma 6.2 in
`q_col_survivors.md` sends the class of `f` to `f(c_1, …, c_d)`. -/
@[simp] theorem evalRc_mk (f : MvPolynomial (Fin d) F) :
    evalRc S c (Ideal.Quotient.mk _ f) = MvPolynomial.aeval (fun j => (c j : F)) f := rfl

/-- *Units* paragraph of the **Proof** of Lemma 6.2 in `q_col_survivors.md`: `R_c` is not the
zero ring (it maps onto `F`). -/
instance nontrivial_Rc : Nontrivial (Rc F S.q (fun j => (c j : F))) :=
  (evalRc S c).toRingHom.domain_nontrivial

/-- `R_c` has characteristic `p` (used in the *Frobenius in `R_c`* paragraph of the **Proof** of
Lemma 6.2 in `q_col_survivors.md`). -/
theorem charP_Rc : CharP (Rc F S.q (fun j => (c j : F))) S.p := by
  haveI := S.charP
  haveI : FaithfulSMul F (Rc F S.q (fun j => (c j : F))) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (algebraMap F _).injective
  exact charP_of_injective_algebraMap' F S.p

/-- **Setting** of `q_col_survivors.md`: in `R_c`, `(t_i − c_i)^q = 0` for every `i`. -/
theorem sub_pow_q_eq_zero (i : Fin d) :
    ((Ideal.Quotient.mk _ (X i) : Rc F S.q (fun j => (c j : F))) - algebraMap F _ (c i)) ^ S.q
      = 0 := by
  rw [show algebraMap F (Rc F S.q (fun j => (c j : F))) (c i) = Ideal.Quotient.mk _ (C (c i : F))
    from rfl, ← map_sub, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span ⟨i, rfl⟩

/-- *Frobenius in `R_c`* (**Proof** of Lemma 6.2 in `q_col_survivors.md`): `(x + y)^q = x^q + y^q`
in `R_c`. -/
theorem frobenius_add (x y : Rc F S.q (fun j => (c j : F))) :
    (x + y) ^ S.q = x ^ S.q + y ^ S.q := by
  haveI := charP_Rc S c
  haveI : Fact S.p.Prime := ⟨S.hp⟩
  exact add_pow_char_pow x y S.p S.v

/-- *Frobenius in `R_c`* (**Proof** of Lemma 6.2 in `q_col_survivors.md`): `(x − y)^q = x^q − y^q`
in `R_c`. -/
theorem frobenius_sub (x y : Rc F S.q (fun j => (c j : F))) :
    (x - y) ^ S.q = x ^ S.q - y ^ S.q := by
  haveI := charP_Rc S c
  haveI : Fact S.p.Prime := ⟨S.hp⟩
  exact sub_pow_char_pow _ _ _

/-- *Frobenius in `R_c`* (**Proof** of Lemma 6.2 in `q_col_survivors.md`): `t_i^q = c_i^q` in
`R_c`. -/
theorem frobenius_t (i : Fin d) :
    (Ideal.Quotient.mk _ (X i) : Rc F S.q (fun j => (c j : F))) ^ S.q
      = algebraMap F _ ((c i : F) ^ S.q) := by
  have h := sub_pow_q_eq_zero S c i
  rw [frobenius_sub, sub_eq_zero] at h
  rw [h, map_pow]

/-- Every element of `R_c` is its value under `t ↦ c` plus a nilpotent (*Units* paragraph of the
**Proof** of Lemma 6.2 in `q_col_survivors.md`: `R_c = F[s_1, …, s_d]/(s_i^q)` with `s_i = t_i − c_i`
nilpotent). -/
theorem isNilpotent_sub_evalRc (x : Rc F S.q (fun j => (c j : F))) :
    IsNilpotent (x - algebraMap F _ (evalRc S c x)) := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  induction f using MvPolynomial.induction_on with
  | C a =>
    refine ⟨1, ?_⟩
    rw [pow_one, sub_eq_zero, evalRc_mk, aeval_C]
    rfl
  | add f g hf hg =>
    rw [map_add, map_add, map_add, add_sub_add_comm]
    exact (Commute.all _ _).isNilpotent_add hf hg
  | mul_X f i hf =>
    have hs : IsNilpotent ((Ideal.Quotient.mk _ (X i) : Rc F S.q (fun j => (c j : F))) -
        algebraMap F _ (c i)) := ⟨_, sub_pow_q_eq_zero S c i⟩
    have e : (Ideal.Quotient.mk _ (f * X i) : Rc F S.q (fun j => (c j : F))) -
        algebraMap F _ (evalRc S c (Ideal.Quotient.mk _ (f * X i))) =
        (Ideal.Quotient.mk _ f - algebraMap F _ (evalRc S c (Ideal.Quotient.mk _ f))) *
          Ideal.Quotient.mk _ (X i) +
        algebraMap F _ (evalRc S c (Ideal.Quotient.mk _ f)) *
          (Ideal.Quotient.mk _ (X i) - algebraMap F _ (c i)) := by
      simp only [evalRc_mk, map_mul, aeval_X]
      ring
    rw [e]
    exact (Commute.all _ _).isNilpotent_add ((Commute.all _ _).isNilpotent_mul_right hf)
      ((Commute.all _ _).isNilpotent_mul_left hs)

/-- *Units* (**Proof** of Lemma 6.2 in `q_col_survivors.md`): an element `x` of `R_c` is a unit iff
it is a non-zero constant plus a nilpotent, i.e. iff its value under `t ↦ c` is non-zero. -/
theorem isUnit_iff_evalRc_ne_zero (x : Rc F S.q (fun j => (c j : F))) :
    IsUnit x ↔ evalRc S c x ≠ 0 := by
  constructor
  · intro hx
    exact (hx.map (evalRc S c)).ne_zero
  · intro hx
    have e : x = algebraMap F _ (evalRc S c x) + (x - algebraMap F _ (evalRc S c x)) := by ring
    rw [e]
    exact (isNilpotent_sub_evalRc S c x).isUnit_add_left_of_commute
      ((Ne.isUnit hx).map _) (Commute.all _ _)

/-- *Units* (**Proof** of Lemma 6.2 in `q_col_survivors.md`): `R_c` is a local ring. -/
theorem isLocalRing_Rc : IsLocalRing (Rc F S.q (fun j => (c j : F))) := by
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
  rw [isUnit_iff_evalRc_ne_zero, isUnit_iff_evalRc_ne_zero, map_sub, map_one]
  by_cases h : evalRc S c a = 0
  · right; simp [h]
  · left; exact h

end Rc

end ColSurv

end
