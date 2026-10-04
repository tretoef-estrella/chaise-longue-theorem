module

public import RequestProject.ColSurv.Defs

/-!
# Part C, (C1)–(C3) of `q_even_block_one.md`: the map `θ`

Throughout, `GA F n q = F[X_0, …, X_{n−1}]/(X_i^q − 1)` (`ColSplit.GA`).

* (C1) `EvenOne.iotaGA : GA F n q →ₐ[F] GA F (n+1) q`, `X i ↦ X i.succ`, and
  `EvenOne.theta : GA F (n+1) q →ₗ[F] GA F n q`, «the coefficient of `X 0 ^ 0`». **Implementation
  (as suggested in the file):** `θ (mk p) := mk (θ̃ p)` where `θ̃ = EvenOne.thetaP` is the `F`-linear
  map with `θ̃ (monomial d a) = if q ∣ d 0 then monomial (d ∘ Fin.succ) a else 0`. It is well
  defined because `θ̃ (p·(X 0^q − 1)) = 0` and `θ̃ (p·(X i.succ^q − 1)) = θ̃(p)·(X i^q − 1)`.
* (C2) `EvenOne.theta_iota_mul`, `EvenOne.theta_X0_pow_mul`.
* (C3) `EvenOne.theta_pair`, `EvenOne.theta_pair_X`.
-/

@[expose] public section

open MvPolynomial

namespace EvenOne

open ColSplit ColSurv

variable {F : Type*} [Field F]

/-- **Part C** of `q_even_block_one.md` (technical): the module structure of `GA F n q` over itself
(`Semiring.toModule`), registered with high priority so that instance search finds it at once
(as `Peel.instModuleCSelf` does for `Peel.C`). -/
noncomputable instance (priority := high) instModuleGASelf (n q : ℕ) :
    Module (GA F n q) (GA F n q) := Semiring.toModule

/-! ### The polynomial map `θ̃` -/

/-- **Part C, (C1)** of `q_even_block_one.md` (implementation): for an exponent vector `d` of
`F[X_0, …, X_n]`, the exponent vector `d ∘ Fin.succ` of `F[X_0, …, X_{n−1}]` (the variable `X i`
of the smaller ring is `X i.succ` of the bigger one). -/
noncomputable def tailExp {n : ℕ} (d : Fin (n + 1) →₀ ℕ) : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i => d i.succ

/-- **Part C, (C1)** of `q_even_block_one.md` (implementation): `tailExp d i = d i.succ`. -/
@[simp] theorem tailExp_apply {n : ℕ} (d : Fin (n + 1) →₀ ℕ) (i : Fin n) :
    tailExp d i = d i.succ := by
  simp [tailExp]

/-- **Part C, (C1)** of `q_even_block_one.md` (implementation): `tailExp` is additive. -/
theorem tailExp_add {n : ℕ} (d e : Fin (n + 1) →₀ ℕ) : tailExp (d + e) = tailExp d + tailExp e := by
  ext i; simp

/-- **Part C, (C1)** of `q_even_block_one.md` (implementation): the `F`-linear map
`θ̃ : F[X_0, …, X_n] → F[X_0, …, X_{n−1}]`,
`θ̃ (monomial d a) = if q ∣ d 0 then monomial (d ∘ Fin.succ) a else 0`. -/
noncomputable def thetaP (q n : ℕ) : MvPolynomial (Fin (n + 1)) F →ₗ[F] MvPolynomial (Fin n) F :=
  Finsupp.lsum F fun d => if q ∣ d 0 then (monomial (tailExp d) : F →ₗ[F] _) else 0

/-- **Part C, (C1)** of `q_even_block_one.md` (implementation): the value of `θ̃` on a monomial. -/
theorem thetaP_monomial (q n : ℕ) (d : Fin (n + 1) →₀ ℕ) (a : F) :
    thetaP q n (monomial d a) = if q ∣ d 0 then monomial (tailExp d) a else 0 := by
  unfold thetaP
  erw [Finsupp.lsum_single]
  split_ifs <;> rfl

/-- **Part C, (C1)** of `q_even_block_one.md` (proof): for an exponent vector `e` with `q ∣ e 0`,
`θ̃ (p · monomial e b) = θ̃ (p) · monomial (e ∘ Fin.succ) b`. -/
theorem thetaP_mul_monomial (q n : ℕ) (p : MvPolynomial (Fin (n + 1)) F)
    {e : Fin (n + 1) →₀ ℕ} (he : q ∣ e 0) (b : F) :
    thetaP q n (p * monomial e b) = thetaP q n p * monomial (tailExp e) b := by
  induction p using MvPolynomial.induction_on' with
  | monomial d a =>
    rw [monomial_mul, thetaP_monomial, thetaP_monomial]
    simp only [Finsupp.add_apply, Nat.dvd_add_left he]
    split_ifs
    · rw [monomial_mul, tailExp_add]
    · rw [zero_mul]
  | add p₁ p₂ h₁ h₂ => rw [add_mul, map_add, map_add, h₁, h₂, add_mul]

/-- **Part C, (C2)** of `q_even_block_one.md` (polynomial form):
`θ̃ (p · rename Fin.succ h) = θ̃ (p) · h`. -/
theorem thetaP_mul_rename (q n : ℕ) (p : MvPolynomial (Fin (n + 1)) F)
    (h : MvPolynomial (Fin n) F) :
    thetaP q n (p * rename Fin.succ h) = thetaP q n p * h := by
  induction h using MvPolynomial.induction_on' with
  | monomial e b =>
    rw [rename_monomial, thetaP_mul_monomial q n p ?_ b]
    · have : tailExp (Finsupp.mapDomain Fin.succ e) = e := by
        ext i
        rw [tailExp_apply, Finsupp.mapDomain_apply (Fin.succ_injective _)]
      rw [this]
    · rw [Finsupp.mapDomain_notin_range]
      · exact dvd_zero _
      · rintro ⟨i, hi⟩
        exact Fin.succ_ne_zero i hi
  | add h₁ h₂ e₁ e₂ => rw [map_add, mul_add, map_add, e₁, e₂, mul_add]

/-- **Part C, (C1)** of `q_even_block_one.md` (well defined): `θ̃` sends
`(X_i^q − 1 : i)` into `(X_i^q − 1 : i)`. -/
theorem thetaP_mem_gaIdeal (q n : ℕ) {p : MvPolynomial (Fin (n + 1)) F}
    (hp : p ∈ gaIdeal F (n + 1) q) : thetaP q n p ∈ gaIdeal F n q := by
  obtain ⟨c, rfl⟩ := (Ideal.mem_span_range_iff_exists_fun).1 hp
  rw [map_sum]
  refine Ideal.sum_mem _ fun i _ => ?_
  induction i using Fin.cases with
  | zero =>
    have hX : (X 0 : MvPolynomial (Fin (n + 1)) F) ^ q = monomial (Finsupp.single 0 q) 1 :=
      X_pow_eq_monomial
    rw [mul_sub, mul_one, map_sub, hX, thetaP_mul_monomial q n _ (by simp)]
    have : tailExp (Finsupp.single (0 : Fin (n + 1)) q) = 0 := by
      ext i; simp
    rw [this, ← C_apply, C_1, mul_one, sub_self]
    exact Ideal.zero_mem _
  | succ j =>
    have hr : (X j.succ ^ q - 1 : MvPolynomial (Fin (n + 1)) F) =
        rename Fin.succ (X j ^ q - 1) := by simp
    rw [hr, thetaP_mul_rename]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)

/-! ### `ι` and `θ` on the group algebras -/

/-- **Part C, (C1)** of `q_even_block_one.md` (proof): `rename Fin.succ` sends
`(X_i^q − 1)` into `(X_i^q − 1)`. -/
theorem gaIdeal_le_comap_rename (q n : ℕ) :
    gaIdeal F n q ≤
      (gaIdeal F (n + 1) q).comap (rename Fin.succ : MvPolynomial (Fin n) F →ₐ[F] _) := by
  rw [gaIdeal, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  simp only [SetLike.mem_coe, Ideal.mem_comap, map_sub, map_pow, rename_X, map_one]
  exact Ideal.subset_span ⟨i.succ, rfl⟩

/-- **Part C, (C1)** of `q_even_block_one.md`: the `F`-algebra map
`ι : GA F n q → GA F (n+1) q` induced by `X i ↦ X i.succ`. -/
noncomputable def iotaGA (q n : ℕ) : GA F n q →ₐ[F] GA F (n + 1) q :=
  Ideal.Quotient.liftₐ (gaIdeal F n q)
    ((Ideal.Quotient.mkₐ F (gaIdeal F (n + 1) q)).comp (rename Fin.succ)) (by
      intro a ha
      simp only [AlgHom.coe_comp, Function.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
        Ideal.Quotient.eq_zero_iff_mem]
      exact gaIdeal_le_comap_rename q n ha)

/-- **Part C, (C1)** of `q_even_block_one.md`: `ι (mk p) = mk (rename Fin.succ p)`. -/
theorem iotaGA_mk (q n : ℕ) (p : MvPolynomial (Fin n) F) :
    iotaGA q n (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ (rename Fin.succ p) := rfl

/-- **Part C, (C1)** of `q_even_block_one.md`: `ι (X i) = X i.succ`. -/
@[simp] theorem iotaGA_X (q n : ℕ) (i : Fin n) :
    iotaGA (F := F) q n (Ideal.Quotient.mk _ (X i)) = Ideal.Quotient.mk _ (X i.succ) := by
  rw [iotaGA_mk, rename_X]

/-- **Part C, (C1)** of `q_even_block_one.md`: the `F`-linear map
`θ : GA F (n+1) q → GA F n q`, `θ (mk p) = mk (θ̃ p)` — «the coefficient of `X 0 ^ 0`». -/
noncomputable def theta (q n : ℕ) : GA F (n + 1) q →ₗ[F] GA F n q where
  toFun := Quotient.lift (fun p => Ideal.Quotient.mk (gaIdeal F n q) (thetaP q n p)) (by
    intro a b hab
    change Ideal.Quotient.mk _ _ = Ideal.Quotient.mk _ _
    rw [Ideal.Quotient.eq, ← map_sub]
    exact thetaP_mem_gaIdeal q n ((Submodule.quotientRel_def _).1 hab))
  map_add' := by
    intro x y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [← map_add]
    change Ideal.Quotient.mk _ (thetaP q n (a + b)) =
      Ideal.Quotient.mk _ (thetaP q n a) + Ideal.Quotient.mk _ (thetaP q n b)
    rw [map_add, map_add]
  map_smul' := by
    intro r x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    have e : r • Ideal.Quotient.mk (gaIdeal F (n + 1) q) a = Ideal.Quotient.mk _ (r • a) :=
      (map_smul (Ideal.Quotient.mkₐ F (gaIdeal F (n + 1) q)) r a).symm
    rw [e]
    change Ideal.Quotient.mk _ (thetaP q n (r • a)) = r • Ideal.Quotient.mk _ (thetaP q n a)
    rw [map_smul]
    exact map_smul (Ideal.Quotient.mkₐ F (gaIdeal F n q)) r _

/-- **Part C, (C1)** of `q_even_block_one.md`: `θ (mk p) = mk (θ̃ p)`. -/
theorem theta_mk (q n : ℕ) (p : MvPolynomial (Fin (n + 1)) F) :
    theta q n (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ (thetaP q n p) := rfl

/-! ### (C2) -/

/-- **Part C, (C2)** of `q_even_block_one.md`: `θ (ι h · f) = h · θ f` for all `h`, `f`
(`θ` is `GA F n q`-linear through `ι`). -/
theorem theta_iota_mul (q n : ℕ) (h : GA F n q) (f : GA F (n + 1) q) :
    theta q n (iotaGA q n h * f) = h * theta q n f := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective h
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective f
  rw [iotaGA_mk, ← map_mul, theta_mk, theta_mk, mul_comm, thetaP_mul_rename, map_mul, mul_comm]

/-- **Part C, (C2)** of `q_even_block_one.md`: `θ (f · ι h) = θ f · h` (the same, with the factors
in the other order). -/
theorem theta_mul_iota (q n : ℕ) (f : GA F (n + 1) q) (h : GA F n q) :
    theta q n (f * iotaGA q n h) = theta q n f * h := by
  rw [mul_comm, theta_iota_mul, mul_comm]

/-- **Part C, (C2)** of `q_even_block_one.md`: for `u < q`,
`θ (X 0^u · ι h) = if u = 0 then h else 0`. -/
theorem theta_X0_pow_mul (q n : ℕ) {u : ℕ} (hu : u < q) (h : GA F n q) :
    theta q n ((Ideal.Quotient.mk _ (X 0)) ^ u * iotaGA q n h) = if u = 0 then h else 0 := by
  rw [theta_mul_iota, ← map_pow, theta_mk, X_pow_eq_monomial, thetaP_monomial]
  by_cases h0 : u = 0
  · subst h0
    have : tailExp (Finsupp.single (0 : Fin (n + 1)) 0) = 0 := by ext i; simp
    rw [Finsupp.single_eq_same, if_pos (dvd_zero q), this, ← C_apply, C_1, map_one, one_mul,
      if_pos rfl]
  · have hnd : ¬ q ∣ (Finsupp.single (0 : Fin (n + 1)) u) 0 := by
      rw [Finsupp.single_eq_same]
      exact fun hd => h0 (Nat.eq_zero_of_dvd_of_lt hd hu)
    rw [if_neg hnd, if_neg h0, map_zero, zero_mul]

/-! ### (C3) -/

/-- **Part C, (C3)** of `q_even_block_one.md` (general form): for `q ≥ 1` and all
`x, h ∈ GA F n q`, `θ ((ι x − 1) · phi q (X 0 · ι x) · ι h) = (x − 1) · h` (the coefficient of
`X 0^0` in `phi q (X 0 · ι x) = Σ_{u<q} X 0^u ι(x)^u` is `1`). **More general than the file:** any
`x` in place of `X b`, and no hypothesis on `q` or on the characteristic beyond `q ≥ 1`. -/
theorem theta_pair (q n : ℕ) (hq : 1 ≤ q) (x h : GA F n q) :
    theta q n ((iotaGA q n x - 1) * phi q (Ideal.Quotient.mk _ (X 0) * iotaGA q n x) *
      iotaGA q n h) = (x - 1) * h := by
  have e : (iotaGA q n x - 1) * phi q (Ideal.Quotient.mk _ (X 0) * iotaGA q n x) * iotaGA q n h =
      ∑ u ∈ Finset.range q, (Ideal.Quotient.mk (gaIdeal F (n + 1) q) (X 0)) ^ u *
        iotaGA q n ((x - 1) * x ^ u * h) := by
    rw [phi, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [map_mul, map_mul, map_pow, map_sub, map_one, mul_pow]
    ring
  rw [e, map_sum,
    Finset.sum_congr rfl fun u hu => theta_X0_pow_mul q n (Finset.mem_range.1 hu) _,
    Finset.sum_ite_eq' (Finset.range q) 0, if_pos (Finset.mem_range.2 hq), pow_zero, mul_one]

/-- **Part C, (C3)** of `q_even_block_one.md`: for `q ≥ 1` (in particular `q = 2^v`, `v ≥ 1`, in
characteristic `2`) and `b : Fin n`,
`θ ((ι (X b) − 1) · phi q (X 0 · ι (X b)) · ι h) = (X b − 1) · h`. (The characteristic is not
needed.) -/
theorem theta_pair_X (q n : ℕ) (hq : 1 ≤ q) (b : Fin n) (h : GA F n q) :
    theta q n ((iotaGA q n (Ideal.Quotient.mk _ (X b)) - 1) *
      phi q (Ideal.Quotient.mk _ (X 0) * iotaGA q n (Ideal.Quotient.mk _ (X b))) *
        iotaGA q n h) = (Ideal.Quotient.mk _ (X b) - 1) * h :=
  theta_pair q n hq _ h

end EvenOne

end
