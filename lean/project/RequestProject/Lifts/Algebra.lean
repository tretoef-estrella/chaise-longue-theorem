module

public import RequestProject.Lifts.Options

/-!
# The algebraic part of the proof of `q_P3_lifts.md`

We work with `m = n + 1`, so that `C_{m−1} = C_n`, and with the identification
`φ : C_m ≅ C_{m−1}[y_1]/(y_1^{q−1})` of `q_peeling_lemma.md` (`Peel.peelEquiv`).  Under `φ`, `y_1`
is the root and `y_{i+1}` is the variable `y_i` of `C_{m−1}` (encoded `X (i-1)`); in particular
the ring map `Peel.incl : C_{m−1} → C_m` (`y_i ↦ y_{i+1}`) becomes the inclusion of constants.

Contents:
* the reduction of **Step 1** of the Proof: if `f ∈ V` has `deg_{y_1} f ≤ d` then its coefficient
  of `y_1^d` lies in `W_d(V)`, computed on any polynomial representative of `φ(f)` of degree `≤ d`
  (`coeff_mem_W`), and the monotonicity `W_d ⊆ W_{d'}` for `d ≤ d' ≤ q − 2` (`W_mono_le`);
* the coefficient computations of the cases: the `y_1`-expansion of `Π_{c ∈ B}(y_c − y_1)` used
  with part (iii) of `q_P3_identities.md` in cases (α) and (β) (`coeff_C_mul_prod`), and the
  `y_1`-expansion of `D(y_1, y_b)` (part (i) of `q_P3_identities.md`) used in case (γ)
  (`phi_D`, `coeff_dpoly`).
-/

@[expose] public section

open Polynomial

namespace Lifts

open Peel hiding C
open Tight ChainLemma

set_option synthInstance.maxHeartbeats 200000

variable {F : Type*} [Field F] {q n : ℕ}

/-- The identification `C_m = C_{m−1}[y_1]/(y_1^{q−1})` of `q_peeling_lemma.md` (used throughout
Step 1 of the Proof in `q_P3_lifts.md`) sends `y_1` to `y_1`. -/
theorem phi_y0 : peelEquiv' F q n (y F q 0) = AdjoinRoot.root _ := by
  simp [peelEquiv', peelFwd, y]

/-- The identification of `q_peeling_lemma.md` (Step 1 of the Proof in `q_P3_lifts.md`) is the
identity on `C_{m−1}` (the variables `y_2, …, y_m`): `φ(incl g) = g`. -/
theorem phi_incl (g : Peel.C F q n) : peelEquiv' F q n (incl F q n g) = AdjoinRoot.of _ g := by
  have : incl F q n g = (peelEquiv' F q n).symm (AdjoinRoot.of _ g) := by
    show _ = peelBwd F q n (AdjoinRoot.of _ g)
    simp [peelBwd]
  rw [this, AlgEquiv.apply_symm_apply]

/-- The variable `y_i` of `C_{m−1}` is the variable `y_{i+1}` of `C_m` (the convention "the ring
`C_{m−1}` has the variables `y_2, …, y_m`" of `q_P3_lifts.md`). -/
theorem incl_y (i : Fin n) : incl F q n (y F q i) = y F q i.succ := by
  simp [incl, y]

/-- **Step 1** of the Proof in `q_P3_lifts.md`: if `f ∈ V` and `φ(f)` is represented by a
polynomial `P ∈ C_{m−1}[y_1]` whose coefficients vanish above `d ≤ q − 2` (so
`deg_{y_1} f ≤ d`), then the coefficient `[y_1^d] f = P_d` lies in `W_d(V)`. -/
theorem coeff_mem_W (hq : 2 ≤ q) (V : Ideal (Peel.C F q (n + 1))) {f : Peel.C F q (n + 1)} (hf : f ∈ V)
    (P : (Peel.C F q n)[X]) (hP : peelEquiv' F q n f = AdjoinRoot.mk _ P) {d : ℕ} (hd : d ≤ q - 2)
    (hdeg : ∀ k, d < k → P.coeff k = 0) :
    P.coeff d ∈ W (m := n + 1) (by omega) V d := by
  haveI := nontrivial_C (F := F) (q := q) (m := n) hq
  have hPdeg : P.degree < (X ^ (q - 1) : (Peel.C F q n)[X]).degree := by
    rw [degree_X_pow]
    refine lt_of_le_of_lt (degree_le_iff_coeff_zero P d |>.2 (fun k hk => hdeg k
      (by exact_mod_cast hk))) ?_
    exact_mod_cast (show d < q - 1 by omega)
  have hexp : expand (m := n + 1) (by omega) f = P := by
    rw [expand_apply]
    show AdjoinRoot.modByMonicHom (monic_X_pow_q q (Peel.C F q n)) (peelEquiv' F q n f) = P
    rw [hP, AdjoinRoot.modByMonicHom_mk, (modByMonic_eq_self_iff (monic_X_pow_q q _)).2 hPdeg]
  refine (mem_W _ V d _).2 ⟨f, (mem_Vle _ V d f).2 ⟨hf, fun k hk => ?_⟩, ?_⟩
  · rw [hexp]; exact hdeg k hk
  · rw [coeffY1_apply, hexp]

/-- **Step 1** of the Proof in `q_P3_lifts.md` ("since `W_j(V_Λ) ⊆ W_{j+1}(V_Λ)`"): iterating
part (ii) of `q_peeling_lemma.md`, `W_d(V) ⊆ W_{d'}(V)` for `d ≤ d' ≤ q − 2`. -/
theorem W_mono_le (hq : 3 ≤ q) {m : ℕ} (hm : 1 ≤ m) (V : Ideal (Peel.C F q m)) {d d' : ℕ}
    (hdd' : d ≤ d') (hd' : d' ≤ q - 2) : W hm V d ≤ W hm V d' := by
  induction d', hdd' using Nat.le_induction with
  | base => exact le_rfl
  | succ k hk ih => exact (ih (by omega)).trans (W_mono hq hm V k (by omega))

/-- Step 1 of the Proof in `q_P3_lifts.md` ("`±G ∈ W_{q−1−Φ}(V_Λ)`, and `W_j` is a subspace"):
if `(−1)^k g ∈ W` then `g ∈ W`. -/
theorem mem_of_neg_one_pow_mul_mem {m : ℕ} {W' : Submodule F (Peel.C F q m)} (k : ℕ) {g : Peel.C F q m}
    (hg : (-1) ^ k * g ∈ W') : g ∈ W' := by
  rcases neg_one_pow_eq_or (Peel.C F q m) k with h | h
  · rwa [h, one_mul] at hg
  · rw [h, neg_one_mul] at hg; simpa using W'.neg_mem hg

/-- Cases (α) and (β) of the Proof in `q_P3_lifts.md` (the `y_1`-expansion behind part (iii) of
`q_P3_identities.md`): in `R[y_1]`, `a · Π_{c ∈ B} (x_c − y_1)` has no coefficient above
`y_1^{|B|}` and its coefficient of `y_1^{|B|}` is `(−1)^{|B|} a`. -/
theorem coeff_C_mul_prod {ι R : Type*} [CommRing R] [Nontrivial R] (B : Finset ι) (x : ι → R) (a : R) :
    (∀ k, B.card < k → (C a * ∏ c ∈ B, (C (x c) - X)).coeff k = 0) ∧
      (C a * ∏ c ∈ B, (C (x c) - X)).coeff B.card = (-1) ^ B.card * a := by
  have e : ∏ c ∈ B, (C (x c) - X) = C ((-1) ^ B.card) * ∏ c ∈ B, (X - C (x c)) := by
    rw [← Finset.prod_const, map_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun c _ => ?_)
    simp
  have hmon : (∏ c ∈ B, (X - C (x c))).Monic := monic_prod_of_monic _ _ (fun c _ => monic_X_sub_C _)
  have hdeg : (∏ c ∈ B, (X - C (x c))).natDegree = B.card := by
    rw [natDegree_prod_of_monic _ _ (fun c _ => monic_X_sub_C _)]; simp [natDegree_X]
  rw [e, ← mul_assoc, ← C_mul]
  refine ⟨fun k hk => ?_, ?_⟩
  · rw [coeff_C_mul, coeff_eq_zero_of_natDegree_lt (by omega), mul_zero]
  · rw [coeff_C_mul, ← hdeg, hmon.coeff_natDegree, mul_one, mul_comm]

/-- Case (γ) of the Proof in `q_P3_lifts.md`: the polynomial
`Σ_{i=0}^{q−2} (−1)^i x^{q−2−i} y_1^i ∈ R[y_1]`, i.e. `D(y_1, y_b)` expanded in `y_1` with
`x = y_b`. -/
noncomputable def dpoly {R : Type*} [CommRing R] (q : ℕ) (x : R) : R[X] :=
  ∑ i ∈ Finset.range (q - 1), C ((-1) ^ i * x ^ (q - 2 - i)) * X ^ i

/-- Case (γ) of the Proof in `q_P3_lifts.md` (part (i) of `q_P3_identities.md`, up to the sign
convention): the coefficient of `y_1^k` in `D(y_1, y_b)` is `(−1)^k y_b^{q−2−k}` for `k ≤ q − 2`,
and `0` for `k > q − 2`. -/
theorem coeff_dpoly {R : Type*} [CommRing R] (x : R) (k : ℕ) :
    (dpoly q x).coeff k = if k < q - 1 then (-1) ^ k * x ^ (q - 2 - k) else 0 := by
  simp only [dpoly, finset_sum_coeff, coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  simp [Finset.mem_range]

/-- Case (γ) of the Proof in `q_P3_lifts.md`: under the identification of `q_peeling_lemma.md`,
`D(y_1, y_{b+1}) ∈ C_m` becomes the polynomial `Σ_i (−1)^i y_b^{q−2−i} y_1^i` (with `y_b` the
variable of `C_{m−1}`). -/
theorem phi_D (b : Fin n) :
    peelEquiv' F q n (D F q 0 b.succ) = AdjoinRoot.mk _ (dpoly q (y F q b)) := by
  have hb : y F q b.succ = incl F q n (y F q b) := (incl_y b).symm
  simp only [D, dpoly, map_sum, map_mul, map_pow, map_neg, map_one, hb, phi_incl, phi_y0,
    AdjoinRoot.mk_C, AdjoinRoot.mk_X]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

end Lifts

end
