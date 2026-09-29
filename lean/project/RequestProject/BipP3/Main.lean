module

public import RequestProject.BipP3.Patterns

/-!
# Proposition 7.5 of `q_bip_P3.md`: every tight pattern of a layer lies in the right slice

For a down-set `Λ` of `BPar_q(α, β)` and every `i ∈ {0, …, q − 1}`:
`V_{Λ_i} ⊆ W_{q−1−i}(V_Λ)`.

The file follows the **Proof** of `q_bip_P3.md`: the identification
`R_{α,β} = R_{α−1,β}[w]/(w^q)` and the reduction of Step 1 are in
`RequestProject/BipP3/Algebra.lean`, the tight patterns of the cases (α), (β), (γ) in
`RequestProject/BipP3/Patterns.lean`; here the coefficient computations of the cases are carried
out and everything is assembled.  (The file `RequestProject/Lifts/Main.lean`, the one-partition
version, is the model.)
-/

@[expose] public section

open Polynomial

namespace BipP3

open Bip ChainLemma Tight

set_option synthInstance.maxHeartbeats 200000

variable {F : Type*} [Field F] {q : ℕ}

/-- **Step 1** of the Proof of Proposition 7.5 in `q_bip_P3.md` ("since
`W_j(V_Λ) ⊆ W_{j+1}(V_Λ)`"): iterating Lemma 7.1 (ii) of `q_bip_setting.md`,
`W_d(V) ⊆ W_{d'}(V)` for `d ≤ d' ≤ q − 1`. -/
theorem Wslice_mono_le (hq : 3 ≤ q) {α β : ℕ} (hα : 1 ≤ α) (V : Ideal (R F q α β)) {d d' : ℕ}
    (hdd' : d ≤ d') (hd' : d' ≤ q - 1) : Wslice F q hα V d ≤ Wslice F q hα V d' := by
  induction d', hdd' using Nat.le_induction with
  | base => exact le_rfl
  | succ k hk ih => exact (ih (by omega)).trans (Wslice_mono (F := F) hq hα V k (by omega))

/-- **Cases (α) and (β)** of the Proof of Proposition 7.5 in `q_bip_P3.md`: let
`λ = (λ_+, μ_−) ∈ Λ`, where `λ_+` has the columns of `μ_+` except that column `c* ≥ 1` is one
longer, and let `G` be the product of a tight pattern of `μ` on `([α − 1], [β])`.  If the height
`(μ_+)'_{c*} = |S|` (`S = B^+_{c*}`) is at most `q − 1`, then `G ∈ W_{|S|}(V_Λ)`: the pattern with
the index `1` put into `S` has product `f = Π_{s ∈ S} (x_s − w) · G ∈ V_Λ`, with `deg_w f = |S|`
and `[w^{|S|}] f = (−1)^{|S|} G` (part (iii) of `q_P3_identities.md`). -/
theorem mem_Wslice_of_insert (hq : 1 ≤ q) {α β : ℕ} (hα : 1 ≤ α)
    {Λ : Set (Partition × Partition)} {μ : Partition × Partition} {lam1 : Partition}
    (hlam : (lam1, μ.2) ∈ Λ) (T : BTightPattern μ (α - 1) β) {cs : ℕ} (hcs : 1 ≤ cs)
    (hcol : ∀ c, 1 ≤ c → colLen lam1 c = colLen μ.1 c + if c = cs then 1 else 0)
    (hd : colLen μ.1 cs ≤ q - 1) :
    T.prod F q ∈ Wslice F q hα (VLamB F q α β Λ) (colLen μ.1 cs) := by
  haveI := Tight.nontrivial_C (F := F) (q := q + 1) (m := α + β - 1) (by omega)
  obtain ⟨T', hT'⟩ := exists_pattern_insert (F := F) (q := q) hα T hcs hcol
  have hf : T'.prod F q ∈ VLamB F q α β Λ := Ideal.subset_span ⟨_, hlam, T', rfl⟩
  set B := cleanX T cs with hBdef
  have hcard : B.card = colLen μ.1 cs := card_cleanX T hcs
  set Pol : (Peel.C F (q + 1) (α + β - 1))[X] :=
    Polynomial.C (constR α β hα (T.prod F q)) *
      ∏ s ∈ B, (Polynomial.C (constR α β hα (x F q s)) - X) with hPol
  have hphi : peelR α β hα (T'.prod F q) = AdjoinRoot.mk _ Pol := by
    have hs : ∀ s : Fin (α - 1), x F q (sh s) = liftR (F := F) (q := q) α β hα (x F q s) :=
      fun s => (liftR_x hα s).symm
    rw [hT', map_mul, map_prod, peelR_liftR, hPol, map_mul, map_prod, mul_comm]
    simp only [map_sub, hs, peelR_liftR, peelR_x0, AdjoinRoot.mk_C, AdjoinRoot.mk_X]
  obtain ⟨h1, h2⟩ := Lifts.coeff_C_mul_prod B (fun s => constR α β hα (x F q s))
    (constR α β hα (T.prod F q))
  have hmem := mem_Wslice_of_coeff hq hα _ hf Pol hphi (d := B.card) (by omega) h1
    ((-1) ^ B.card * T.prod F q) (by rw [h2]; simp)
  rw [hcard] at hmem
  exact Lifts.mem_of_neg_one_pow_mul_mem _ hmem

/-- Case (γ) of the Proof of Proposition 7.5 in `q_bip_P3.md` (the binomial theorem): in `A[w]`,
the coefficient of `w^k` in `(w − a)^{q−1}` is `C(q−1, k) (−a)^{q−1−k}` (so
`[w^{q−1−t}] (w − a)^{q−1} = C(q−1, t) (−1)^t a^t`). -/
lemma coeff_X_sub_C_pow' {A : Type*} [CommRing A] (a : A) (n k : ℕ) :
    ((X - Polynomial.C a) ^ n).coeff k = (-a) ^ (n - k) * (n.choose k : A) := by
  rw [sub_eq_add_neg, ← Polynomial.C_neg, coeff_X_add_C_pow]

/-- **Case (γ)** of the Proof of Proposition 7.5 in `q_bip_P3.md`: let `λ = (μ_+, λ_−) ∈ Λ`, where
`λ_−` has the columns of `μ_−` except that column `c_0 ≥ 1` is one shorter, of height
`r = (μ_−)'_{c_0}` with `1 ≤ r ≤ q`, and let `G = Δ(z_S) · G'` be the product of a tight pattern
of `μ` on `([α − 1], [β])` (`S = B^−_{c_0}`).  If `C(q−1, q−r) = C(q−1, r−1) ≠ 0` in `F`, then
`G ∈ W_{q−r}(V_Λ)`: the element `f := Σ_{b ∈ S} ε_b Δ(z_{S∖{b}}) (w − z_b)^{q−1} G' ∈ V_Λ` has,
by the binomial theorem and part (ii) of `q_P3_identities.md`,
`[w^{q−1−t}] f = C(q−1, t)(−1)^t (Σ_b ε_b Δ(z_{S∖{b}}) z_b^t) G'`, which is `0` for `t ≤ r − 2`
and `C(q−1, r−1)(−1)^{r−1} G` for `t = r − 1`. -/
theorem mem_Wslice_of_pair (hq : 1 ≤ q) {α β : ℕ} (hα : 1 ≤ α)
    {Λ : Set (Partition × Partition)} {μ : Partition × Partition} {lam2 : Partition}
    (hlam : (μ.1, lam2) ∈ Λ) (T : BTightPattern μ (α - 1) β) {c0 : ℕ} (hc0 : 1 ≤ c0)
    (hcol : ∀ c, 1 ≤ c → colLen lam2 c + (if c = c0 then 1 else 0) = colLen μ.2 c)
    (hr : 1 ≤ colLen μ.2 c0) (hrq : colLen μ.2 c0 ≤ q)
    (hbin : (((q - 1).choose (q - colLen μ.2 c0) : ℕ) : F) ≠ 0) :
    T.prod F q ∈ Wslice F q hα (VLamB F q α β Λ) (q - colLen μ.2 c0) := by
  classical
  set S := cleanZ T c0 with hSdef
  have hcard : S.card = colLen μ.2 c0 := card_cleanZ T hc0
  set N := lam2.row 1 + μ.1.row 1 + μ.2.row 1 + c0 with hNdef
  set G' : R F q (α - 1) β := (∏ p ∈ T.pairs, (x F q p.1 - z F q p.2) ^ (q - 1)) *
    (∏ c ∈ Finset.Icc 1 N, vand (x F q) (cleanX T c)) *
    ∏ c ∈ (Finset.Icc 1 N).erase c0, vand (z F q) (cleanZ T c) with hG'
  have hG : T.prod F q = vand (z F q) S * G' := by
    rw [prod_clean T (N := N) (by omega) (by omega),
      ← Finset.mul_prod_erase _ (fun c => vand (z F q (α := α - 1)) (cleanZ T c))
        (Finset.mem_Icc.2 ⟨hc0, (by omega : c0 ≤ N)⟩), hG']
    ring
  have hex : ∀ b ∈ S, ∃ T' : BTightPattern (μ.1, lam2) α β,
      T'.prod F q = (x F q ⟨0, hα⟩ - z F q b) ^ (q - 1) *
        liftR α β hα (vand (z F q) (S.erase b) * G') :=
    fun b hb => exists_pattern_pair (F := F) (q := q) hα T hc0 hcol (N := N) (by omega)
      (by omega) (by omega) (by omega) hb
  choose Tb hTb using hex
  clear_value G' N S
  set eps : Fin β → R F q (α - 1) β :=
    fun b => (-1) ^ (S.card + ((S.filter (· < b)).card + 1)) with heps
  set f : R F q α β :=
    ∑ b ∈ S.attach, liftR α β hα (eps b.1) * (Tb b.1 b.2).prod F q with hfdef
  have hf : f ∈ VLamB F q α β Λ :=
    Ideal.sum_mem _ (fun b _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨_, hlam, _, rfl⟩))
  set Pol0 : (R F q (α - 1) β)[X] :=
    ∑ b ∈ S.attach, Polynomial.C (eps b.1 * vand (z F q) (S.erase b.1) * G') *
      (X - Polynomial.C (z F q b.1)) ^ (q - 1) with hPol0
  have hphi : peelR α β hα f = AdjoinRoot.mk _ (Pol0.map (constR α β hα)) := by
    have hz : ∀ b : Fin β, z F q b = liftR (F := F) (q := q) α β hα (z F q b) :=
      fun b => (liftR_z hα b).symm
    rw [hfdef, hPol0, map_sum, Polynomial.map_sum, map_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [hTb, hz b]
    simp only [map_mul, map_pow, map_sub, peelR_liftR, peelR_x0, Polynomial.map_mul,
      Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_C, Polynomial.map_X,
      AdjoinRoot.mk_C, AdjoinRoot.mk_X]
    ring
  have hcoeff : ∀ k, Pol0.coeff k = ((q - 1).choose k : R F q (α - 1) β) *
      (-1) ^ (q - 1 - k) * G' *
        ∑ b ∈ S, eps b * vand (z F q) (S.erase b) * z F q b ^ (q - 1 - k) := by
    intro k
    rw [hPol0, finset_sum_coeff]
    simp only [coeff_C_mul, coeff_X_sub_C_pow']
    rw [Finset.sum_attach S (fun b => eps b * vand (z F q) (S.erase b) * G' *
      ((-z F q b) ^ (q - 1 - k) * ((q - 1).choose k : R F q (α - 1) β))), Finset.mul_sum]
    exact Finset.sum_congr rfl (fun b _ => by rw [neg_pow]; ring)
  have hvan : ∀ k, q - colLen μ.2 c0 < k → (Pol0.map (constR α β hα)).coeff k = 0 := by
    intro k hk
    rw [Polynomial.coeff_map, hcoeff k]
    by_cases hkq : k ≤ q - 1
    · have := sum_eps_vand (z F q (α := α - 1)) S (q - 1 - k) (by omega)
      rw [if_neg (by omega), zero_mul] at this
      simp only [heps] at this ⊢
      rw [this, mul_zero, map_zero]
    · rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
  have htop := sum_eps_vand (z F q (α := α - 1)) S (S.card - 1) (by omega)
  rw [if_pos rfl, one_mul] at htop
  set κ : F := (((q - 1).choose (q - colLen μ.2 c0) : ℕ) : F) with hκ
  have hmem := mem_Wslice_of_coeff hq hα _ hf _ hphi (d := q - colLen μ.2 c0) (by omega) hvan
    (κ • ((-1) ^ (S.card - 1) * T.prod F q)) (by
      rw [Polynomial.coeff_map, hcoeff, show q - 1 - (q - colLen μ.2 c0) = S.card - 1 by omega]
      simp only [heps] at htop ⊢
      rw [htop, hκ, Nat.cast_smul_eq_nsmul, nsmul_eq_mul, hG]
      congr 1
      ring)
  have h2 := Submodule.smul_mem _ κ⁻¹ hmem
  rw [inv_smul_smul₀ hbin] at h2
  exact Lifts.mem_of_neg_one_pow_mul_mem _ h2

/-- **Step 1** of the Proof of Proposition 7.5 in `q_bip_P3.md`: for `μ ∈ Λ_i` and every tight
pattern of `μ` on `([α − 1], [β])` with product `G`, we have `G ∈ W_{q−1−i}(V_Λ)`.  With
`Φ = F_Λ(μ) ≥ i + 1`, one shows (∗) `G ∈ W_{q−Φ}(V_Λ)` in each of the three cases of Lemma 7.3 (v):
(α) and (β) by `mem_Wslice_of_insert`, (γ) by `mem_Wslice_of_pair`; and concludes by
`W_j(V_Λ) ⊆ W_{j+1}(V_Λ)` (Lemma 7.1 (ii)) since `q − Φ ≤ q − 1 − i`. -/
theorem prod_mem_Wslice (hq : 3 ≤ q)
    (hbin : ∀ t, t ≤ q - 1 → (((q - 1).choose t : ℕ) : F) ≠ 0) {α β : ℕ} (hα : 1 ≤ α)
    {Λ : Set (Partition × Partition)} (hΛ : IsDownSetB q α β Λ) {i : ℕ} (hi : i ≤ q - 1)
    {μ : Partition × Partition} (hμ : μ ∈ BPar q (α - 1) β) (hiΦ : i < FLamB q Λ μ)
    (T : BTightPattern μ (α - 1) β) :
    T.prod F q ∈ Wslice F q hα (VLamB F q α β Λ) (q - 1 - i) := by
  have hΦq := FLamB_le q Λ μ
  rcases lemma73_v hq hα hμ hΛ (by omega) with ⟨hA, -, -⟩ | ⟨-, hB, -⟩ | ⟨-, -, hC⟩
  · -- case (α)
    obtain ⟨h1, hj, hjl, heq, hmem, hfirst⟩ := hA
    set j0 := q + 1 - FLamB q Λ μ with hj0
    have hcs := Lifts.colLen_row_succ μ.1 hj hjl (fun h2 => hfirst.resolve_left (by omega))
    rw [← heq] at hmem
    have h := mem_Wslice_of_insert (F := F) (q := q) (by omega) hα hmem T (cs := μ.1.row j0 + 1)
      (by omega) (fun c _ => Lifts.colLen_addE μ.1 hj hjl c) (by omega)
    rw [hcs] at h
    exact Wslice_mono_le hq hα _ (by omega) (by omega) h
  · -- case (β)
    obtain ⟨h1, h2, h3, h4, heq, hmem⟩ := hB
    rw [← heq] at hmem
    have h := mem_Wslice_of_insert (F := F) (q := q) (by omega) hα hmem T (cs := 1) le_rfl
      (fun c hc => Lifts.colLen_addOne μ.1 hc) (by rw [Lifts.colLen_one]; omega)
    rw [Lifts.colLen_one] at h
    exact Wslice_mono_le hq hα _ (by omega) (by omega) h
  · -- case (γ)
    obtain ⟨h1, h2, heq, hmem, hlast⟩ := hC
    rw [← heq] at hmem
    have hr := Lifts.colLen_row μ.2 h1 h2 (fun h => hlast.resolve_left (by omega))
    have h := mem_Wslice_of_pair (F := F) (q := q) (by omega) hα hmem T
      (c0 := μ.2.row (FLamB q Λ μ)) (μ.2.row_pos _ h1 h2)
      (fun c hc => Lifts.colLen_subE μ.2 h1 h2 hc) (by omega) (by omega)
      (hbin _ (by omega))
    rw [hr] at h
    exact Wslice_mono_le hq hα _ (by omega) (by omega) h

/-- **Proposition 7.5** of `q_bip_P3.md`.  Let `F` be a field, `q ≥ 3` odd, such that the binomial
coefficients `C(q−1, t)`, `0 ≤ t ≤ q − 1`, are non-zero in `F`; let `α ≥ 1`, `β ≥ 0`, and let `Λ`
be a down-set of `BPar_q(α, β)` (`IsDownSetB q α β Λ`).  Then for every `i ∈ {0, …, q − 1}`,
`V_{Λ_i} ⊆ W_{q−1−i}(V_Λ)`: the ideal `V_{Λ_i} ⊆ R_{α−1,β}` generated by the products of the
tight patterns (on `([α − 1], [β])`) of the elements of the layer
`Λ_i = {ν ∈ BPar_q(α − 1, β) : F_Λ(ν) > i}` (`LamLayer q α β Λ i`) is contained in the slice
`W_{q−1−i}(V_Λ) ⊆ R_{α−1,β}` of Lemma 7.1 (peeling `w := x_1`, with `x_i` of `R_{α−1,β}` being
`x_{i+1}` of `R_{α,β}` and `z_l` being `z_l`), where `V_Λ ⊆ R_{α,β}`.  (`W_{q−1−i}(V_Λ)` is an
`F`-subspace of `R_{α−1,β}`, and the inclusion is an inclusion of sets.)  The hypothesis that `q`
is odd is kept as in the file, although the proof does not use it. -/
theorem prop75 (hq : 3 ≤ q) (hodd : Odd q)
    (hbin : ∀ t, t ≤ q - 1 → (((q - 1).choose t : ℕ) : F) ≠ 0) {α β : ℕ} (hα : 1 ≤ α)
    (Λ : Set (Partition × Partition)) (hΛ : IsDownSetB q α β Λ) (i : ℕ) (hi : i ≤ q - 1) :
    (VLamB F q (α - 1) β (LamLayer q α β Λ i) : Set (R F q (α - 1) β)) ⊆
      Wslice F q hα (VLamB F q α β Λ) (q - 1 - i) := by
  obtain ⟨I, hI⟩ := Wslice_isIdeal (F := F) hq hα (VLamB F q α β Λ) (q - 1 - i) (by omega)
  have hle : VLamB F q (α - 1) β (LamLayer q α β Λ i) ≤ I := by
    refine Ideal.span_le.2 ?_
    rintro _ ⟨μ, ⟨hμ, hiΦ⟩, T, rfl⟩
    rw [hI]
    exact prod_mem_Wslice (F := F) hq hbin hα hΛ hi hμ hiΦ T
  intro g hg
  have := hle hg
  rw [← SetLike.mem_coe, hI] at this
  exact this

end BipP3

end
