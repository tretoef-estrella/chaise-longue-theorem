module

public import RequestProject.Lifts.Lift

/-!
# The Proposition of `q_P3_lifts.md`

For every down-set `Λ` of `Par_m` and every `i ∈ {0, …, q − 2}`: `V_{Λ_i} ⊆ W_{q−2−i}(V_Λ)`.

The file follows the **Proof** of `q_P3_lifts.md`: Step 0 is in `RequestProject/Lifts/Options.lean`,
the reduction of Step 1 in `RequestProject/Lifts/Algebra.lean`, the tight patterns of the cases
(α), (β), (γ) in `RequestProject/Lifts/Lift.lean`; here the coefficient computations of the
cases are carried out and everything is assembled.
-/

@[expose] public section

open Polynomial

namespace Lifts

open Peel hiding C
open Tight ChainLemma

set_option synthInstance.maxHeartbeats 200000

variable {F : Type*} [Field F] {q : ℕ}

/-- **Cases (α) and (β)** of the Proof in `q_P3_lifts.md` (with `m = n + 1`): let `λ ∈ Λ` have the
columns of `μ` except that column `c* ≥ 1` is one longer, and let `G` be the product of a tight
pattern of `μ` on `{2, …, m}`.  If the height `μ'_{c*} = |B_{c*}|` is at most `q − 2`, then
`G ∈ W_{μ'_{c*}}(V_Λ)`: the lifted pattern (index `1` put into `B_{c*}`) has product
`f = Π_{c ∈ B_{c*}} (y_c − y_1) · G ∈ V_Λ`, of `y_1`-degree `|B_{c*}|` with top coefficient
`(−1)^{|B_{c*}|} G` (part (iii) of `q_P3_identities.md`). -/
theorem mem_W_of_insert (hq : 2 ≤ q) {n : ℕ} {Λ : Set Partition} {μ lam : Partition}
    (hlam : lam ∈ Λ) (T : TightPattern μ (Finset.univ : Finset (Fin n))) {cs : ℕ} (hcs : 1 ≤ cs)
    (hcol : ∀ c, 1 ≤ c → colLen lam c = colLen μ c + if c = cs then 1 else 0)
    (hd : colLen μ cs ≤ q - 2) :
    T.prod F q ∈ W (m := n + 1) (by omega) (VLamAll F q (n + 1) Λ) (colLen μ cs) := by
  haveI := nontrivial_C (F := F) (q := q) (m := n) hq
  obtain ⟨T', hT'⟩ := exists_pattern_insert (F := F) (q := q) T hcs hcol
  have hf : T'.prod F q ∈ VLamAll F q (n + 1) Λ := Ideal.subset_span ⟨lam, hlam, T', rfl⟩
  set B := cleanBlocks T cs with hBdef
  have hcard : B.card = colLen μ cs := card_cleanBlocks T hcs
  set Pol : (Peel.C F q n)[X] :=
    Polynomial.C (T.prod F q) * ∏ x ∈ B, (Polynomial.C (y F q x) - X) with hPol
  have hphi : peelEquiv' F q n (T'.prod F q) = AdjoinRoot.mk _ Pol := by
    have hs : ∀ x : Fin n, y F q x.succ = incl F q n (y F q x) := fun x => (incl_y x).symm
    rw [hT', map_mul, map_prod, phi_incl, hPol, map_mul, map_prod, mul_comm]
    simp only [map_sub, hs, phi_incl, phi_y0, AdjoinRoot.mk_C, AdjoinRoot.mk_X]
  obtain ⟨h1, h2⟩ := coeff_C_mul_prod B (fun x => y F q x) (T.prod F q)
  have hmem := coeff_mem_W hq _ hf Pol hphi (d := B.card) (by omega) h1
  rw [h2, hcard] at hmem
  exact mem_of_neg_one_pow_mul_mem _ hmem

/-- **Case (γ)** of the Proof in `q_P3_lifts.md` (with `m = n + 1`): let `λ ∈ Λ` have the columns
of `μ` except that column `c ≥ 1` is one shorter, of height `r = μ'_c` with `1 ≤ r ≤ q − 1`, and
let `G = Δ(S) · G'` be the product of a tight pattern of `μ` on `{2, …, m}` (`S = B_c`).  Then
`G ∈ W_{q−1−r}(V_Λ)`: the element `f := Σ_{b ∈ S} ε_b Δ(S ∖ {b}) D(y_1, y_b) G' ∈ V_Λ` has, by
parts (i) and (ii) of `q_P3_identities.md`, `[y_1^{q−2−t}] f = ± (Σ_b ε_b Δ(S ∖ {b}) y_b^t) G'`,
which is `0` for `t ≤ r − 2` and `±Δ(S) G' = ±G` for `t = r − 1`. -/
theorem mem_W_of_pair (hq : 2 ≤ q) {n : ℕ} {Λ : Set Partition} {μ lam : Partition}
    (hlam : lam ∈ Λ) (T : TightPattern μ (Finset.univ : Finset (Fin n))) {c0 : ℕ} (hc0 : 1 ≤ c0)
    (hcol : ∀ c, 1 ≤ c → colLen lam c + (if c = c0 then 1 else 0) = colLen μ c)
    (hr : 1 ≤ colLen μ c0) (hrq : colLen μ c0 ≤ q - 1) :
    T.prod F q ∈ W (m := n + 1) (by omega) (VLamAll F q (n + 1) Λ) (q - 1 - colLen μ c0) := by
  classical
  set S := cleanBlocks T c0 with hSdef
  have hcard : S.card = colLen μ c0 := card_cleanBlocks T hc0
  set N := lam.row 1 + μ.row 1 + c0 with hNdef
  set G' : Peel.C F q n := (∏ e ∈ T.pairs, pairD F q e) *
    ∏ c ∈ (Finset.Icc 1 N).erase c0, Delta F q (cleanBlocks T c) with hG'
  have hG : T.prod F q = Delta F q S * G' := by
    rw [prod_cleanBlocks T (N := N) (by omega),
      ← Finset.mul_prod_erase _ _ (Finset.mem_Icc.2 ⟨hc0, (by omega : c0 ≤ N)⟩), hG']
    ring
  have hex : ∀ b ∈ S, ∃ T' : TightPattern lam (Finset.univ : Finset (Fin (n + 1))),
      T'.prod F q = D F q 0 b.succ * incl F q n (Delta F q (S.erase b) * G') :=
    fun b hb => exists_pattern_pair (F := F) (q := q) T hc0 hcol (N := N) (by omega) (by omega)
      (by omega) hb
  choose Tb hTb using hex
  set eps : Fin n → Peel.C F q n := fun b => (-1) ^ (S.card + ((S.filter (· < b)).card + 1))
    with heps
  set f : Peel.C F q (n + 1) :=
    ∑ b ∈ S.attach, incl F q n (eps b.1) * (Tb b.1 b.2).prod F q with hfdef
  have hf : f ∈ VLamAll F q (n + 1) Λ :=
    Ideal.sum_mem _ (fun b _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨lam, hlam, _, rfl⟩))
  set Pol : (Peel.C F q n)[X] :=
    ∑ b ∈ S.attach, Polynomial.C (eps b.1 * Delta F q (S.erase b.1) * G') * dpoly q (y F q b.1)
    with hPol
  have hphi : peelEquiv' F q n f = AdjoinRoot.mk _ Pol := by
    rw [hfdef, hPol, map_sum, map_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [hTb, map_mul, map_mul, phi_incl, phi_incl, phi_D]
    simp only [map_mul, AdjoinRoot.mk_C]
    ring
  have hcoeff : ∀ k, Pol.coeff k = if k < q - 1 then
      (-1) ^ k * G' * ∑ b ∈ S, eps b * Delta F q (S.erase b) * y F q b ^ (q - 2 - k) else 0 := by
    intro k
    rw [hPol, finset_sum_coeff]
    simp only [coeff_C_mul, coeff_dpoly]
    split_ifs with hk
    · rw [Finset.sum_attach S (fun b => eps b * Delta F q (S.erase b) * G' *
        ((-1) ^ k * y F q b ^ (q - 2 - k))), Finset.mul_sum]
      exact Finset.sum_congr rfl (fun b _ => by ring)
    · simp
  obtain ⟨hz, htop⟩ := sum_eps_Delta (F := F) (q := q) S (by omega)
  have hvan : ∀ k, q - 1 - colLen μ c0 < k → Pol.coeff k = 0 := by
    intro k hk
    rw [hcoeff k]
    split_ifs with hk'
    · rw [hz (q - 2 - k) (by omega), mul_zero]
    · rfl
  have hmem := coeff_mem_W hq _ hf Pol hphi (d := q - 1 - colLen μ c0) (by omega) hvan
  rw [hcoeff, if_pos (by omega), show q - 2 - (q - 1 - colLen μ c0) = S.card - 1 by omega, htop,
    mul_assoc, mul_comm G', ← hG] at hmem
  exact mem_of_neg_one_pow_mul_mem _ hmem

/-- **Step 1** of the Proof in `q_P3_lifts.md` (with `m = n + 1`): for `μ ∈ Λ_i` and every tight
pattern of `μ` on `{2, …, m}` with product `G`, we have `G ∈ W_{q−2−i}(V_Λ)`.  With
`Φ = F_Λ(μ) ≥ i + 1` one shows (∗) `G ∈ W_{q−1−Φ}(V_Λ)` by the cases (α), (β) (`mem_W_of_insert`)
and (γ) (`mem_W_of_pair`), and concludes by `W_j(V_Λ) ⊆ W_{j+1}(V_Λ)` (part (ii) of
`q_peeling_lemma.md`) since `q − 1 − Φ ≤ q − 2 − i`. -/
theorem prod_mem_W (hq : 3 ≤ q) (hodd : Odd q) {n : ℕ} {Λ : Set Partition}
    (hΛ : IsDownSetPar ((q - 1) / 2) (n + 1) Λ) {i : ℕ} (hi : i ≤ q - 2) {μ : Partition}
    (hμ : μ ∈ Par ((q - 1) / 2) n) (hiΦ : i < Fibres.FLam ((q - 1) / 2) Λ μ)
    (T : TightPattern μ (Finset.univ : Finset (Fin n))) :
    T.prod F q ∈ W (m := n + 1) (by omega) (VLamAll F q (n + 1) Λ) (q - 2 - i) := by
  have hL : 2 * ((q - 1) / 2) = q - 1 := by obtain ⟨k, rfl⟩ := hodd; omega
  have hΦL := FLam_le ((q - 1) / 2) Λ μ
  rcases cases_of_FLam hΛ hμ (by omega) with
    ⟨lam, hlam, cs, hcs, hcol, hsum⟩ | ⟨lam, hlam, c0, hc0, hcol, hr⟩
  · have h := mem_W_of_insert (F := F) (q := q) (by omega) hlam T hcs hcol (by omega)
    exact W_mono_le hq _ _ (by omega) (by omega) h
  · have h := mem_W_of_pair (F := F) (q := q) (by omega) hlam T hc0 hcol (by omega) (by omega)
    exact W_mono_le hq _ _ (by omega) (by omega) h

/-- **Proposition** of `q_P3_lifts.md`.  Let `q ≥ 3` be odd, `h = (q − 1)/2`, `m ≥ 1`, and let `Λ`
be a down-set of `Par_m` (`IsDownSetPar h m Λ`: `Λ ⊆ Par_m`, and `λ ∈ Par_m`, `λ ≼ μ ∈ Λ` imply
`λ ∈ Λ`).  Then for every `i ∈ {0, …, q − 2}`, the ideal `V_{Λ_i} ⊆ C_{m−1}` generated by the
products of the tight patterns of the elements of `Λ_i = {μ ∈ Par_{m−1} : F_Λ(μ) > i}` on all the
variables `y_2, …, y_m` of `C_{m−1}` is contained in `W_{q−2−i}(V_Λ)`, where
`V_Λ = V_Λ({1, …, m}) ⊆ C_m`.  (As in `q_peeling_lemma.md`, `W_{q−2−i}(V_Λ)` is an `F`-subspace of
`C_{m−1}`, and the inclusion is an inclusion of sets.) -/
theorem layer_subset_W (hq : 3 ≤ q) (hodd : Odd q) {m : ℕ} (hm : 1 ≤ m) (Λ : Set Partition)
    (hΛ : IsDownSetPar ((q - 1) / 2) m Λ) (i : ℕ) (hi : i ≤ q - 2) :
    (VLamAll F q (m - 1) (layer ((q - 1) / 2) m Λ i) : Set (Peel.C F q (m - 1))) ⊆
      W hm (VLamAll F q m Λ) (q - 2 - i) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  obtain ⟨I, hI⟩ := W_isIdeal hq hm (VLamAll F q (n + 1) Λ) (q - 2 - i) (by omega)
  have hle : VLamAll F q (n + 1 - 1) (layer ((q - 1) / 2) (n + 1) Λ i) ≤ I := by
    refine Ideal.span_le.2 ?_
    rintro _ ⟨μ, ⟨hμ, hiΦ⟩, T, rfl⟩
    have := prod_mem_W (F := F) hq hodd hΛ hi hμ hiΦ T
    rw [hI]
    exact this
  intro x hx
  have := hle hx
  rw [← SetLike.mem_coe, hI] at this
  exact this

end Lifts

end
