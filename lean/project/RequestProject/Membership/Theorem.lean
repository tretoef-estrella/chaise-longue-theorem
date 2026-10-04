module

public import RequestProject.Membership.Defs
public import RequestProject.Membership.Box
public import RequestProject.RankTwo.Main

/-!
# Theorem M of `q_membership.md`: the membership lemma

(M1) the coefficients of `bpf(Hm h y; c')` lie in `𝔘_{s'}(y)` for border columns polynomial in
`y`; (M2) the membership lemma for any exponents; (M3) Lemma 8.7 of the paper; (M4) the same on
a set `B` of indices. Throughout `r = 2h + 1` and `y` lies in the box (`y_i^r = 0`).
-/

@[expose] public section

namespace Membership

open Finset Pfaffian Polynomial

variable {A : Type*} [CommRing A]

/-- **(M1)** of Theorem M in `q_membership.md`: let `y : Fin n → A` with `y_i^{2h+1} = 0` for
every `i`, and let `c' = (c'_0, …, c'_{s'−1})` be border columns over `A[ζ]`, each polynomial in
`y` in the sense of (V3). Then every coefficient of `bpf(Hm h y; c')` lies in `𝔘_{s'}(y)`
(`U (2h+1) s' y`). The hypothesis `h ≥ 1` of Theorem M is not needed here (a more general
statement). Proof as in the file: (B5) `bpf_laplace`, (V3), (H2), (H3) and
`Ideal.mem_map_C_iff`. -/
theorem M1 (h : ℕ) {n s' : ℕ} (y : Fin n → A) (hy : ∀ i, y i ^ (2 * h + 1) = 0)
    (c' : Fin s' → Fin n → A[X]) (hc : ∀ k, PolyIn y (c' k)) (d : ℕ) :
    (bpf (RankTwo.Hm h y) c').coeff d ∈ U (2 * h + 1) s' y := by
  suffices hmem : bpf (RankTwo.Hm h y) c' ∈ Ideal.map C (U (2 * h + 1) s' y) from
    Ideal.mem_map_C_iff.1 hmem d
  rw [bpf_laplace _ (RankTwo.Hm_isAlt h y)]
  refine Ideal.mul_mem_left _ _ (Ideal.sum_mem _ fun S _ => ?_)
  obtain ⟨g, hg⟩ := V3 y S.1 S.2 c' hc
  rw [hg, H2]
  set ι' := S.1ᶜ.orderEmbOfFin (by rw [Finset.card_compl, Fintype.card_fin, S.2]) with hι'
  rw [H3 h (y ∘ ι') (fun i => hy _)]
  have key : ∀ π ∈ univ.filter (fun π : Fin (n - s') → Fin (n - s') => IsMatching π),
      C (Tight.vand y S.1) * ((-1) ^ (crossings π) *
        C (∏ x ∈ univ.filter (fun x => x < π x),
          ColOne.Dab (2 * h + 2) ((y ∘ ι') x) ((y ∘ ι') (π x))) *
        ∏ x ∈ univ.filter (fun x => x < π x), RankTwo.Od h (y ∘ ι') (π x)) ∈
        Ideal.map C (U (2 * h + 1) s' y) := by
    intro π hπ
    simp only [mem_filter, mem_univ, true_and] at hπ
    have hgen : Tight.vand y S.1 * ∏ x ∈ univ.filter (fun x => x < π x),
        ColOne.Dab (2 * h + 2) ((y ∘ ι') x) ((y ∘ ι') (π x)) ∈ U (2 * h + 1) s' y := by
      apply Ideal.subset_span
      refine ⟨S.1, pairsOf ι' π, subset_univ _, S.2, isPairs_pairsOf ι' hπ, ?_, ?_⟩
      · rw [supp_pairsOf ι' hπ, hι', map_orderEmbOfFin_univ, compl_eq_univ_sdiff]
      · rw [DPy_pairsOf]; rfl
    have e : C (Tight.vand y S.1) * ((-1) ^ (crossings π) *
        C (∏ x ∈ univ.filter (fun x => x < π x),
          ColOne.Dab (2 * h + 2) ((y ∘ ι') x) ((y ∘ ι') (π x))) *
        ∏ x ∈ univ.filter (fun x => x < π x), RankTwo.Od h (y ∘ ι') (π x)) =
        ((-1) ^ (crossings π) *
          ∏ x ∈ univ.filter (fun x => x < π x), RankTwo.Od h (y ∘ ι') (π x)) *
        C (Tight.vand y S.1 * ∏ x ∈ univ.filter (fun x => x < π x),
          ColOne.Dab (2 * h + 2) ((y ∘ ι') x) ((y ∘ ι') (π x))) := by
      rw [C_mul]; ring
    rw [e]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem C hgen)
  have e2 : ∀ a b c d : A[X], a * (b * c) * d = (a * c) * (b * d) := fun _ _ _ _ => by ring
  rw [e2, Finset.mul_sum]
  exact Ideal.mul_mem_left _ _ (Ideal.sum_mem _ key)

/-- **(M2)** (a) of Theorem M in `q_membership.md` (the membership lemma, any exponents): for
`h ≥ 1`, `y : Fin n → A` in the box (`y_i^{2h+1} = 0`), a list `e` of `s` exponents and
`n = s + 2(t + 1)`: `Pfe (2h+1) y e ∈ 𝔘_{s+2}(y)`. (From (S5)(a) and (M1); the case `t ≥ h`,
where the left side is `0`, is trivial.) -/
theorem M2a {h : ℕ} (hh : 1 ≤ h) {n s : ℕ} (t : ℕ) (hn : n = s + 2 * (t + 1))
    (y : Fin n → A) (hy : ∀ i, y i ^ (2 * h + 1) = 0) (e : Fin s → ℕ) :
    Pfe (2 * h + 1) y e ∈ U (2 * h + 1) (s + 2) y := by
  by_cases ht : t + 1 ≤ h
  · unfold Pfe
    rw [RankTwo.S5a_of_le hh t hn ht]
    refine Ideal.mul_mem_left _ _ (M1 h y hy _ (fun k => ?_) _)
    induction k using Fin.lastCases with
    | last => simpa only [Fin.snoc_last] using polyIn_Od h y
    | cast k =>
      simp only [Fin.snoc_castSucc]
      induction k using Fin.lastCases with
      | last => simpa only [Fin.snoc_last] using polyIn_Ev h y
      | cast k => simpa only [Fin.snoc_castSucc] using polyIn_pow y (e k)
  · unfold Pfe
    rw [RankTwo.S5a_of_ge hh t hn (by omega)]
    exact Ideal.zero_mem _

/-- **(M2)** (b) of Theorem M in `q_membership.md` (the membership lemma, any exponents): for
`h ≥ 1`, `y : Fin n → A` in the box, a list `e` of `s` exponents and `n = s + 1 + 2t`:
`Pf (2h+1) y (y^{e_0}, …, y^{e_{s−1}}, y^{2h}) ∈ 𝔘_{s+1}(y)`, the last border `i ↦ y_i^{2h}`
being appended with `Fin.snoc`. (From (S5)(b) and (M1); the case `t > h`, where the left side
is `0`, is trivial.) -/
theorem M2b {h : ℕ} (hh : 1 ≤ h) {n s : ℕ} (t : ℕ) (hn : n = s + 1 + 2 * t)
    (y : Fin n → A) (hy : ∀ i, y i ^ (2 * h + 1) = 0) (e : Fin s → ℕ) :
    Pf (2 * h + 1) y (Fin.snoc (α := fun _ => Fin n → A) (fun k i => y i ^ e k)
      (fun i => y i ^ (2 * h))) ∈ U (2 * h + 1) (s + 1) y := by
  by_cases ht : t ≤ h
  · rw [RankTwo.S5b_of_le hh t hn ht]
    refine Ideal.mul_mem_left _ _ (M1 h y hy _ (fun k => ?_) _)
    induction k using Fin.lastCases with
    | last => simpa only [Fin.snoc_last] using polyIn_Ev h y
    | cast k => simpa only [Fin.snoc_castSucc] using polyIn_pow y (e k)
  · rw [RankTwo.S5b_of_gt hh t hn (by omega)]
    exact Ideal.zero_mem _

/-- **(M3)** of Theorem M in `q_membership.md` (Lemma 8.7 of the paper), case `ℓ ≥ 1`, written
with `ℓ = l + 1`: if `n = l + 2 + 2t` (i.e. `n = ℓ + 1 + 2t`), then
`Pfe (2h+1) y (0, 1, …, ℓ − 2) ∈ 𝔘_{ℓ+1}(y) = U (2h+1) (l+2) y`. This is (M2)(a) with
`s = l`. -/
theorem M3_pos {h : ℕ} (hh : 1 ≤ h) {n l : ℕ} (t : ℕ) (hn : n = l + 2 + 2 * t)
    (y : Fin n → A) (hy : ∀ i, y i ^ (2 * h + 1) = 0) :
    Pfe (2 * h + 1) y (fun k : Fin l => (k : ℕ)) ∈ U (2 * h + 1) (l + 2) y :=
  M2a hh t (by omega) y hy _

/-- **(M3)** of Theorem M in `q_membership.md` (Lemma 8.7 of the paper), case `ℓ = 0`: if
`n = 1 + 2t`, then `Pfe (2h+1) y (2h) ∈ 𝔘_1(y)` (one border, `i ↦ y_i^{2h}`). This is (M2)(b)
with `s = 0`. -/
theorem M3_zero {h : ℕ} (hh : 1 ≤ h) {n : ℕ} (t : ℕ) (hn : n = 1 + 2 * t)
    (y : Fin n → A) (hy : ∀ i, y i ^ (2 * h + 1) = 0) :
    Pfe (2 * h + 1) y (fun _ : Fin 1 => 2 * h) ∈ U (2 * h + 1) 1 y := by
  have := M2b hh t (by omega) y hy (Fin.elim0 : Fin 0 → ℕ)
  have e : (Fin.snoc (α := fun _ => Fin n → A) (fun k i => y i ^ (Fin.elim0 k : ℕ))
      (fun i => y i ^ (2 * h)) : Fin 1 → Fin n → A) = fun _ i => y i ^ (2 * h) := by
    funext k i
    rw [Fin.fin_one_eq_zero k]
    rfl
  rw [e] at this
  exact this

/-- **(M4)** (a) of Theorem M in `q_membership.md` (the membership lemma on a set of indices):
let `h ≥ 1`, `y : Fin m → A` with `y_i^{2h+1} = 0` for every `i`, `B` a set of `n` indices of
`Fin m` with increasing enumeration `ι = B.orderEmbOfFin hB`, and `e` a list of `s` exponents.
If `n = s + 2(t + 1)`, then `Pfe (2h+1) (y ∘ ι) e ∈ 𝔘_{s+2}(y; B) = UB (2h+1) (s+2) y B`.
(From (M2)(a) by transporting the generators along `ι`.) -/
theorem M4a {h : ℕ} (hh : 1 ≤ h) {m n s : ℕ} (t : ℕ) (y : Fin m → A)
    (hy : ∀ i, y i ^ (2 * h + 1) = 0) (B : Finset (Fin m)) (hB : B.card = n)
    (hn : n = s + 2 * (t + 1)) (e : Fin s → ℕ) :
    Pfe (2 * h + 1) (y ∘ B.orderEmbOfFin hB) e ∈ UB (2 * h + 1) (s + 2) y B := by
  have h2 := U_le_UB (2 * h + 1) (s + 2) y (B.orderEmbOfFin hB)
    (M2a hh t hn (y ∘ B.orderEmbOfFin hB) (fun i => hy _) e)
  rwa [map_orderEmbOfFin_univ] at h2

/-- **(M4)** (b) of Theorem M in `q_membership.md` (the membership lemma on a set of indices):
with `h`, `y`, `B`, `ι`, `e` as in (M4)(a), if `n = s + 1 + 2t`, then
`Pf (2h+1) (y ∘ ι) ((y ∘ ι)^{e_0}, …, (y ∘ ι)^{e_{s−1}}, (y ∘ ι)^{2h}) ∈ 𝔘_{s+1}(y; B)`.
(From (M2)(b) by transporting the generators along `ι`.) -/
theorem M4b {h : ℕ} (hh : 1 ≤ h) {m n s : ℕ} (t : ℕ) (y : Fin m → A)
    (hy : ∀ i, y i ^ (2 * h + 1) = 0) (B : Finset (Fin m)) (hB : B.card = n)
    (hn : n = s + 1 + 2 * t) (e : Fin s → ℕ) :
    Pf (2 * h + 1) (y ∘ B.orderEmbOfFin hB)
      (Fin.snoc (α := fun _ => Fin n → A) (fun k i => y (B.orderEmbOfFin hB i) ^ e k)
        (fun i => y (B.orderEmbOfFin hB i) ^ (2 * h))) ∈ UB (2 * h + 1) (s + 1) y B := by
  have h2 := U_le_UB (2 * h + 1) (s + 1) y (B.orderEmbOfFin hB)
    (M2b hh t hn (y ∘ B.orderEmbOfFin hB) (fun i => hy _) e)
  rwa [map_orderEmbOfFin_univ] at h2

end Membership
