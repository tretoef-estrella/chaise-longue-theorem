module

public import RequestProject.Pfaffian.Main

/-!
# Part A of `q_oddbox_patterns.md`: the marked Pfaffian

This file formalizes **Definition (A0)** and **Lemma A** (A1)–(A7) of `q_oddbox_patterns.md`.
The bordered Pfaffians `Pfaffian.Pfe`, `Pfaffian.Pf`, `Pfaffian.bpf`, `Pfaffian.bmat`,
`Pfaffian.pf` and (C6) `Pfaffian.C6_e` of `RequestProject/Pfaffian/` are used unchanged, and
`D^− = ColOne.Dab (2h+1)`.
-/

@[expose] public section

namespace OddPatterns

open Pfaffian ColOne

variable {A : Type*} [CommRing A]

/-- **Definition (A0)** of `q_oddbox_patterns.md` (the marked Pfaffian): for `z : Fin n → A`,
`mPf_0(z) := Pf_{(2h)}(z)` (the single border `i ↦ z_i^{2h}`) and
`mPf_ℓ(z) := Pf_{(0, 1, …, ℓ−2)}(z)` for `ℓ ≥ 1` (no border for `ℓ = 1`). -/
noncomputable def mPf (h l : ℕ) {n : ℕ} (z : Fin n → A) : A :=
  if l = 0 then Pfe (2 * h + 1) z (fun _ : Fin 1 => 2 * h)
  else Pfe (2 * h + 1) z (fun k : Fin (l - 1) => (k : ℕ))

/-- Auxiliary for Lemma A of `q_oddbox_patterns.md`: `r = 2h + 1` is odd. -/
theorem odd_two_mul_add_one (h : ℕ) : Odd (2 * h + 1) := ⟨h, rfl⟩

/-- **Lemma A, (A1)** of `q_oddbox_patterns.md`: for `z : Fin 1 → A`, `mPf_0(z) = z_0^{2h}`. -/
theorem A1 (h : ℕ) (z : Fin 1 → A) : mPf h 0 z = z 0 ^ (2 * h) := by
  simp only [mPf, if_pos, Pfe, Pf, bpf]
  rw [pf_two]
  rfl

/-- **Lemma A, (A2)** of `q_oddbox_patterns.md`: for `z : Fin 2 → A`,
`mPf_1(z) = D^−(z_0, z_1)`. -/
theorem A2 (h : ℕ) (z : Fin 2 → A) : mPf h 1 z = Dab (2 * h + 1) (z 0) (z 1) := by
  simp only [mPf, one_ne_zero, if_false, Pfe, Pf, bpf]
  rw [pf_two]
  rfl

/-- **Lemma A, (A3)** of `q_oddbox_patterns.md`: for `z : Fin 3 → A`,
`mPf_0(z) = z_2^{2h}·D^−(z_0, z_1) − z_1^{2h}·D^−(z_0, z_2) + z_0^{2h}·D^−(z_1, z_2)`. -/
theorem A3 (h : ℕ) (z : Fin 3 → A) :
    mPf h 0 z = z 2 ^ (2 * h) * Dab (2 * h + 1) (z 0) (z 1) -
      z 1 ^ (2 * h) * Dab (2 * h + 1) (z 0) (z 2) +
      z 0 ^ (2 * h) * Dab (2 * h + 1) (z 1) (z 2) := by
  simp only [mPf, if_pos, Pfe, Pf, bpf]
  rw [pf_four]
  change Dab (2 * h + 1) (z 0) (z 1) * z 2 ^ (2 * h) -
      Dab (2 * h + 1) (z 0) (z 2) * z 1 ^ (2 * h) +
      z 0 ^ (2 * h) * Dab (2 * h + 1) (z 1) (z 2) = _
  ring

/-- **Lemma A, (A4)** of `q_oddbox_patterns.md`: for `z : Fin 3 → A`,
`mPf_2(z) = D^−(z_0, z_1) − D^−(z_0, z_2) + D^−(z_1, z_2)`. -/
theorem A4 (h : ℕ) (z : Fin 3 → A) :
    mPf h 2 z = Dab (2 * h + 1) (z 0) (z 1) - Dab (2 * h + 1) (z 0) (z 2) +
      Dab (2 * h + 1) (z 1) (z 2) := by
  simp only [mPf, two_ne_zero, if_false, Pfe, Pf, bpf]
  rw [pf_four]
  change Dab (2 * h + 1) (z 0) (z 1) * z 2 ^ 0 -
      Dab (2 * h + 1) (z 0) (z 2) * z 1 ^ 0 +
      z 0 ^ 0 * Dab (2 * h + 1) (z 1) (z 2) = _
  ring

/-- **Lemma A, (A5)** of `q_oddbox_patterns.md` (parity): if `n + ℓ` is even, then
`mPf_ℓ(z) = 0`. -/
theorem A5 (h l : ℕ) {n : ℕ} (z : Fin n → A) (hev : Even (n + l)) : mPf h l z = 0 := by
  unfold mPf
  split_ifs with hl
  · subst hl
    exact pf_odd _ _ (by rcases hev with ⟨k, hk⟩; exact ⟨k, by omega⟩)
  · exact pf_odd _ _ (by rcases hev with ⟨k, hk⟩; exact ⟨k - 1, by omega⟩)

/-- **Lemma A, (A6)** of `q_oddbox_patterns.md`: for `ℓ ≥ 1` and `z : Fin n → A` with
`n + 1 < ℓ`, `mPf_ℓ(z) = 0` (more borders than indices; from (B0) `Pfaffian.bpf_eq_zero_of_lt`). -/
theorem A6 (h l : ℕ) {n : ℕ} (z : Fin n → A) (hl : 1 ≤ l) (hn : n + 1 < l) :
    mPf h l z = 0 := by
  unfold mPf
  rw [if_neg (by omega)]
  exact bpf_eq_zero_of_lt _ (ay_isAlt (odd_two_mul_add_one h) z) _ (by omega)

/-- **Lemma A, (A7)** of `q_oddbox_patterns.md` (relabelling): for a permutation `σ` of `Fin n`,
`mPf_ℓ(z ∘ σ) = sgn(σ)·mPf_ℓ(z)` (from (C6) `Pfaffian.C6_e`). -/
theorem A7 (h l : ℕ) {n : ℕ} (z : Fin n → A) (σ : Equiv.Perm (Fin n)) :
    mPf h l (fun i => z (σ i)) = ((Equiv.Perm.sign σ : ℤ) : A) * mPf h l z := by
  unfold mPf
  split_ifs <;> exact C6_e (odd_two_mul_add_one h) z _ σ

/-- Auxiliary for (C1) of `q_oddbox_patterns.md`: `pf` commutes with ring homomorphisms. -/
theorem map_pf {A' : Type*} [CommRing A'] (f : A →+* A') :
    ∀ (m : ℕ) (M : Matrix (Fin m) (Fin m) A), f (pf m M) = pf m (fun i j => f (M i j))
  | 0, _ => by simp
  | 1, _ => by simp
  | m + 2, M => by
    rw [pf_succ_succ, pf_succ_succ, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, map_mul, map_pow, map_neg, map_one, map_pf f m]
    rfl

/-- Auxiliary for (C1) of `q_oddbox_patterns.md`: `mPf_ℓ` commutes with ring homomorphisms
(it is a polynomial expression with integer coefficients in the `z_i`). -/
theorem map_mPf {A' : Type*} [CommRing A'] (f : A →+* A') (h l : ℕ) {n : ℕ} (z : Fin n → A) :
    f (mPf h l z) = mPf h l (fun i => f (z i)) := by
  have key : ∀ {s : ℕ} (e : Fin s → ℕ), f (Pfe (2 * h + 1) z e) =
      Pfe (2 * h + 1) (fun i => f (z i)) e := by
    intro s e
    unfold Pfe Pf bpf
    rw [map_pf]
    congr 1
    funext p q
    induction p using Fin.addCases with
    | left i =>
      induction q using Fin.addCases with
      | left j => simp [ay, map_Dab]
      | right k => simp
    | right k =>
      induction q using Fin.addCases with
      | left j => simp
      | right k' => simp
  unfold mPf
  split_ifs <;> exact key _

/-- Auxiliary for (B6) and (C1) of `q_oddbox_patterns.md`: `mPf_ℓ` is unchanged when the index
type `Fin n'` is replaced by `Fin n` along an equality `n = n'`. -/
theorem mPf_cast (h l : ℕ) {n n' : ℕ} (hn : n = n') (z : Fin n' → A) :
    mPf h l (fun i => z (Fin.cast hn i)) = mPf h l z := by
  subst hn
  rfl

end OddPatterns
