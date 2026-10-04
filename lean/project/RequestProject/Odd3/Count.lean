module

public import RequestProject.Odd3.Defs
public import RequestProject.EvenCount.Closed

/-!
# Parts (i) and (v) of the Theorem of `q_odd3.md` (the counts)

* (i) `card_Z_succ`, `card_Z_succ_zero` (with `m = n + 1`) and `card_Z_rec`, `card_Z_rec_zero`
  (with `1 ≤ m`, as in the file);
* (v) `card_Z_one_odd`: `|Z_1^{(2k+1)}| = Q^e_k(4)`.
-/

@[expose] public section

namespace Odd3

open Fibres

/-- Proof of part (i) of `q_odd3.md` (auxiliary): write `M = (t, M')`; then
`|Z_J^{(m)}|` is the sum over the tails `M'` of the number of completions `t`. -/
lemma card_Z_succ_eq_sum (n J : ℕ) : (Z (n + 1) J).card = ∑ M' : Fin n → Fin 3,
    (Finset.univ.filter fun t : Fin 3 => |val3 t + ∑ i, val3 (M' i)| ≤ (J : ℤ)).card := by
  rw [Z, Finset.card_filter]
  rw [← (Fin.consEquiv fun _ => Fin 3).sum_comp]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun M' _ => ?_
  rw [Finset.card_filter]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp [Fin.consEquiv, Fin.sum_univ_succ]

/-- Proof of part (i) of `q_odd3.md` (auxiliary): for `J ≥ 1` the number of `t ∈ {−1, 0, 1}` with
`|t + s'| ≤ J` is `[|s'| ≤ J + 1] + [|s'| ≤ J] + [|s'| ≤ J − 1]`. -/
lemma card_fiber (s : ℤ) (J : ℕ) (hJ : 1 ≤ J) :
    (Finset.univ.filter fun t : Fin 3 => |val3 t + s| ≤ (J : ℤ)).card =
      (if |s| ≤ ((J + 1 : ℕ) : ℤ) then 1 else 0) + (if |s| ≤ (J : ℤ) then 1 else 0) +
        (if |s| ≤ ((J - 1 : ℕ) : ℤ) then 1 else 0) := by
  rw [Finset.card_filter, Fin.sum_univ_three]
  simp only [val3, Fin.val_zero, Fin.val_one, Fin.val_two]
  push_cast [hJ]
  split_ifs <;> simp only [abs_le] at * <;> omega

/-- Proof of part (i) of `q_odd3.md` (auxiliary): for `J = 0`, `t = −s'` is the only possible
completion, and it exists exactly when `|s'| ≤ 1`. -/
lemma card_fiber_zero (s : ℤ) :
    (Finset.univ.filter fun t : Fin 3 => |val3 t + s| ≤ ((0 : ℕ) : ℤ)).card =
      (if |s| ≤ ((1 : ℕ) : ℤ) then 1 else 0) := by
  rw [Finset.card_filter, Fin.sum_univ_three]
  simp only [val3, Fin.val_zero, Fin.val_one, Fin.val_two]
  push_cast
  split_ifs <;> simp only [abs_le] at * <;> omega

/-- **Theorem, part (i)** of `q_odd3.md` (the count), first formula, written with `m = n + 1`:
`|Z_J^{(n+1)}| = |Z_{J+1}^{(n)}| + |Z_J^{(n)}| + |Z_{J−1}^{(n)}|` for every `J ≥ 1`. -/
theorem card_Z_succ (n J : ℕ) (hJ : 1 ≤ J) :
    (Z (n + 1) J).card = (Z n (J + 1)).card + (Z n J).card + (Z n (J - 1)).card := by
  rw [card_Z_succ_eq_sum]
  simp only [card_fiber _ J hJ, Finset.sum_add_distrib, Z, Finset.card_filter]

/-- **Theorem, part (i)** of `q_odd3.md` (the count), second formula, written with `m = n + 1`:
`|Z_0^{(n+1)}| = |Z_1^{(n)}|`. -/
theorem card_Z_succ_zero (n : ℕ) : (Z (n + 1) 0).card = (Z n 1).card := by
  rw [card_Z_succ_eq_sum, Finset.sum_congr rfl fun M' _ => card_fiber_zero _]
  simp only [Z, Finset.card_filter]

/-- **Theorem, part (i)** of `q_odd3.md` (the count), first formula, exactly as in the file: for
`m ≥ 1` and every `J ≥ 1`, `|Z_J^{(m)}| = |Z_{J+1}^{(m−1)}| + |Z_J^{(m−1)}| + |Z_{J−1}^{(m−1)}|`. -/
theorem card_Z_rec {m : ℕ} (hm : 1 ≤ m) (J : ℕ) (hJ : 1 ≤ J) :
    (Z m J).card = (Z (m - 1) (J + 1)).card + (Z (m - 1) J).card + (Z (m - 1) (J - 1)).card := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  exact card_Z_succ n J hJ

/-- **Theorem, part (i)** of `q_odd3.md` (the count), second formula, exactly as in the file: for
`m ≥ 1`, `|Z_0^{(m)}| = |Z_1^{(m−1)}|`. -/
theorem card_Z_rec_zero {m : ℕ} (hm : 1 ≤ m) : (Z m 0).card = (Z (m - 1) 1).card := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  exact card_Z_succ_zero n

/-- Proof of part (v) of `q_odd3.md` (auxiliary): `T = {−1, 0, 1}` (here `Fin 3`) with `u ↦ −u`
(here `Fin.rev`, `v ↦ 2 − v`) is a pointed point set with `o = 0` (here `1 : Fin 3`) and
`|T| = 3 = 2·1 + 1`. -/
def setting3 : EvenCount.PointedSetting (Fin 3) 1 where
  neg := Fin.rev
  neg_neg := Fin.rev_rev
  o := 1
  neg_o := by decide
  eq_o_of_neg_eq := by decide
  card_eq := rfl

/-- Proof of part (v) of `q_odd3.md` (auxiliary): the sum of `M` is `cnt_M(1) − cnt_M(−1)`. -/
lemma sum_val3_eq {N : ℕ} (M : Fin N → Fin 3) :
    ∑ i, val3 (M i) = (cnt M 2 : ℤ) - cnt M 0 := by
  rw [← Finset.sum_fiberwise Finset.univ M (fun i => val3 (M i)), Fin.sum_univ_three]
  have h : ∀ u : Fin 3, ∑ i ∈ Finset.univ with M i = u, val3 (M i) = (cnt M u : ℤ) * val3 u := by
    intro u
    rw [Finset.sum_congr rfl (g := fun _ => val3 u) (fun i hi => by
      rw [(Finset.mem_filter.1 hi).2]), Finset.sum_const, nsmul_eq_mul]
    rfl
  rw [h, h, h]
  simp [val3]
  ring

/-- Proof of part (v) of `q_odd3.md` (auxiliary): `cnt_M(−1) + cnt_M(0) + cnt_M(1) = N`. -/
lemma cnt_sum {N : ℕ} (M : Fin N → Fin 3) : cnt M 0 + cnt M 1 + cnt M 2 = N := by
  have := Finset.sum_fiberwise Finset.univ M (fun _ => (1 : ℕ))
  simp only [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_univ, Fintype.card_fin,
    Fin.sum_univ_three] at this
  simpa [cnt] using this

/-- Proof of part (v) of `q_odd3.md`: a tuple `M ∈ T^{2k+2}` is closed iff its sum is `0`
(`cnt_M(1) = cnt_M(−1)`, the evenness of `cnt_M(0)` being automatic). -/
lemma closedPointed_eq_Z (k : ℕ) : EvenCount.closedPointed setting3 (2 * k + 2) = Z (2 * k + 2) 0 := by
  ext M
  simp only [EvenCount.closedPointed, Z, Finset.mem_filter, Finset.mem_univ, true_and,
    sum_val3_eq, Nat.cast_zero, abs_nonpos_iff, sub_eq_zero]
  have hs := cnt_sum M
  constructor
  · rintro ⟨h, -⟩
    exact_mod_cast (h 0).symm
  · intro h
    have h' : cnt M 2 = cnt M 0 := by exact_mod_cast h
    refine ⟨fun u => ?_, ?_⟩
    · fin_cases u
      · exact h'.symm
      · rfl
      · exact h'
    · show Even (cnt M 1)
      exact ⟨k + 1 - cnt M 0, by omega⟩

/-- **Theorem, part (v)** of `q_odd3.md` (the number): `|Z_1^{(2k+1)}| = Q^e_k(4)`.  The tuples
of sum `0` in `T^{2k+2}` are the closed tuples of the pointed point set `T`, counted by part (iii)
of `q_even_count.md` (`EvenCount.card_closedPointed` with `h = 1`); they correspond to
`Z_1^{(2k+1)}` by deleting one entry (here the first one, through part (i):
`|Z_0^{(2k+2)}| = |Z_1^{(2k+1)}|`, instead of the last one as in the file). -/
theorem card_Z_one_odd (k : ℕ) : (Z (2 * k + 1) 1).card = EvenCount.QkEven k 4 := by
  rw [← card_Z_succ_zero, ← closedPointed_eq_Z, EvenCount.card_closedPointed]

end Odd3

end
