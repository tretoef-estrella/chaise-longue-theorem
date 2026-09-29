module

public import RequestProject.ColOne.Sum

/-!
# The generators `g_P` in the coordinates `y` (`q_col_one.md`, Lemma 2.4 (ii))

This file formalizes **Lemma 2.4 (ii)** of `q_col_one.md`: for the block `W_1 = 𝒞_1 ∖ {0}` of
`q_col_decomp.md` (where the point `c` is `1`), `g_P = u·Y_{W_1}·D_P` in `B(W_1)`.

Conventions (from `q_col_decomp.md`): the box ring `B(W_1)` is `(boxS S c).Box (W1 S c)`, the
variables `t_a ∈ B(W_1)` indexed by `a ∈ V = {0, …, d}` are `tB S c (W1 S c) a`, and `g_P` is
`gP S c P` for a perfect matching `P` of `𝒞_1 = cls (cExt c) 1`.  Here `y_a := t_a − t_a^{−1}` is
`yB S c W a` (for `a = j + 1`, `j ∈ W`, this is the coordinate `y_j` of `yW`; the value at `a = 0`
is an unused dummy value).
-/

@[expose] public section

open MvPolynomial

namespace ColOne

open ColSplit ColSurv ColComp ColTensor ColDecomp

open scoped Classical

variable {F : Type*} [Field F] (S : ColSetting F) {k : ℕ}

/-- **Setting** of `q_col_decomp.md` (used in Lemma 2.4 (ii) of `q_col_one.md`):
`j ∈ W_1 = 𝒞_1 ∖ {0}` iff the element `j + 1` of `V` lies in `𝒞_1`. -/
theorem mem_W1 {c : Fin (2 * k + 1) → S.μ} {j : Fin (2 * k + 1)} :
    j ∈ W1 S c ↔ j.succ ∈ cls (cExt c) 1 := by
  simp [W1, varSet]

/-- **Lemma 2.4 (ii)** of `q_col_one.md`: the point `c` has `c_s = 1` on `W_1 = 𝒞_1 ∖ {0}`, i.e. the
box ring `B(W_1)` is a box ring at the point `1`. -/
theorem boxS_c_W1 (c : Fin (2 * k + 1) → S.μ) : ∀ s : W1 S c, (boxS S c).c s = 1 := by
  intro s
  have := (mem_W1 S).1 s.2
  rw [mem_cls] at this
  simpa [boxS, cExt] using this

/-- **Lemma 2.4 (ii)** of `q_col_one.md`: `y_a := t_a − t_a^{−1} ∈ B(W)` for `a ∈ V` (for `a = 0`, and
for variables outside `W`, this is the unused dummy value `0 − 0^{−1} = 0`). -/
noncomputable def yB (c : Fin (2 * k + 1) → S.μ) (W : Finset (Fin (2 * k + 1))) :
    Fin (2 * k + 2) → (boxS S c).Box W :=
  fun a => tB S c W a - Ring.inverse (tB S c W a)

/-- **Setting** of `q_col_decomp.md`: `t_{j+1} ∈ B(W)` is the variable `t_j` of `B(W)` for `j ∈ W`. -/
theorem tB_succ (c : Fin (2 * k + 1) → S.μ) (W : Finset (Fin (2 * k + 1))) {j : Fin (2 * k + 1)}
    (h : j ∈ W) : tB S c W j.succ = (boxS S c).t W ⟨j, h⟩ := by
  simp [tB, h]

/-- **Lemma 2.4 (ii)** of `q_col_one.md`: `y_{j+1} = y_j` (the coordinate of Lemma 2.3) for
`j ∈ W`. -/
theorem yB_succ (c : Fin (2 * k + 1) → S.μ) (W : Finset (Fin (2 * k + 1))) {j : Fin (2 * k + 1)}
    (h : j ∈ W) : yB S c W j.succ = yW (boxS S c) W ⟨j, h⟩ := by
  simp only [yB, tB_succ S c W h, yW]

/-- **Lemma 2.4 (ii)** of `q_col_one.md`: `D_P := Π D(y_a, y_b) ∈ B(W_1)` over the pairs `{a < b}`
of the perfect matching `P` of `𝒞_1` with `a ≠ 0` (the pairs avoiding `0`; each pair is recorded by
its smaller element `a`, with `b = P(a)`; the empty product is `1`). -/
noncomputable def DP (c : Fin (2 * k + 1) → S.μ) (P : PerfMatch (cls (cExt c) 1)) :
    (boxS S c).Box (W1 S c) :=
  ∏ x ∈ Finset.univ.filter (fun x => x.1 ≠ 0 ∧ x.1 < (P.1 x).1),
    Dab S.q (yB S c (W1 S c) x.1) (yB S c (W1 S c) (P.1 x).1)

/-- **Proof of Lemma 2.4 (ii)** of `q_col_one.md`: the monomial factor `y_a` of an index `a`, with
the convention that the index `0` contributes `1`. -/
noncomputable def gy (c : Fin (2 * k + 1) → S.μ) (a : Fin (2 * k + 2)) : (boxS S c).Box (W1 S c) :=
  if a = 0 then 1 else yB S c (W1 S c) a

/-- **Proof of Lemma 2.4 (ii)** of `q_col_one.md`: for a pair `{a < b}` of `𝒞_1`,
`f_{0,b} = u·y_b` and, for `a ≠ 0`, `f_{a,b} = u·(y_a y_b D(y_a, y_b))` with `u` a unit. -/
theorem pairF_eq_unit_mul (hp : S.p ≠ 2) (c : Fin (2 * k + 1) → S.μ) {a b : Fin (2 * k + 2)}
    (ha : a ∈ cls (cExt c) 1) (hb : b ∈ cls (cExt c) 1) (hb0 : b ≠ 0) :
    ∃ u : ((boxS S c).Box (W1 S c))ˣ, pairF S.q (tB S c (W1 S c)) a b =
      u * ((gy S c a * gy S c b) *
        (if a = 0 then 1 else Dab S.q (yB S c (W1 S c) a) (yB S c (W1 S c) b))) := by
  obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.2 hb0
  have hj : j ∈ W1 S c := (mem_W1 S).2 hb
  have hc := boxS_c_W1 S c
  have hgb : gy S c j.succ = yW (boxS S c) (W1 S c) ⟨j, hj⟩ := by
    rw [gy, if_neg (Fin.succ_ne_zero j), yB_succ S c _ hj]
  by_cases ha0 : a = 0
  · subst ha0
    obtain ⟨u, hu⟩ := lemma23_ii_one hp hc ⟨j, hj⟩
    refine ⟨u, ?_⟩
    rw [pairF, if_pos rfl, if_pos rfl, gy, if_pos rfl, hgb, tB_succ S c _ hj, hu]
    ring
  · obtain ⟨i, rfl⟩ := Fin.exists_succ_eq.2 ha0
    have hi : i ∈ W1 S c := (mem_W1 S).2 ha
    have hga : gy S c i.succ = yW (boxS S c) (W1 S c) ⟨i, hi⟩ := by
      rw [gy, if_neg (Fin.succ_ne_zero i), yB_succ S c _ hi]
    obtain ⟨u1, hu1⟩ := lemma23_ii_one hp hc ⟨j, hj⟩
    obtain ⟨u2, hu2⟩ := lemma23_ii_two hp hc ⟨i, hi⟩ ⟨j, hj⟩
    have key := lemma24_i hp (yW (boxS S c) (W1 S c) ⟨i, hi⟩)
      (yW (boxS S c) (W1 S c) ⟨j, hj⟩) (yW_pow hc _)
    refine ⟨-(u1 * u2 ^ (S.q - 1)), ?_⟩
    rw [pairF, if_neg (Fin.succ_ne_zero i), if_neg (Fin.succ_ne_zero i), hga, hgb,
      tB_succ S c _ hj, tB_succ S c _ hi, yB_succ S c _ hi, yB_succ S c _ hj, hu1, hu2, mul_pow]
    simp only [Units.val_neg, Units.val_mul, Units.val_pow_eq_pow_val]
    linear_combination (↑u1 * ↑u2 ^ (S.q - 1)) * key

/-- **Proof of Lemma 2.4 (ii)** of `q_col_one.md` ("the pairs of `P` partition `𝒞_1`"): for a
fixed-point-free involution `P` of a finite type and an injective `key` into a linear order,
`Π_{x : key x < key (P x)} f(x) f(P x) = Π_x f(x)`. -/
theorem prod_pairs_eq_prod {T L M : Type*} [Fintype T] [LinearOrder L] [CommMonoid M]
    (P : PerfMatch T) (key : T → L) (hkey : Function.Injective key) (f : T → M) :
    ∏ x ∈ Finset.univ.filter (fun x => key x < key (P.1 x)), f x * f (P.1 x) = ∏ x, f x := by
  have hne : ∀ x, key (P.1 x) ≠ key x := fun x h => (P.2 x).1 (hkey h)
  rw [Finset.prod_mul_distrib,
    ← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun x => key x < key (P.1 x))]
  congr 1
  refine Finset.prod_nbij' P.1 P.1 ?_ ?_ ?_ ?_ ?_
  · intro x hx
    replace hx : key x < key (P.1 x) := by simpa using hx
    change P.1 x ∈ Finset.univ.filter _
    rw [Finset.mem_filter, (P.2 x).2]
    exact ⟨Finset.mem_univ _, not_lt.2 hx.le⟩
  · intro x hx
    replace hx : ¬ key x < key (P.1 x) := by simpa using hx
    change P.1 x ∈ Finset.univ.filter _
    rw [Finset.mem_filter, (P.2 x).2]
    refine ⟨Finset.mem_univ _, ?_⟩
    exact lt_of_le_of_ne (not_lt.1 hx) (hne x)
  · intro x _; exact (P.2 x).2
  · intro x _; exact (P.2 x).2
  · intro x _; rfl

/-- **Proof of Lemma 2.4 (ii)** of `q_col_one.md`: the indices occurring in the monomial factors are
the elements of `𝒞_1 ∖ {0} = W_1`, each once: `Π_{a ∈ 𝒞_1} (y_a or 1 for a = 0) = Y_{W_1}`. -/
theorem prod_gy (c : Fin (2 * k + 1) → S.μ) :
    ∏ x : cls (cExt c) 1, gy S c x.1 = YW (boxS S c) (W1 S c) := by
  have h1 : ∏ x : cls (cExt c) 1, gy S c x.1 =
      ∏ x ∈ Finset.univ.filter (fun x : cls (cExt c) 1 => x.1 ≠ 0), yB S c (W1 S c) x.1 := by
    rw [Finset.prod_filter]
    refine Finset.prod_congr rfl fun x _ => ?_
    by_cases h : x.1 = 0 <;> simp [gy, h]
  rw [h1, YW]
  symm
  refine Finset.prod_nbij (fun s : W1 S c => (⟨s.1.succ, (mem_W1 S).1 s.2⟩ : cls (cExt c) 1))
    ?_ ?_ ?_ ?_
  · intro s _
    simp [Fin.succ_ne_zero]
  · intro s _ s' _ h
    exact Subtype.ext (Fin.succ_injective _ (congrArg Subtype.val h))
  · intro x hx
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hx
    obtain ⟨j, hj⟩ := Fin.exists_succ_eq.2 hx
    have hjW : j ∈ W1 S c := (mem_W1 S).2 (hj ▸ x.2)
    exact ⟨⟨j, hjW⟩, by simp, Subtype.ext hj⟩
  · intro s _
    rw [yB_succ S c _ s.2]

/-- **Lemma 2.4 (ii)** of `q_col_one.md`: suppose `c_s = 1` on `W = 𝒞_1 ∖ {0}` (as for `W_1` of
`q_col_decomp.md`, automatically) and `p ≠ 2`, and let `P` be a perfect matching of `𝒞_1`. Then in
`B(W_1)`, `g_P = u·Y_{W_1}·D_P` with `u` a unit, `Y_{W_1} = Π_{s ∈ W_1} y_s` and
`D_P = Π D(y_a, y_b)` over the pairs `{a < b}` of `P` with `a ≠ 0`. -/
theorem lemma24_ii (hp : S.p ≠ 2) (c : Fin (2 * k + 1) → S.μ) (P : PerfMatch (cls (cExt c) 1)) :
    ∃ u : ((boxS S c).Box (W1 S c))ˣ,
      gP S c P = u * (YW (boxS S c) (W1 S c) * DP S c P) := by
  set Fs := Finset.univ.filter (fun x : cls (cExt c) 1 => x.1 < (P.1 x).1)
  have H : ∀ x : cls (cExt c) 1, x.1 < (P.1 x).1 →
      ∃ u : ((boxS S c).Box (W1 S c))ˣ, pairF S.q (tB S c (W1 S c)) x.1 (P.1 x).1 =
        u * ((gy S c x.1 * gy S c (P.1 x).1) *
          (if x.1 = 0 then 1 else
            Dab S.q (yB S c (W1 S c) x.1) (yB S c (W1 S c) (P.1 x).1))) := fun x hx =>
    pairF_eq_unit_mul S hp c x.2 (P.1 x).2 (ne_of_gt (lt_of_le_of_lt (Fin.zero_le _) hx))
  set U : cls (cExt c) 1 → ((boxS S c).Box (W1 S c))ˣ := fun x =>
    if h : x.1 < (P.1 x).1 then (H x h).choose else 1
  refine ⟨∏ x ∈ Fs, U x, ?_⟩
  have e1 : gP S c P = ∏ x ∈ Fs, ((U x : (boxS S c).Box (W1 S c)) *
      ((gy S c x.1 * gy S c (P.1 x).1) *
        (if x.1 = 0 then 1 else
          Dab S.q (yB S c (W1 S c) x.1) (yB S c (W1 S c) (P.1 x).1)))) := by
    refine Finset.prod_congr rfl fun x hx => ?_
    have hx' : x.1 < (P.1 x).1 := (Finset.mem_filter.1 hx).2
    simp only [U, dif_pos hx']
    exact (H x hx').choose_spec
  rw [e1, Finset.prod_mul_distrib, Finset.prod_mul_distrib, Units.coe_prod]
  congr 2
  · have := prod_pairs_eq_prod P (fun x : cls (cExt c) 1 => x.1) Subtype.val_injective
      (fun x => gy S c x.1)
    rw [this, prod_gy]
  · have e2 : Finset.univ.filter (fun x : cls (cExt c) 1 => x.1 ≠ 0 ∧ x.1 < (P.1 x).1) =
        Fs.filter (fun x => x.1 ≠ 0) := by
      ext x
      simp only [Fs, Finset.mem_filter, Finset.mem_univ, true_and]
      tauto
    rw [DP, e2, Finset.prod_filter (s := Fs)]
    refine Finset.prod_congr rfl fun x _ => ?_
    by_cases h : x.1 = 0 <;> simp [h]

end ColOne

end
