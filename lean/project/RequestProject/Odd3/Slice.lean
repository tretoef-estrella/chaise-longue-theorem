module

public import RequestProject.Odd3.Pairs

/-!
# Slices of ideals of `C_m` and the shapes of `I(m, J)` (`q_odd3.md`)

Auxiliary facts used in the proof of part (ii) of the Theorem of `q_odd3.md`:
* the four cases of the definition of `I(m, J)`, and the remark of the Setting that the formulas
  of the second and third lines also give the unit ideal for `J = m` and `J = m + 1`;
* "an element of `V` of degree `≤ j` in `y_1` puts its coefficient of `y_1^j` in `W_j(V)`", in
  the form: for a polynomial `Q = Σ_i Q_i y_1^i` with coefficients `Q_i ∈ C_{m−1}` and degree
  `≤ j ≤ 2`, if (the image of) `Q` lies in `V` then `Q_j ∈ W_j(V)`;
* "an element of `V` that does not contain `y_1` lies in `W_0 ⊆ W_1 ⊆ W_2`";
* "since `W_j` is an ideal, it is enough to find the generators of the smaller ideal in `W_j`".
-/

@[expose] public section

namespace Odd3

open Peel Tight Polynomial

set_option synthInstance.maxHeartbeats 200000

variable {F : Type*} [Field F]

/-- Setting of `q_odd3.md`, first line of the definition of `I(m, J)`. -/
lemma I_top {m J : ℕ} (h : m ≤ J) : I F m J = ⊤ := by
  rw [I, if_pos h]

/-- Setting of `q_odd3.md`, second line of the definition of `I(m, J)`. -/
lemma I_even {m J : ℕ} (h : J < m) (hp : J % 2 = m % 2) :
    I F m J = Ideal.span (evenGens F m J) := by
  rw [I, if_neg (by omega), if_pos hp]

/-- Setting of `q_odd3.md`, third line of the definition of `I(m, J)`. -/
lemma I_odd {m J : ℕ} (h1 : 1 ≤ J) (h : J < m) (hp : J % 2 ≠ m % 2) :
    I F m J = Ideal.span (oddGens F m J) := by
  rw [I, if_neg (by omega), if_neg hp, if_pos h1]

/-- Setting of `q_odd3.md`, fourth line of the definition of `I(m, J)`. -/
lemma I_zero {m : ℕ} (hm : m % 2 = 1) : I F m 0 = Ideal.span (zeroGens F m) := by
  rw [I, if_neg (by omega), if_neg (by omega), if_neg (by omega)]

/-- Setting of `q_odd3.md`, the remark after the definition: for `J = m` the second line gives
`(D_∅) = C_m`, so the second line is valid for all `J ≤ m` with `J ≡ m (mod 2)`. -/
lemma I_even' {m J : ℕ} (h : J ≤ m) (hp : J % 2 = m % 2) :
    I F m J = Ideal.span (evenGens F m J) := by
  rcases lt_or_eq_of_le h with h | rfl
  · exact I_even h hp
  · rw [I_top le_rfl, eq_comm, Ideal.eq_top_iff_one]
    exact Ideal.subset_span ⟨∅, isPairs_empty, by simp, by simp⟩

/-- Setting of `q_odd3.md`, the remark after the definition: for `J = m + 1` the third line gives
`(D_∅) = C_m`, so the third line is valid for all `1 ≤ J ≤ m + 1` with `J ≢ m (mod 2)`. -/
lemma I_odd' {m J : ℕ} (h1 : 1 ≤ J) (h : J ≤ m + 1) (hp : J % 2 ≠ m % 2) :
    I F m J = Ideal.span (oddGens F m J) := by
  rcases lt_or_ge J m with h' | h'
  · exact I_odd h1 h' hp
  · rw [I_top h', eq_comm, Ideal.eq_top_iff_one]
    exact Ideal.subset_span (Or.inr ⟨∅, isPairs_empty, by simp; omega, by simp⟩)

/-- Proof of part (ii) of `q_odd3.md` (auxiliary): the slice `W_j(V) ⊆ C_{m−1}` for `m = n + 1`,
regarded as a subspace of `C_n` (`C_{(n+1)−1}` is definitionally `C_n`). -/
noncomputable def Ws {n : ℕ} (V : Ideal (C F 4 (n + 1))) (j : ℕ) : Submodule F (C F 4 n) :=
  W (m := n + 1) (Nat.succ_pos n) V j

/-- Proof of part (ii) of `q_odd3.md` (auxiliary): the identification
`C_m = C_{m−1}[y_1]/(y_1^3)` sends the class of `Q` back to `Q(y_1)`. -/
lemma peelEquiv'_bwd (n : ℕ) (z : Peeled 4 (C F 4 n)) :
    peelEquiv' F 4 n (peelBwdₐ F 4 n z) = z :=
  (peelEquiv' F 4 n).apply_symm_apply z

/-- Proof of part (ii) of `q_odd3.md` (auxiliary): the element of `C_m` given by a polynomial
`Q ∈ C_{m−1}[y_1]` is `Q` evaluated at `y_1`. -/
lemma bwd_mk (n : ℕ) (Q : (C F 4 n)[X]) :
    peelBwdₐ F 4 n (AdjoinRoot.mk _ Q) = Q.eval₂ (incl F 4 n) (y F 4 0) := by
  show peelBwd F 4 n (AdjoinRoot.mk _ Q) = _
  rw [peelBwd, AdjoinRoot.lift_mk]; rfl

/-- Proof of part (ii) of `q_odd3.md`: "an element of `I(m, J)` of degree `≤ j` in `y_1` puts its
coefficient of `y_1^j` in `W_j`".  Here the element is `Q(y_1) = Σ_i Q_i y_1^i` for a polynomial
`Q` with coefficients in `C_{m−1}` (in the variables `y_2, …, y_m`) of degree `≤ j ≤ 2`. -/
lemma coeff_mem_W {n : ℕ} (V : Ideal (C F 4 (n + 1))) (j : ℕ) (hj : j ≤ 2) (Q : (C F 4 n)[X])
    (hQ : Q.degree ≤ j) (hV : Q.eval₂ (incl F 4 n) (y F 4 0) ∈ V) :
    Q.coeff j ∈ Ws V j := by
  haveI : Nontrivial (C F 4 n) := nontrivial_C (by norm_num)
  have hexp : expand (m := n + 1) (by omega) (Q.eval₂ (incl F 4 n) (y F 4 0)) = Q := by
    rw [expand_apply, ← bwd_mk]
    show expandGen F 4 (C F 4 n) (peelEquiv' F 4 n _) = Q
    rw [peelEquiv'_bwd, expandGen]
    simp only [LinearMap.coe_restrictScalars, AdjoinRoot.modByMonicHom_mk]
    rw [modByMonic_eq_self_iff (monic_X_pow_q 4 _)]
    rw [degree_X_pow]
    exact lt_of_le_of_lt hQ (by norm_cast; omega)
  refine (mem_W _ V j _).2 ⟨_, (mem_Vle _ V j _).2 ⟨hV, fun k hk => ?_⟩, ?_⟩
  · rw [hexp]; exact coeff_eq_zero_of_degree_lt (lt_of_le_of_lt hQ (by exact_mod_cast hk))
  · rw [coeffY1_apply, hexp]

/-- Proof of part (ii) of `q_odd3.md`: "an element of `I(m, J)` that does not contain `y_1` lies in
`W_0 ⊆ W_1 ⊆ W_2`". -/
lemma mem_W_of_incl {n : ℕ} (V : Ideal (C F 4 (n + 1))) (j : ℕ) (hj : j ≤ 2) (g : C F 4 n)
    (hg : incl F 4 n g ∈ V) : g ∈ Ws V j := by
  have h0 : g ∈ Ws V 0 := by
    have := coeff_mem_W V 0 (by norm_num) (Polynomial.C g) (by simpa using degree_C_le) (by simpa using hg)
    simpa using this
  have h1 : g ∈ Ws V 1 := W_mono (q := 4) (by norm_num) (m := n + 1) (by omega) V 0 (by norm_num) h0
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact W_mono (q := 4) (by norm_num) (m := n + 1) (by omega) V 1 (by norm_num) h1

/-- Proof of part (ii) of `q_odd3.md`: "since `W_j` is an ideal (part (i) of the peeling lemma),
it is enough to find the generators of the smaller ideal in `W_j`". -/
lemma span_subset_W {n : ℕ} (V : Ideal (C F 4 (n + 1))) (j : ℕ) (hj : j ≤ 2) (S : Set (C F 4 n))
    (hS : S ⊆ Ws V j) :
    (Ideal.span S : Set (C F 4 n)) ⊆ Ws V j := by
  obtain ⟨K, hK⟩ : ∃ K : Ideal (C F 4 n), (K : Set (C F 4 n)) = Ws V j :=
    W_isIdeal (q := 4) (by norm_num) (m := n + 1) (by omega) V j (by omega)
  have : Ideal.span S ≤ K := Ideal.span_le.2 (fun x hx => by rw [hK]; exact hS hx)
  intro x hx
  rw [← hK]; exact this hx

/-- Proof of part (ii) of `q_odd3.md`: "if the smaller ideal is the unit ideal, it is enough to
find `1` in `W_j`". -/
lemma top_subset_W {n : ℕ} (V : Ideal (C F 4 (n + 1))) (j : ℕ) (hj : j ≤ 2)
    (h1 : (1 : C F 4 n) ∈ Ws V j) :
    ((⊤ : Ideal (C F 4 n)) : Set (C F 4 n)) ⊆ Ws V j := by
  rw [← Ideal.span_singleton_one]
  exact span_subset_W V j hj _ (by simpa using h1)

/-- Proof of part (ii) of `q_odd3.md` (auxiliary): every slice of the unit ideal is everything
(`y_1^j ∈ C_m` has `y_1^j`-coefficient `1`). -/
lemma top_subset_W_top {n : ℕ} (j : ℕ) (hj : j ≤ 2) (S : Set (C F 4 n)) :
    S ⊆ Ws (⊤ : Ideal (C F 4 (n + 1))) j := by
  haveI : Nontrivial (C F 4 n) := nontrivial_C (by norm_num)
  refine fun x _ => top_subset_W _ j hj ?_ (Set.mem_univ x)
  have := coeff_mem_W (⊤ : Ideal (C F 4 (n + 1))) j hj (Polynomial.X ^ j)
    (by rw [degree_X_pow]) Submodule.mem_top
  simpa using this

end Odd3

end
