module

public import RequestProject.Lifts.Main
public import RequestProject.BipOpt.Main

/-!
# The layer ring inside the big ring (`q_bip_P3.md`, Setting and Step 1 of the Proof)

Formalization of the paragraph **"The layer ring inside the big ring"** of the **Setting** of
`q_bip_P3.md`: peeling `w := x_1` identifies `R_{α,β} = R_{α−1,β}[w]/(w^q)`, the variable `x_i`
of `R_{α−1,β}` being `x_{i+1}` of `R_{α,β}` and `z_l` being `z_l`.  This is the identification
built into the slices `W_j` of Lemma 7.1 (`Bip.Wslice`): the peeling isomorphism
`Peel.peelEquiv` of `q_peeling_lemma.md` (box exponent `(q + 1) − 1 = q`) followed by the renaming
`Bip.castC`.

Contents:
* `peelR`: the identification `R_{α,β} ≅ C_{α+β−1}[w]/(w^q)`, and `constR`: the inclusion of the
  constants `R_{α−1,β} → C_{α+β−1}` (the inverse renaming);
* `liftR`: the ring map `R_{α−1,β} → R_{α,β}` reading an element of the layer ring inside the big
  ring, with `liftR x_i = x_{i+1}` (`liftR_x`) and `liftR z_l = z_l` (`liftR_z`), and
  `peelR (liftR g) = constR g` (`peelR_liftR`); `peelR x_1 = w` (`peelR_x0`);
* the reduction of **Step 1** of the Proof: if `f ∈ V` and `peelR f` is represented by a
  polynomial of degree `≤ d` whose coefficient of `w^d` is `constR g`, then `g ∈ W_d(V)`
  (`mem_Wslice_of_coeff`).
-/

@[expose] public section

open MvPolynomial

namespace BipP3

open Bip ChainLemma Tight

set_option synthInstance.maxHeartbeats 200000

variable {F : Type*} [Field F] {q : ℕ}

/-- The peeling isomorphism of `q_peeling_lemma.md` sends the variable `y_1` to the root
(**Setting** of `q_bip_P3.md`, "`w := x_1`"), for any `m ≥ 1`. -/
lemma peelEquiv_X_zero {q' m : ℕ} (hm : 1 ≤ m) (k : Fin m) (hk : (k : ℕ) = 0) :
    Peel.peelEquiv F q' m hm (Ideal.Quotient.mk _ (X k)) = AdjoinRoot.root _ := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  obtain rfl : k = 0 := Fin.ext hk
  exact Lifts.phi_y0

/-- The peeling isomorphism of `q_peeling_lemma.md` sends the variable `y_{j+2}` to the constant
`y_{j+1}` of `C_{m−1}` (**Setting** of `q_bip_P3.md`, "the variables of `R_{α−1,β}` are
renamed"), for any `m ≥ 1`. -/
lemma peelEquiv_X_succ {q' m : ℕ} (hm : 1 ≤ m) (k : Fin m) (j : ℕ) (hk : (k : ℕ) = j + 1) :
    Peel.peelEquiv F q' m hm (Ideal.Quotient.mk _ (X k)) =
      AdjoinRoot.of _ (Ideal.Quotient.mk _ (X ⟨j, by omega⟩)) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have hj : j < n := by omega
  obtain rfl : k = Fin.succ ⟨j, hj⟩ := Fin.ext (by simp [hk])
  show Peel.peelEquiv' F q' n (Tight.y F q' _) = _
  rw [← Lifts.incl_y, Lifts.phi_incl]
  rfl

/-- The renaming `castC` of `q_bip_setting.md` sends a variable to the variable with the same
index (used for the identification in the **Setting** of `q_bip_P3.md`). -/
lemma castC_X {m n : ℕ} (h : m = n) (k : Fin m) :
    castC F q h (Ideal.Quotient.mk _ (X k)) = Ideal.Quotient.mk _ (X (Fin.cast h k)) := by
  subst h; rfl

/-- The inverse of the renaming `castC` is the renaming in the other direction (used for the identification in the **Setting** of `q_bip_P3.md`). -/
lemma castC_symm {m n : ℕ} (h : m = n) : (castC F q h).symm = castC F q h.symm := by
  subst h; rfl

/-- **Setting** of `q_bip_P3.md`, "The layer ring inside the big ring": the identification
`R_{α,β} = C_{α+β−1}[w]/(w^q)` obtained by peeling `w := x_1` (the peeling isomorphism of
`q_peeling_lemma.md` with `q + 1` in place of `q`, as in `Bip.Wslice`). -/
noncomputable def peelR (α β : ℕ) (hα : 1 ≤ α) :
    R F q α β ≃ₐ[F] Peel.Peeled (q + 1) (Peel.C F (q + 1) (α + β - 1)) :=
  Peel.peelEquiv F (q + 1) (α + β) (by omega)

/-- **Setting** of `q_bip_P3.md`, "The layer ring inside the big ring": the constants
`R_{α−1,β} → C_{α+β−1}` of the peeled ring, i.e. the inverse of the renaming `castC` used by
`Bip.Wslice`. -/
noncomputable def constR (α β : ℕ) (hα : 1 ≤ α) :
    R F q (α - 1) β →+* Peel.C F (q + 1) (α + β - 1) :=
  (castC F q (show α + β - 1 = α - 1 + β by omega)).symm.toRingEquiv.toRingHom

/-- **Setting** of `q_bip_P3.md`, "The layer ring inside the big ring": the ring map
`R_{α−1,β} → R_{α,β}` reading an element of the layer ring inside the big ring (the constants of
`R_{α−1,β}[w]/(w^q) = R_{α,β}`). -/
noncomputable def liftR (α β : ℕ) (hα : 1 ≤ α) : R F q (α - 1) β →+* R F q α β :=
  (peelR (F := F) (q := q) α β hα).symm.toRingEquiv.toRingHom.comp
    ((AdjoinRoot.of _).comp (constR α β hα))

/-- **Setting** of `q_bip_P3.md`: under the identification, `liftR g` is the constant `g`. -/
lemma peelR_liftR {α β : ℕ} (hα : 1 ≤ α) (g : R F q (α - 1) β) :
    peelR α β hα (liftR α β hα g) = AdjoinRoot.of _ (constR α β hα g) :=
  (peelR α β hα).toRingEquiv.apply_symm_apply _

/-- **Setting** of `q_bip_P3.md`: `w = x_1` is the root of `R_{α−1,β}[w]/(w^q)`. -/
lemma peelR_x0 {α β : ℕ} (hα : 1 ≤ α) :
    peelR (F := F) (q := q) α β hα (x F q ⟨0, hα⟩) = AdjoinRoot.root _ :=
  peelEquiv_X_zero _ _ rfl

/-- The index shift `[α − 1] → {2, …, α}`, `i ↦ i + 1` (**Setting** of `q_bip_P3.md`: the
variable `x_i` of `R_{α−1,β}` is the variable `x_{i+1}` of `R_{α,β}`). -/
def sh {α : ℕ} : Fin (α - 1) ↪ Fin α :=
  ⟨fun i => ⟨i + 1, by omega⟩, fun i j h => Fin.ext (by simpa using congrArg Fin.val h)⟩

/-- The index shift `i ↦ i + 1` of the **Setting** of `q_bip_P3.md` is strictly increasing (so Vandermondes are preserved). -/
lemma sh_strictMono {α : ℕ} : StrictMono (sh (α := α)) := fun i j h => by
  change (i : ℕ) + 1 < (j : ℕ) + 1; exact Nat.succ_lt_succ h

/-- **Setting** of `q_bip_P3.md`: the index `1` (encoded `⟨0, _⟩`) is not a shifted index, i.e. a lifted tight pattern "does not involve the index `1`". -/
lemma sh_ne_zero {α : ℕ} (hα : 1 ≤ α) (i : Fin (α - 1)) : sh i ≠ ⟨0, hα⟩ := by
  intro h; have := congrArg Fin.val h; simp [sh] at this

/-- Cases (α), (β) of the Proof of Proposition 7.5 in `q_bip_P3.md`: "`1 < s` for every `s ∈ S`" — the index `1` is smaller than every shifted index. -/
lemma zero_lt_sh {α : ℕ} (hα : 1 ≤ α) (i : Fin (α - 1)) : (⟨0, hα⟩ : Fin α) < sh i := by
  change 0 < (i : ℕ) + 1; omega

/-- **Setting** of `q_bip_P3.md`: the variable `x_i` of `R_{α−1,β}` is the variable `x_{i+1}` of
`R_{α,β}`. -/
lemma liftR_x {α β : ℕ} (hα : 1 ≤ α) (i : Fin (α - 1)) :
    liftR (F := F) (q := q) α β hα (x F q i) = x F q (sh i) := by
  apply (peelR (F := F) (q := q) α β hα).injective
  rw [peelR_liftR]
  simp only [peelR, x, constR, castC_symm]
  rw [peelEquiv_X_succ _ _ i (by simp [sh])]
  simp only [RingEquiv.toRingHom_eq_coe, AlgEquiv.toRingEquiv_eq_coe, RingHom.coe_coe,
    AlgEquiv.coe_ringEquiv, castC_X]
  rfl

/-- **Setting** of `q_bip_P3.md`: the variable `z_l` of `R_{α−1,β}` is the variable `z_l` of
`R_{α,β}`. -/
lemma liftR_z {α β : ℕ} (hα : 1 ≤ α) (l : Fin β) :
    liftR (F := F) (q := q) α β hα (z F q l) = z F q l := by
  apply (peelR (F := F) (q := q) α β hα).injective
  rw [peelR_liftR]
  simp only [peelR, z, constR, castC_symm]
  rw [peelEquiv_X_succ _ _ (α - 1 + l) (by simp; omega)]
  simp only [RingEquiv.toRingHom_eq_coe, AlgEquiv.toRingEquiv_eq_coe, RingHom.coe_coe,
    AlgEquiv.coe_ringEquiv, castC_X]
  congr 3

/-- **Step 1** of the Proof of Proposition 7.5 in `q_bip_P3.md`: if `f ∈ V` and, under the
identification `R_{α,β} = R_{α−1,β}[w]/(w^q)`, `f` is represented by a polynomial `P` whose
coefficients vanish above `d ≤ q − 1` (so `deg_w f ≤ d`) and whose coefficient of `w^d` is
(the constant) `g ∈ R_{α−1,β}`, then `g ∈ W_d(V)`. -/
theorem mem_Wslice_of_coeff (hq : 1 ≤ q) {α β : ℕ} (hα : 1 ≤ α) (V : Ideal (R F q α β)) {f : R F q α β}
    (hf : f ∈ V) (P : Polynomial (Peel.C F (q + 1) (α + β - 1)))
    (hP : peelR α β hα f = AdjoinRoot.mk _ P) {d : ℕ} (hd : d ≤ q - 1)
    (hdeg : ∀ k, d < k → P.coeff k = 0) (g : R F q (α - 1) β)
    (hg : P.coeff d = constR α β hα g) : g ∈ Wslice F q hα V d := by
  have key : ∀ {m : ℕ} (hm : 1 ≤ m) (V : Ideal (Peel.C F (q + 1) m)) (f : Peel.C F (q + 1) m),
      f ∈ V → ∀ P : Polynomial (Peel.C F (q + 1) (m - 1)),
      Peel.peelEquiv F (q + 1) m hm f = AdjoinRoot.mk _ P → (∀ k, d < k → P.coeff k = 0) →
      P.coeff d ∈ Peel.W hm V d := by
    intro m hm V f hf P hP hdeg
    obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
    exact Lifts.coeff_mem_W (q := q + 1) (n := n) (by omega) V hf P hP (show d ≤ q + 1 - 2 by omega) hdeg
  have hmem := key (m := α + β) (by omega) V f hf P hP hdeg
  rw [hg] at hmem
  exact ⟨_, hmem, (castC F q (show α + β - 1 = α - 1 + β by omega)).toRingEquiv.apply_symm_apply g⟩

end BipP3

end
