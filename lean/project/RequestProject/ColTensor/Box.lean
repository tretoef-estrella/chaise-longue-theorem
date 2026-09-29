module

public import RequestProject.ColTensor.Tensor

/-!
# Box rings: Setting and Lemma 6.4 (ii) (`q_col_tensor.md`)

This file formalizes the **Setting** (box rings) of `q_col_tensor.md` and part **(ii)** of
**Lemma 6.4** (box rings split).

Conventions: the variables `t_1, …, t_d` are indexed by `Fin d`, a finite set `W ⊆ {1, …, d}` is a
`Finset (Fin d)`, and the data `q ≥ 1`, `c ∈ F^d` are bundled in `S : BoxSetting F d`. The box
ring `B(W)` is `S.Box W`, and for `W' ⊆ W` the map `ι_{W',W}` is `S.iota W' W h` (where
`h : W' ⊆ W`).
-/

@[expose] public section

open scoped TensorProduct

namespace ColTensor

open MvPolynomial

/-- The data of the **Setting** (box rings) of `q_col_tensor.md`: an integer `q ≥ 1` and a point
`c = (c_1, …, c_d) ∈ F^d` (the variables `t_1, …, t_d` are indexed by `Fin d`). The hypothesis
`q ≥ 1` is part of the Setting and is kept, although none of the proofs of Lemma 6.4 needs it. -/
structure BoxSetting (F : Type*) [Field F] (d : ℕ) where
  /-- The exponent `q` of the relations `(t_i − c_i)^q`. -/
  q : ℕ
  /-- The hypothesis `q ≥ 1` of the Setting. -/
  one_le_q : 1 ≤ q
  /-- The point `c ∈ F^d`. -/
  c : Fin d → F

variable {F : Type*} [Field F] {d : ℕ} (S : BoxSetting F d)

namespace BoxSetting

/-- The ideal `((t_i − c_i)^q : i ∈ W)` of `F[t_i : i ∈ W]` (**Setting** of `q_col_tensor.md`). -/
noncomputable def boxIdeal (W : Finset (Fin d)) : Ideal (MvPolynomial W F) :=
  Ideal.span (Set.range fun i : W => (X i - C (S.c i)) ^ S.q)

/-- The **box ring** `B(W) := F[t_i : i ∈ W] / ((t_i − c_i)^q : i ∈ W)` of the **Setting** of
`q_col_tensor.md`, for a finite set `W ⊆ {1, …, d}`. -/
abbrev Box (W : Finset (Fin d)) : Type _ := MvPolynomial W F ⧸ S.boxIdeal W

/-- The class of the variable `t_i` in `B(W)` (**Setting** of `q_col_tensor.md`). -/
noncomputable abbrev t (W : Finset (Fin d)) (i : W) : S.Box W :=
  Ideal.Quotient.mk (S.boxIdeal W) (X i)

/-- **Setting** of `q_col_tensor.md`: the relation `(t_i − c_i)^q = 0` holds in `B(W)`. -/
theorem t_sub_pow (W : Finset (Fin d)) (i : W) :
    (S.t W i - algebraMap F (S.Box W) (S.c i)) ^ S.q = 0 := by
  have : (S.t W i - algebraMap F (S.Box W) (S.c i)) ^ S.q =
      Ideal.Quotient.mk (S.boxIdeal W) ((X i - C (S.c i)) ^ S.q) := by
    simp only [t, map_pow, map_sub]
    rfl
  rw [this, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span ⟨i, rfl⟩

/-- **Setting** of `q_col_tensor.md` (universal property of `B(W)`): an `F`-algebra map out of
`B(W)` is given by images `x_i` of the `t_i` satisfying `(x_i − c_i)^q = 0`. -/
noncomputable def boxLift {B : Type*} [CommRing B] [Algebra F B] (W : Finset (Fin d))
    (x : W → B) (hx : ∀ i, (x i - algebraMap F B (S.c i)) ^ S.q = 0) : S.Box W →ₐ[F] B :=
  Ideal.Quotient.liftₐ (S.boxIdeal W) (aeval x) (by
    intro a ha
    have hle : S.boxIdeal W ≤ RingHom.ker (aeval x : MvPolynomial W F →ₐ[F] B) := by
      rw [boxIdeal, Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      simp [RingHom.mem_ker, hx i]
    exact hle ha)

/-- **Setting** of `q_col_tensor.md`: the map out of `B(W)` given by the universal property sends
`t_i` to `x_i`. -/
@[simp] theorem boxLift_t {B : Type*} [CommRing B] [Algebra F B] (W : Finset (Fin d))
    (x : W → B) (hx : ∀ i, (x i - algebraMap F B (S.c i)) ^ S.q = 0) (i : W) :
    S.boxLift W x hx (S.t W i) = x i := by
  simp [boxLift, t]

/-- **Setting** of `q_col_tensor.md`: two `F`-algebra maps out of `B(W)` agreeing on every
`t_i` are equal. -/
theorem box_algHom_ext {B : Type*} [Semiring B] [Algebra F B] {W : Finset (Fin d)}
    {f g : S.Box W →ₐ[F] B} (h : ∀ i, f (S.t W i) = g (S.t W i)) : f = g := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  simpa using h i

/-- The map `ι_{W',W} : B(W') → B(W)` of the **Setting** of `q_col_tensor.md`, for `W' ⊆ W`:
the `F`-algebra map induced by `t_i ↦ t_i`. -/
noncomputable def iota (W' W : Finset (Fin d)) (h : W' ⊆ W) : S.Box W' →ₐ[F] S.Box W :=
  S.boxLift W' (fun i => S.t W ⟨i.1, h i.2⟩) (fun i => S.t_sub_pow W ⟨i.1, h i.2⟩)

/-- **Setting** of `q_col_tensor.md`: `ι_{W',W}(t_i) = t_i`. -/
@[simp] theorem iota_t (W' W : Finset (Fin d)) (h : W' ⊆ W) (i : W') :
    S.iota W' W h (S.t W' i) = S.t W ⟨i.1, h i.2⟩ := by
  simp [iota]

/-- **Proof of Lemma 6.4 (iv)** of `q_col_tensor.md`: `ι_{W',W} ∘ ι_{W'',W'} = ι_{W'',W}`. -/
theorem iota_iota (W'' W' W : Finset (Fin d)) (h₁ : W'' ⊆ W') (h₂ : W' ⊆ W) (x : S.Box W'') :
    S.iota W' W h₂ (S.iota W'' W' h₁ x) = S.iota W'' W (h₁.trans h₂) x := by
  have : (S.iota W' W h₂).comp (S.iota W'' W' h₁) = S.iota W'' W (h₁.trans h₂) :=
    S.box_algHom_ext fun i => by simp
  exact congrArg (fun f => f x) this

/-- The `F`-algebra map `B(W_1) ⊗ B(W_2) → B(W)`, `x ⊗ y ↦ ι_{W_1,W}(x)·ι_{W_2,W}(y)`, of
**Lemma 6.4 (ii)** of `q_col_tensor.md`. -/
noncomputable def splitMap (W₁ W₂ W : Finset (Fin d)) (h₁ : W₁ ⊆ W) (h₂ : W₂ ⊆ W) :
    S.Box W₁ ⊗[F] S.Box W₂ →ₐ[F] S.Box W :=
  Algebra.TensorProduct.lift (S.iota W₁ W h₁) (S.iota W₂ W h₂) fun _ _ => Commute.all _ _

/-- **Lemma 6.4 (ii)** of `q_col_tensor.md`: the map sends `x ⊗ y` to
`ι_{W_1,W}(x)·ι_{W_2,W}(y)`. -/
@[simp] theorem splitMap_tmul (W₁ W₂ W : Finset (Fin d)) (h₁ : W₁ ⊆ W) (h₂ : W₂ ⊆ W)
    (x : S.Box W₁) (y : S.Box W₂) :
    S.splitMap W₁ W₂ W h₁ h₂ (x ⊗ₜ y) = S.iota W₁ W h₁ x * S.iota W₂ W h₂ y := by
  simp [splitMap]

/-- **Proof of Lemma 6.4 (ii)** of `q_col_tensor.md`: the images of the generators under the
inverse map, `t_i ↦ t_i ⊗ 1` for `i ∈ W_1` and `t_i ↦ 1 ⊗ t_i` for `i ∈ W_2 ∖ W_1`. -/
noncomputable def splitGen (W₁ W₂ W : Finset (Fin d)) (hW : W = W₁ ∪ W₂) (i : W) :
    S.Box W₁ ⊗[F] S.Box W₂ :=
  if h : i.1 ∈ W₁ then Algebra.TensorProduct.includeLeft (R := F) (S := F) (S.t W₁ ⟨i.1, h⟩)
  else Algebra.TensorProduct.includeRight (R := F)
    (S.t W₂ ⟨i.1, (Finset.mem_union.1 (hW ▸ i.2 : i.1 ∈ W₁ ∪ W₂)).resolve_left h⟩)

/-- **Proof of Lemma 6.4 (ii)** of `q_col_tensor.md`: the images of the generators satisfy the
relations `(x_i − c_i)^q = 0`, so the inverse map is well defined. -/
theorem splitGen_rel (W₁ W₂ W : Finset (Fin d)) (hW : W = W₁ ∪ W₂) (i : W) :
    (S.splitGen W₁ W₂ W hW i - algebraMap F _ (S.c i)) ^ S.q = 0 := by
  unfold splitGen
  split_ifs with h
  · rw [← AlgHom.commutes (Algebra.TensorProduct.includeLeft (R := F) (S := F)), ← map_sub,
      ← map_pow, S.t_sub_pow, map_zero]
  · rw [← AlgHom.commutes (Algebra.TensorProduct.includeRight (R := F)), ← map_sub,
      ← map_pow, S.t_sub_pow, map_zero]

/-- **Proof of Lemma 6.4 (ii)** of `q_col_tensor.md`: the inverse map `B(W) → B(W_1) ⊗ B(W_2)`,
`t_i ↦ t_i ⊗ 1` for `i ∈ W_1` and `t_i ↦ 1 ⊗ t_i` for `i ∈ W_2`, where `W = W_1 ∪ W_2`. -/
noncomputable def splitInv (W₁ W₂ W : Finset (Fin d)) (hW : W = W₁ ∪ W₂) :
    S.Box W →ₐ[F] S.Box W₁ ⊗[F] S.Box W₂ :=
  S.boxLift W (S.splitGen W₁ W₂ W hW) (S.splitGen_rel W₁ W₂ W hW)

/-- **Lemma 6.4 (ii)** of `q_col_tensor.md` (box rings split): for a disjoint union
`W = W_1 ⊔ W_2`, the map `B(W_1) ⊗ B(W_2) → B(W)`, `x ⊗ y ↦ ι_{W_1,W}(x)·ι_{W_2,W}(y)`, as an
isomorphism of `F`-algebras. -/
noncomputable def splitEquiv (W₁ W₂ W : Finset (Fin d)) (hW : W = W₁ ∪ W₂)
    (hd : Disjoint W₁ W₂) : S.Box W₁ ⊗[F] S.Box W₂ ≃ₐ[F] S.Box W :=
  AlgEquiv.ofAlgHom (S.splitMap W₁ W₂ W (hW ▸ Finset.subset_union_left)
      (hW ▸ Finset.subset_union_right)) (S.splitInv W₁ W₂ W hW)
    (S.box_algHom_ext fun i => by
      by_cases h : i.1 ∈ W₁ <;> simp [splitInv, splitGen, h])
    (by
      apply Algebra.TensorProduct.ext
      · exact S.box_algHom_ext fun i => by simp [splitInv, splitGen]
      · exact S.box_algHom_ext fun i => by
          simp [splitInv, splitGen, Finset.disjoint_right.1 hd i.2])

/-- **Lemma 6.4 (ii)** of `q_col_tensor.md`: `splitEquiv` is the map
`x ⊗ y ↦ ι_{W_1,W}(x)·ι_{W_2,W}(y)`. -/
theorem splitEquiv_tmul (W₁ W₂ W : Finset (Fin d)) (hW : W = W₁ ∪ W₂) (hd : Disjoint W₁ W₂)
    (x : S.Box W₁) (y : S.Box W₂) :
    S.splitEquiv W₁ W₂ W hW hd (x ⊗ₜ y) =
      S.iota W₁ W (hW ▸ Finset.subset_union_left) x *
        S.iota W₂ W (hW ▸ Finset.subset_union_right) y := by
  simp [splitEquiv]

/-- **Lemma 6.4 (ii)** of `q_col_tensor.md` (box rings split): if `W = W_1 ⊔ W_2` (disjoint
union), the `F`-algebra map `B(W_1) ⊗ B(W_2) → B(W)`, `x ⊗ y ↦ ι_{W_1,W}(x)·ι_{W_2,W}(y)`, is
an isomorphism (bijective). -/
theorem lemma64_ii (W₁ W₂ W : Finset (Fin d)) (hW : W = W₁ ∪ W₂) (hd : Disjoint W₁ W₂) :
    Function.Bijective (S.splitMap W₁ W₂ W (hW ▸ Finset.subset_union_left)
      (hW ▸ Finset.subset_union_right)) :=
  (S.splitEquiv W₁ W₂ W hW hd).bijective

end BoxSetting

end ColTensor
