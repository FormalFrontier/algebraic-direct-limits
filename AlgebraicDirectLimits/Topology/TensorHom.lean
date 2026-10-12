/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicDirectLimits.Topology.TensorProduct

/-!
# Continuous bilinear maps out of the one-sided tensor

For an algebraic coefficient module `C` and topological modules `M` and `N`,
`TopModuleCat.tensorLiftCLM` extends a linear family `C →ₗ[R] (M →L[R] N)` to a
continuous linear map from `TopModuleCat.tensorLeftObj R C M`. Its underlying
linear map is Mathlib's `TensorProduct.lift`, after forgetting continuity in the
right argument. `TopModuleCat.tensorCurry` restricts an outgoing map to the
continuous fixed-coefficient generators.

`TopModuleCat.tensorHomLinearEquiv` packages these constructions, oriented from
outgoing continuous linear maps to linear families of continuous linear maps.
The characteristic statements include pure-tensor evaluation, agreement with
Mathlib's algebraic universal property, uniqueness, and composition coherence.

## Implementation notes

Only the existing one-sided coinduced module topology is used. The continuity
criterion applies to linear maps, not arbitrary functions. Neither `C` nor a Hom
space is given a topology, and the ring and three module universes are independent.

## References

The algebraic universal property is Mathlib's `LinearAlgebra.TensorProduct.Basic`,
by Kenny Lau and Mario Carneiro. The continuous linear map API is due to Jan-David
Salchow, Sébastien Gouëzel, Jean Lo, Yury Kudryashov, Frédéric Dupuis and Heather
Macbeth. This module follows the coinduced linear continuity and one-sided tensor
constructions in `AlgebraicDirectLimits.Topology.Coinduced` and
`AlgebraicDirectLimits.Topology.TensorProduct`, by Formal Frontier Agents, which
in turn follow Mathlib's topological-module development by Richard Hill and Andrew
Yang and Beacon's original topological development for continuous group cohomology.
-/

@[expose] public section

open scoped TensorProduct

universe uR uC uD uM uN uP

namespace TopModuleCat

variable (R : Type uR) [CommRing R] [TopologicalSpace R]
variable {C : ModuleCat.{uC} R} {M : TopModuleCat.{uM} R} {N : TopModuleCat.{uN} R}

/-- Extend a linear family of continuous linear maps by Mathlib's algebraic tensor lift. -/
noncomputable def tensorLiftCLM (b : C →ₗ[R] (M →L[R] N)) :
    tensorLeftObj R C M →L[R] N where
  toLinearMap := TensorProduct.lift ((ContinuousLinearMap.coeLM R).comp b)
  cont := by
    -- Each fixed-coefficient restriction is the given continuous linear map `b c`.
    apply (continuous_tensorLeftObj_iff_tmul R C M N
      (show tensorLeftObj R C M →ₗ[R] N from
        TensorProduct.lift ((ContinuousLinearMap.coeLM R).comp b))).mpr
    intro c
    exact (b c).continuous.congr
      (fun m ↦ (TensorProduct.lift.tmul
        (f' := (ContinuousLinearMap.coeLM R).comp b) c m).symm)

/-- Forgetting continuity gives exactly Mathlib's tensor lift of the linearized family. -/
@[simp]
theorem tensorLiftCLM_toLinearMap (b : C →ₗ[R] (M →L[R] N)) :
    (tensorLiftCLM R b).toLinearMap =
      TensorProduct.lift ((ContinuousLinearMap.coeLM R).comp b) := by
  rfl

/-- The continuous tensor lift evaluates a pure tensor by the given bilinear family. -/
@[simp]
theorem tensorLiftCLM_tmul (b : C →ₗ[R] (M →L[R] N)) (c : C) (m : M) :
    tensorLiftCLM R b (c ⊗ₜ[R] m) = b c m := by
  calc
    tensorLiftCLM R b (c ⊗ₜ[R] m) =
        TensorProduct.lift ((ContinuousLinearMap.coeLM R).comp b) (c ⊗ₜ[R] m) :=
      DFunLike.congr_fun (tensorLiftCLM_toLinearMap R b) _
    _ = b c m :=
      TensorProduct.lift.tmul (f' := (ContinuousLinearMap.coeLM R).comp b) c m

/-- The continuous tensor lift evaluates a fixed-coefficient generator by its family. -/
@[simp]
theorem tensorLiftCLM_tensorGenerator_apply (b : C →ₗ[R] (M →L[R] N))
    (c : C) (m : M) :
    tensorLiftCLM R b (tensorGenerator R C M c m) = b c m := by
  rw [tensorGenerator_apply, tensorLiftCLM_tmul]

/-- Restriction of the tensor lift to a generator is the given continuous linear map. -/
@[simp]
theorem tensorLiftCLM_comp_tensorGenerator (b : C →ₗ[R] (M →L[R] N)) (c : C) :
    (tensorLiftCLM R b).comp (tensorGenerator R C M c) = b c := by
  apply ContinuousLinearMap.ext
  intro m
  exact tensorLiftCLM_tensorGenerator_apply R b c m

/-- Curry an outgoing continuous linear map by composing with each tensor generator. -/
noncomputable def tensorCurry (f : tensorLeftObj R C M →L[R] N) :
    C →ₗ[R] (M →L[R] N) where
  toFun c := f.comp (tensorGenerator R C M c)
  map_add' := by
    intro c d
    apply ContinuousLinearMap.ext
    intro m
    simp only [ContinuousLinearMap.comp_apply, tensorGenerator_apply,
      TensorProduct.add_tmul, add_apply]
    exact f.map_add (show tensorLeftObj R C M from c ⊗ₜ[R] m)
      (show tensorLeftObj R C M from d ⊗ₜ[R] m)
  map_smul' := by
    intro r c
    apply ContinuousLinearMap.ext
    intro m
    simp only [ContinuousLinearMap.comp_apply, tensorGenerator_apply,
      ← TensorProduct.smul_tmul', smul_apply, RingHom.id_apply]
    exact f.map_smul r (show tensorLeftObj R C M from c ⊗ₜ[R] m)

/-- At a coefficient, currying is composition with the continuous tensor generator. -/
@[simp]
theorem tensorCurry_apply (f : tensorLeftObj R C M →L[R] N) (c : C) :
    tensorCurry R f c = f.comp (tensorGenerator R C M c) := by
  rfl

/-- The value of a curried map is its value on the corresponding pure tensor. -/
@[simp]
theorem tensorCurry_apply_apply (f : tensorLeftObj R C M →L[R] N) (c : C) (m : M) :
    tensorCurry R f c m = f (c ⊗ₜ[R] m) := by
  simp only [tensorCurry_apply, ContinuousLinearMap.comp_apply, tensorGenerator_apply]

/-- Linearizing the continuous family agrees with Mathlib's algebraic curry equivalence. -/
theorem tensorCurry_toLinearMap (f : tensorLeftObj R C M →L[R] N) :
    (ContinuousLinearMap.coeLM R).comp (tensorCurry R f) =
      (TensorProduct.lift.equiv (RingHom.id R) C M N).symm f.toLinearMap := by
  apply LinearMap.ext
  intro c
  apply LinearMap.ext
  intro m
  calc
    _ = f (c ⊗ₜ[R] m) := tensorCurry_apply_apply R f c m
    _ = _ := (TensorProduct.lift.equiv_symm_apply
      (σ₁₂ := RingHom.id R) (M := C) (N := M) (P₂ := N) f.toLinearMap c m).symm

/-- The underlying tensor lift is also the forward map of Mathlib's lift equivalence. -/
theorem tensorLiftCLM_toLinearMap_eq_liftEquiv (b : C →ₗ[R] (M →L[R] N)) :
    (tensorLiftCLM R b).toLinearMap =
      TensorProduct.lift.equiv (RingHom.id R) C M N
        ((ContinuousLinearMap.coeLM R).comp b) := by
  rfl

/-- Lifting the curried family recovers the outgoing continuous linear map. -/
@[simp]
theorem tensorLiftCLM_tensorCurry (f : tensorLeftObj R C M →L[R] N) :
    tensorLiftCLM R (tensorCurry R f) = f := by
  apply tensorLeft_ext R
  intro c m
  rw [tensorLiftCLM_tmul, tensorCurry_apply_apply]

/-- Currying the lifted family recovers the original family. -/
@[simp]
theorem tensorCurry_tensorLiftCLM (b : C →ₗ[R] (M →L[R] N)) :
    tensorCurry R (tensorLiftCLM R b) = b := by
  apply LinearMap.ext
  intro c
  apply ContinuousLinearMap.ext
  intro m
  rw [tensorCurry_apply_apply, tensorLiftCLM_tmul]

/-- The continuous bilinear universal property of the existing one-sided tensor topology. -/
noncomputable def tensorHomLinearEquiv (C : ModuleCat.{uC} R)
    (M : TopModuleCat.{uM} R) (N : TopModuleCat.{uN} R) :
    (tensorLeftObj R C M →L[R] N) ≃ₗ[R] (C →ₗ[R] (M →L[R] N)) where
  toFun := tensorCurry R
  invFun := tensorLiftCLM R
  left_inv := by
    exact tensorLiftCLM_tensorCurry R
  right_inv := by
    exact tensorCurry_tensorLiftCLM R
  map_add' := by
    intro f g
    apply LinearMap.ext
    intro c
    apply ContinuousLinearMap.ext
    intro m
    simpa only [tensorCurry_apply, ContinuousLinearMap.comp_apply,
      LinearMap.add_apply, add_apply] using
      (add_apply f g (tensorGenerator R C M c m))
  map_smul' := by
    intro r f
    apply LinearMap.ext
    intro c
    apply ContinuousLinearMap.ext
    intro m
    simpa only [tensorCurry_apply, ContinuousLinearMap.comp_apply,
      LinearMap.smul_apply, smul_apply, RingHom.id_apply] using
      (smul_apply f r (tensorGenerator R C M c m))

/-- The forward Hom equivalence is the curried family. -/
@[simp]
theorem tensorHomLinearEquiv_apply (f : tensorLeftObj R C M →L[R] N) :
    tensorHomLinearEquiv R C M N f = tensorCurry R f := by
  rfl

/-- The inverse Hom equivalence is the continuous tensor lift. -/
@[simp]
theorem tensorHomLinearEquiv_symm_apply (b : C →ₗ[R] (M →L[R] N)) :
    (tensorHomLinearEquiv R C M N).symm b = tensorLiftCLM R b := by
  rfl

/-- Evaluation of the forward Hom equivalence on a coefficient and module vector. -/
@[simp]
theorem tensorHomLinearEquiv_apply_apply (f : tensorLeftObj R C M →L[R] N)
    (c : C) (m : M) :
    tensorHomLinearEquiv R C M N f c m = f (c ⊗ₜ[R] m) := by
  rw [tensorHomLinearEquiv_apply, tensorCurry_apply_apply]

/-- Evaluation of the inverse Hom equivalence on a pure tensor. -/
@[simp]
theorem tensorHomLinearEquiv_symm_apply_tmul (b : C →ₗ[R] (M →L[R] N))
    (c : C) (m : M) :
    (tensorHomLinearEquiv R C M N).symm b (c ⊗ₜ[R] m) = b c m := by
  rw [tensorHomLinearEquiv_symm_apply, tensorLiftCLM_tmul]

/-- Equality on all bundled tensor generators determines an outgoing map. -/
theorem tensorLeft_ext_tensorGenerator {f g : tensorLeftObj R C M →L[R] N}
    (h : ∀ c : C, f.comp (tensorGenerator R C M c) =
      g.comp (tensorGenerator R C M c)) : f = g := by
  apply tensorLeft_ext R
  intro c m
  simpa only [ContinuousLinearMap.comp_apply, tensorGenerator_apply] using
    DFunLike.congr_fun (h c) m

/-- The continuous tensor lift is uniquely determined by its pure-tensor values. -/
theorem tensorLiftCLM_unique (b : C →ₗ[R] (M →L[R] N))
    (f : tensorLeftObj R C M →L[R] N)
    (h : ∀ c m, f (c ⊗ₜ[R] m) = b c m) : f = tensorLiftCLM R b := by
  apply tensorLeft_ext R
  intro c m
  exact (h c m).trans (tensorLiftCLM_tmul R b c m).symm

/-- Agreement with the family on all bundled generators characterizes the tensor lift. -/
theorem tensorLiftCLM_unique_of_comp_tensorGenerator (b : C →ₗ[R] (M →L[R] N))
    (f : tensorLeftObj R C M →L[R] N)
    (h : ∀ c : C, f.comp (tensorGenerator R C M c) = b c) :
    f = tensorLiftCLM R b := by
  apply tensorLeft_ext_tensorGenerator R
  intro c
  exact (h c).trans (tensorLiftCLM_comp_tensorGenerator R b c).symm

/-- Every linear family has exactly one outgoing map with its pure-tensor values. -/
theorem existsUnique_tensorLiftCLM (b : C →ₗ[R] (M →L[R] N)) :
    ∃! f : tensorLeftObj R C M →L[R] N, ∀ c m, f (c ⊗ₜ[R] m) = b c m :=
  ⟨tensorLiftCLM R b, tensorLiftCLM_tmul R b,
    fun f hf ↦ tensorLiftCLM_unique R b f hf⟩

section Composition

variable {D : ModuleCat.{uD} R} {P : TopModuleCat.{uP} R}

/-- Postcomposition commutes with lifting the bilinear family. -/
theorem tensorLiftCLM_comp (b : C →ₗ[R] (M →L[R] N)) (g : N →L[R] P) :
    tensorLiftCLM R (((ContinuousLinearMap.llcomp R M N P).flip g).comp b) =
      g.comp (tensorLiftCLM R b) := by
  apply tensorLeft_ext R
  intro c m
  calc
    _ = g (b c m) := tensorLiftCLM_tmul R _ c m
    _ = _ := congrArg g (tensorLiftCLM_tmul R b c m).symm

/-- Currying a composite with the two-factor tensor map restricts both arguments. -/
theorem tensorCurry_comp_tensorMapCLM (f : tensorLeftObj R C M →L[R] N)
    (a : D →ₗ[R] C) (g : P →L[R] M) :
    tensorCurry R (f.comp (tensorMapCLM R a g)) =
      (ContinuousLinearMap.lcomp N g).comp ((tensorCurry R f).comp a) := by
  apply LinearMap.ext
  intro d
  apply ContinuousLinearMap.ext
  intro p
  calc
    _ = f (a d ⊗ₜ[R] g p) := by
      rw [tensorCurry_apply_apply]
      exact (ContinuousLinearMap.comp_apply f (tensorMapCLM R a g)
        (show tensorLeftObj R D P from d ⊗ₜ[R] p)).trans
          (congrArg f (tensorMapCLM_tmul R a g d p))
    _ = _ := (tensorCurry_apply_apply R f (a d) (g p)).symm

end Composition

end TopModuleCat
