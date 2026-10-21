/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicDirectLimits.Topology.TensorFunctor
public import AlgebraicDirectLimits.Topology.CoefficientTensor
public import Mathlib.CategoryTheory.Functor.Currying

/-!
# Tensor functor in both variables

`TopModuleCat.tensorBifunctor R` sends an algebraic coefficient module `C` to
`TopModuleCat.tensorLeftFunctor R C`. A coefficient morphism acts by the maps of
`TopModuleCat.coefficientTensor R M`, naturally in the topological right module
`M`. Thus both variables retain the canonical one-sided tensor topology and
scalar action, without a topology on the coefficients.

The characteristic API identifies the continuous map of the standard uncurried
functor with `TopModuleCat.tensorMapBilinear`, hence with Mathlib's algebraic
tensor map after forgetting continuity. Fixing the coefficient recovers
`tensorLeftFunctor`; fixing the right module by `Functor.flip` recovers
`coefficientTensor`. Product, flipped and curried presentations use Mathlib's
functor-category interfaces rather than separate tensor constructions.

The scalar and carrier universes are independent, with output in `max uC uM`.
The commutative ring needs only a supplied topology; the topological modules
supply jointly continuous actions. No finiteness, freeness, separation or
continuity of ring multiplication is required. This is functoriality, not a
faithfulness or nonzero-preservation assertion.

## References

This construction combines Formal Frontier Agents' one-variable tensor
functors and bilinear tensor-map API, including the coefficient tensor
formulation, coinduced topology and integer tensor models. It reuses
Mathlib's functor currying and flipping interfaces by Kim Morrison, Tim Baumann,
Stephen Morgan and Floris van Doorn, and the algebraic tensor-map API by Kenny
Lau and Mario Carneiro. The one-variable modules credit the underlying module
and topological-module interfaces. Mathematical and prior-formalization credit
is separate from the Apache-2.0 notice above.
-/

@[expose] public section

open CategoryTheory
open scoped TensorProduct CategoryTheory.Prod

universe uR uC uM

namespace TopModuleCat

variable (R : Type uR) [CommRing R] [TopologicalSpace R]

/-- Tensor product, covariantly in algebraic coefficients and in the topological
right module, with the one-sided tensor topology and canonical scalar action. -/
noncomputable def tensorBifunctor :
    ModuleCat.{uC} R ⥤
      (TopModuleCat.{uM} R ⥤ TopModuleCat.{max uC uM} R) where
  obj C := tensorLeftFunctor R C
  map {C D} f :=
    { app M := (coefficientTensor R M).map f
      naturality {M N} g := by
        apply ConcreteCategory.ext
        -- At the constructor boundary, the two orders of tensoring are the
        -- existing simultaneous-composition law with identities in opposite slots.
        change (tensorMapCLM R f.hom (ContinuousLinearMap.id R N)).comp
            (tensorMapCLM R (LinearMap.id : C →ₗ[R] C) g.hom) =
          (tensorMapCLM R (LinearMap.id : D →ₗ[R] D) g.hom).comp
            (tensorMapCLM R f.hom (ContinuousLinearMap.id R M))
        simp only [← tensorMapCLM_comp, LinearMap.comp_id, LinearMap.id_comp,
          ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id] }
  map_id C := by
    apply NatTrans.ext
    funext M
    exact (coefficientTensor R M).map_id C
  map_comp {C D E} f h := by
    apply NatTrans.ext
    funext M
    exact (coefficientTensor R M).map_comp f h

/-- Fixing the coefficient gives the existing additive right-variable functor. -/
@[simp]
theorem tensorBifunctor_obj (C : ModuleCat.{uC} R) :
    (tensorBifunctor R).obj C = tensorLeftFunctor R C := rfl

/-- A coefficient component is the full bilinear tensor map with right identity. -/
@[simp]
theorem tensorBifunctor_map_app_hom
    {C D : ModuleCat.{uC} R} (f : C ⟶ D) (M : TopModuleCat.{uM} R) :
    (((tensorBifunctor R).map f).app M).hom =
      tensorMapBilinear R C D M M f.hom (ContinuousLinearMap.id R M) :=
  (tensorMapBilinear_apply R f.hom (ContinuousLinearMap.id R M)).symm

/-- The standard uncurried functor acts by the simultaneous tensor map. -/
@[simp↓]
theorem tensorBifunctor_uncurry_map_hom
    {C D : ModuleCat.{uC} R} {M N : TopModuleCat.{uM} R}
    (f : C ⟶ D) (g : M ⟶ N) :
    ((Functor.uncurry.obj (tensorBifunctor R)).map (f ×ₘ g)).hom =
      tensorMapBilinear R C D M N f.hom g.hom := by
  dsimp only [Functor.uncurry, tensorBifunctor, tensorLeftFunctor, coefficientTensor]
  change (tensorMapCLM R (C := D) (D := D) (M := M) (N := N)
      (LinearMap.id : D →ₗ[R] D) g.hom).comp
    (tensorMapCLM R (C := C) (D := D) (M := M) (N := M)
      f.hom (ContinuousLinearMap.id R M)) =
    tensorMapBilinear R C D M N f.hom g.hom
  rw [tensorMapBilinear_apply]
  simpa only [LinearMap.id_comp, ContinuousLinearMap.comp_id] using
    (tensorMapCLM_comp R (C := C) (D := D) (E := D)
      (M := M) (N := M) (P := N) f.hom (LinearMap.id : D →ₗ[R] D)
      (ContinuousLinearMap.id R M) g.hom).symm

/-- On every tensor, the uncurried functor agrees with the algebraic tensor map. -/
theorem tensorBifunctor_uncurry_map_apply
    {C D : ModuleCat.{uC} R} {M N : TopModuleCat.{uM} R}
    (f : C ⟶ D) (g : M ⟶ N) (x : tensorLeftObj R C M) :
    ((Functor.uncurry.obj (tensorBifunctor R)).map (f ×ₘ g)).hom x =
      TensorProduct.map f.hom g.hom.toLinearMap x := by
  rw [tensorBifunctor_uncurry_map_hom]
  exact tensorMapBilinear_apply_apply R f.hom g.hom x

/-- The uncurried functor sends a pure tensor to the tensor of its two images. -/
@[simp↓]
theorem tensorBifunctor_uncurry_map_tmul
    {C D : ModuleCat.{uC} R} {M N : TopModuleCat.{uM} R}
    (f : C ⟶ D) (g : M ⟶ N) (c : C) (m : M) :
    ((Functor.uncurry.obj (tensorBifunctor R)).map (f ×ₘ g)).hom
      (c ⊗ₜ[R] m) = f.hom c ⊗ₜ[R] g.hom m := by
  exact (tensorBifunctor_uncurry_map_apply R f g (c ⊗ₜ[R] m)).trans
    (TensorProduct.map_tmul f.hom g.hom.toLinearMap c m)

/-- Fixing the right module by flipping gives the existing coefficient functor. -/
theorem tensorBifunctor_flip_obj (M : TopModuleCat.{uM} R) :
    ((tensorBifunctor R).flip).obj M =
      (coefficientTensor R M :
        ModuleCat.{uC} R ⥤ TopModuleCat.{max uC uM} R) := by
  conv_lhs =>
    dsimp only [Functor.flip, tensorBifunctor, tensorLeftFunctor, coefficientTensor]
  conv_rhs => dsimp only [coefficientTensor]

end TopModuleCat
