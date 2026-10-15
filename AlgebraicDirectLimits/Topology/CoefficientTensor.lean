/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Topology.Basic
public import AlgebraicDirectLimits.Topology.TensorHom
public import Mathlib.CategoryTheory.Linear.Yoneda

/-!
# Coefficient tensor and categorical continuous Hom

For a fixed topological right module, the coefficient tensor sends an algebraic
module to its one-sided topological tensor. Its categorical Hom equivalence
sends an outgoing continuous linear map to the corresponding coefficient-indexed
family of categorical continuous linear maps. The coefficient has no topology.
The concrete Hom equivalence uses the category's stored scalar action, and the
covariant Hom functor is Mathlib's linear coyoneda functor.

## Limitations

The characteristic identities describe concrete Hom, tensor maps and currying.
The plain Hom equivalence is natural in algebraic coefficients and continuous
targets. No adjunction structure is defined here.

## References

This construction follows Wick's coefficient tensor formulation and Formal
Frontier Agents' one-sided topological tensor and continuous-Hom formalization,
including Beacon's coinduced topology work and Lantern's tensor models. It reuses
Mathlib's TopModuleCat interface by Andrew Yang and Richard Hill, the ModuleCat
interface by Robert A. Spencer and Markus Himmel, Kim Morrison's linear Yoneda
construction, and the tensor universal property by Kenny Lau and Mario Carneiro.
The continuous-linear-map formalization is credited in
`AlgebraicDirectLimits.Topology.TensorHom`; the categorical and linear-equivalence
interfaces are those of Mathlib. Mathematical and prior-formalization credit is
separate from the Apache-2.0 licensing notice above.
-/

@[expose] public section

open CategoryTheory
open scoped TensorProduct

universe uR w uC uM

namespace TopModuleCat

/-- The linear equivalence from categorical morphisms to continuous linear maps. -/
noncomputable def homLinearEquiv
    (R : Type uR) [CommRing R] [TopologicalSpace R]
    {X Y : TopModuleCat.{w} R} :
    (X ⟶ Y) ≃ₗ[R] (X →L[R] Y) where
  toFun := ConcreteCategory.hom (C := TopModuleCat.{w} R)
  invFun := ConcreteCategory.ofHom (C := TopModuleCat.{w} R)
  left_inv := ConcreteCategory.ofHom_hom
  right_inv := CategoryTheory.ConcreteCategory.hom_ofHom (C := TopModuleCat.{w} R) (X := X) (Y := Y)
  map_add' := TopModuleCat.hom_add R (M₁ := X) (M₂ := Y)
  map_smul' := fun r f => TopModuleCat.hom_smul r f

/-- Tensor algebraic coefficients with a fixed topological right module. -/
noncomputable def coefficientTensor
    (R : Type uR) [CommRing R] [TopologicalSpace R]
    (M : TopModuleCat.{uM} R) :
    ModuleCat.{uC} R ⥤ TopModuleCat.{max uC uM} R where
  obj C := tensorLeftObj R C M
  map {C D} a := CategoryTheory.ConcreteCategory.ofHom
    (C := TopModuleCat.{max uC uM} R)
    (X := tensorLeftObj R C M) (Y := tensorLeftObj R D M)
    (tensorMapCLM R a.hom (ContinuousLinearMap.id R M))
  map_id C := ConcreteCategory.ext
    ((CategoryTheory.ConcreteCategory.hom_ofHom
      (C := TopModuleCat.{max uC uM} R)
      (X := tensorLeftObj R C M) (Y := tensorLeftObj R C M)
      (tensorMapCLM R
        (ModuleCat.Hom.hom (R := R) (A := C) (B := C) (𝟙 C))
        (ContinuousLinearMap.id R M))).trans
      ((congrArg (fun l => tensorMapCLM R l (ContinuousLinearMap.id R M))
        (ModuleCat.hom_id (M := C))).trans
        ((tensorMapCLM_id R (C := C) (M := M)).trans
          (TopModuleCat.hom_id R (tensorLeftObj R C M)).symm)))
  map_comp {C D E} a b := ConcreteCategory.ext
    ((CategoryTheory.ConcreteCategory.hom_ofHom
      (C := TopModuleCat.{max uC uM} R)
      (X := tensorLeftObj R C M) (Y := tensorLeftObj R E M)
      (tensorMapCLM R (a ≫ b).hom (ContinuousLinearMap.id R M))).trans
      ((congrArg (fun l => tensorMapCLM R l (ContinuousLinearMap.id R M))
        (ModuleCat.hom_comp a b)).trans
        (((congrArg (tensorMapCLM R (b.hom.comp a.hom))
          (ContinuousLinearMap.id_comp (ContinuousLinearMap.id R M))).symm.trans
          (tensorMapCLM_comp R a.hom b.hom
            (ContinuousLinearMap.id R M) (ContinuousLinearMap.id R M))).trans
          ((congrArg₂ (fun v u => v.comp u)
            (CategoryTheory.ConcreteCategory.hom_ofHom
              (C := TopModuleCat.{max uC uM} R)
              (X := tensorLeftObj R D M) (Y := tensorLeftObj R E M)
              (tensorMapCLM R b.hom (ContinuousLinearMap.id R M))).symm
            (CategoryTheory.ConcreteCategory.hom_ofHom
              (C := TopModuleCat.{max uC uM} R)
              (X := tensorLeftObj R C M) (Y := tensorLeftObj R D M)
              (tensorMapCLM R a.hom (ContinuousLinearMap.id R M))).symm).trans
            (TopModuleCat.hom_comp R
              (CategoryTheory.ConcreteCategory.ofHom
                (C := TopModuleCat.{max uC uM} R)
                (X := tensorLeftObj R C M) (Y := tensorLeftObj R D M)
                (tensorMapCLM R a.hom (ContinuousLinearMap.id R M)))
              (CategoryTheory.ConcreteCategory.ofHom
                (C := TopModuleCat.{max uC uM} R)
                (X := tensorLeftObj R D M) (Y := tensorLeftObj R E M)
                (tensorMapCLM R b.hom (ContinuousLinearMap.id R M)))).symm))))

/-- Outgoing coefficient-tensor morphisms correspond to categorical continuous-map families. -/
noncomputable def coefficientTensorHomEquiv
    (R : Type uR) [CommRing R] [TopologicalSpace R]
    (M : TopModuleCat.{w} R) (C : ModuleCat.{w} R)
    (N : TopModuleCat.{w} R) :
    ((TopModuleCat.coefficientTensor R M).obj C ⟶ N) ≃
      (C ⟶ ((CategoryTheory.linearCoyoneda R (TopModuleCat.{w} R)).obj
        (Opposite.op M)).obj N) :=
  (CategoryTheory.ConcreteCategory.homEquiv
    (C := TopModuleCat.{w} R)
    (X := (TopModuleCat.coefficientTensor R M).obj C) (Y := N)).trans
      ((TopModuleCat.tensorHomLinearEquiv R C M N).toEquiv.trans
        ((LinearEquiv.congrRight
          (TopModuleCat.homLinearEquiv R (X := M) (Y := N)).symm).toEquiv.trans
          (ModuleCat.homLinearEquiv
            (R := R) (S := R) (M := C)
            (N := ((CategoryTheory.linearCoyoneda R (TopModuleCat.{w} R)).obj
              (Opposite.op M)).obj N)).symm.toEquiv))

variable (R : Type uR) [CommRing R] [TopologicalSpace R]

/-- The concrete continuous linear map underlying a categorical morphism. -/
theorem homLinearEquiv_apply {X Y : TopModuleCat.{w} R} (f : X ⟶ Y) :
    homLinearEquiv R f = f.hom := by
  rfl

/-- The inverse concrete-Hom equivalence bundles a continuous linear map. -/
theorem homLinearEquiv_symm_apply {X Y : TopModuleCat.{w} R} (q : X →L[R] Y) :
    (homLinearEquiv R).symm q = TopModuleCat.ofHom q := by
  rfl

/-- The coefficient tensor has the one-sided topological tensor as its object. -/
theorem coefficientTensor_obj (M : TopModuleCat.{w} R) {C : ModuleCat.{w} R} :
    (coefficientTensor R M).obj C = tensorLeftObj R C M := by
  rfl

/-- A coefficient morphism acts by its tensor map with the right-factor identity. -/
theorem coefficientTensor_map_hom (M : TopModuleCat.{w} R)
    {C D : ModuleCat.{w} R} (a : C ⟶ D) :
    ((coefficientTensor R M).map a).hom =
      tensorMapCLM R a.hom (ContinuousLinearMap.id R M) := by
  rfl

/-- A coefficient morphism acts on the coefficient of every pure tensor. -/
theorem coefficientTensor_map_tmul (M : TopModuleCat.{w} R)
    {C D : ModuleCat.{w} R} (a : C ⟶ D) (c : C) (m : M) :
    ((coefficientTensor R M).map a).hom (c ⊗ₜ[R] m) = a.hom c ⊗ₜ[R] m := by
  exact tensorMapCLM_tmul R a.hom (ContinuousLinearMap.id R M) c m

/-- Coefficient tensor maps preserve addition of coefficient morphisms. -/
theorem coefficientTensor_map_add (M : TopModuleCat.{w} R)
    {C D : ModuleCat.{w} R} (a a' : C ⟶ D) :
    (coefficientTensor R M).map (a + a') =
      (coefficientTensor R M).map a + (coefficientTensor R M).map a' := by
  apply ConcreteCategory.ext
  exact tensorMapCLM_add_left R a.hom a'.hom (ContinuousLinearMap.id R M)

/-- Coefficient tensor maps preserve scalar multiplication of morphisms. -/
theorem coefficientTensor_map_smul (M : TopModuleCat.{w} R)
    {C D : ModuleCat.{w} R} (r : R) (a : C ⟶ D) :
    (coefficientTensor R M).map (r • a) = r • (coefficientTensor R M).map a := by
  apply ConcreteCategory.ext
  exact tensorMapCLM_smul_left R r a.hom (ContinuousLinearMap.id R M)

/-- The categorical Hom equivalence curries the underlying continuous linear map. -/
theorem coefficientTensorHomEquiv_apply (M : TopModuleCat.{w} R)
    {C : ModuleCat.{w} R} {N : TopModuleCat.{w} R}
    (f : (coefficientTensor R M).obj C ⟶ N) :
    coefficientTensorHomEquiv R M C N f =
      ModuleCat.ofHom ((homLinearEquiv R (X := M) (Y := N)).symm.toLinearMap.comp
        (tensorCurry R f.hom)) := by
  apply ConcreteCategory.ext
  apply LinearMap.ext
  intro c
  rfl

/-- The inverse categorical Hom equivalence lifts the continuous-map family. -/
theorem coefficientTensorHomEquiv_symm_apply (M : TopModuleCat.{w} R)
    {C : ModuleCat.{w} R} {N : TopModuleCat.{w} R}
    (b : C ⟶ ((CategoryTheory.linearCoyoneda R (TopModuleCat.{w} R)).obj
      (Opposite.op M)).obj N) :
    (coefficientTensorHomEquiv R M C N).symm b =
      TopModuleCat.ofHom (tensorLiftCLM R
        ((homLinearEquiv R (X := M) (Y := N)).toLinearMap.comp b.hom)) := by
  apply ConcreteCategory.ext
  exact congrArg (tensorLiftCLM R) (LinearMap.ext (fun c => rfl))

/-- Evaluation of the curried categorical family is evaluation on a pure tensor. -/
theorem coefficientTensorHomEquiv_apply_apply (M : TopModuleCat.{w} R)
    {C : ModuleCat.{w} R} {N : TopModuleCat.{w} R}
    (f : (coefficientTensor R M).obj C ⟶ N) (c : C) (m : M) :
    ((coefficientTensorHomEquiv R M C N f).hom c).hom m =
      f.hom (c ⊗ₜ[R] m) := by
  rw [coefficientTensorHomEquiv_apply]
  exact tensorCurry_apply_apply R f.hom c m

/-- The inverse categorical Hom equivalence evaluates pure tensors by its family. -/
theorem coefficientTensorHomEquiv_symm_apply_tmul (M : TopModuleCat.{w} R)
    {C : ModuleCat.{w} R} {N : TopModuleCat.{w} R}
    (b : C ⟶ ((CategoryTheory.linearCoyoneda R (TopModuleCat.{w} R)).obj
      (Opposite.op M)).obj N) (c : C) (m : M) :
    ((coefficientTensorHomEquiv R M C N).symm b).hom (c ⊗ₜ[R] m) =
      (b.hom c).hom m := by
  rw [coefficientTensorHomEquiv_symm_apply]
  exact tensorLiftCLM_tmul R
    ((homLinearEquiv R (X := M) (Y := N)).toLinearMap.comp b.hom) c m

/-- Currying commutes with precomposition by a coefficient morphism. -/
theorem coefficientTensorHomEquiv_naturality_left
    (R : Type uR) [CommRing R] [TopologicalSpace R]
    (M : TopModuleCat.{w} R) {C D : ModuleCat.{w} R}
    {N : TopModuleCat.{w} R} (u : D ⟶ C)
    (f : (TopModuleCat.coefficientTensor R M).obj C ⟶ N) :
    TopModuleCat.coefficientTensorHomEquiv R M D N
        ((TopModuleCat.coefficientTensor R M).map u ≫ f) =
      u ≫ TopModuleCat.coefficientTensorHomEquiv R M C N f := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  apply ConcreteCategory.ext
  apply ContinuousLinearMap.ext
  intro m
  change
    ((coefficientTensorHomEquiv R M D N
      ((coefficientTensor R M).map u ≫ f)).hom c).hom m =
    ((coefficientTensorHomEquiv R M C N f).hom (u.hom c)).hom m
  calc
    _ = ((coefficientTensor R M).map u ≫ f).hom (c ⊗ₜ[R] m) :=
      coefficientTensorHomEquiv_apply_apply R M _ c m
    _ = f.hom (((coefficientTensor R M).map u).hom (c ⊗ₜ[R] m)) :=
      CategoryTheory.comp_apply (C := TopModuleCat.{w} R)
        (X := (coefficientTensor R M).obj D)
        (Y := (coefficientTensor R M).obj C) (Z := N)
        ((coefficientTensor R M).map u) f (c ⊗ₜ[R] m)
    _ = f.hom (u.hom c ⊗ₜ[R] m) :=
      congrArg f.hom (coefficientTensor_map_tmul R M u c m)
    _ = _ := (coefficientTensorHomEquiv_apply_apply R M f (u.hom c) m).symm

/-- Currying commutes with postcomposition in the continuous target module. -/
theorem coefficientTensorHomEquiv_naturality_right
    (R : Type uR) [CommRing R] [TopologicalSpace R]
    (M : TopModuleCat.{w} R) {C : ModuleCat.{w} R}
    {N N' : TopModuleCat.{w} R}
    (f : (TopModuleCat.coefficientTensor R M).obj C ⟶ N)
    (v : N ⟶ N') :
    TopModuleCat.coefficientTensorHomEquiv R M C N' (f ≫ v) =
      TopModuleCat.coefficientTensorHomEquiv R M C N f ≫
        ((CategoryTheory.linearCoyoneda R (TopModuleCat.{w} R)).obj
          (Opposite.op M)).map v := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  apply ConcreteCategory.ext
  apply ContinuousLinearMap.ext
  intro m
  change
    ((coefficientTensorHomEquiv R M C N' (f ≫ v)).hom c).hom m =
    (((coefficientTensorHomEquiv R M C N f).hom c) ≫ v).hom m
  calc
    _ = (f ≫ v).hom (c ⊗ₜ[R] m) :=
      coefficientTensorHomEquiv_apply_apply R M _ c m
    _ = v.hom (f.hom (c ⊗ₜ[R] m)) :=
      CategoryTheory.comp_apply (C := TopModuleCat.{w} R)
        (X := (coefficientTensor R M).obj C) (Y := N) (Z := N')
        f v (c ⊗ₜ[R] m)
    _ = v.hom (((coefficientTensorHomEquiv R M C N f).hom c).hom m) :=
      congrArg v.hom (coefficientTensorHomEquiv_apply_apply R M f c m).symm
    _ = _ :=
      (CategoryTheory.comp_apply (C := TopModuleCat.{w} R)
        (X := M) (Y := N) (Z := N')
        ((coefficientTensorHomEquiv R M C N f).hom c) v m).symm

end TopModuleCat
