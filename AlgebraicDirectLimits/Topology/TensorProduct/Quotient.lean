/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicDirectLimits.Topology.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Topology.Homology
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient

/-!
# Quotients of one-sided topological tensors

`TopModuleCat.tensorQuotient` relates tensoring a topological module quotient to
quotienting the one-sided tensor by the image of the submodule tensor map. Its
underlying linear equivalence is Mathlib's `TensorProduct.tensorQuotientEquiv`.
The coefficient module is algebraic and carries no topology; the scalar ring,
coefficient module and right module have independent carrier universes.

The characteristic formulas compare the tensor of the right quotient map with
the quotient map of the tensor, both on arbitrary tensors and on pure tensors.
The inverse formulas transport quotient classes back to tensors of classes.
The existing continuous-linear-equivalence API supplies both round trips.

## Implementation notes

The submodule in the target is the algebraic range of `TensorProduct.map` applied
to the coefficient identity and the submodule inclusion. It is not a closure, and
no injectivity of the submodule tensor map is required. The quotient topologies
and module structures are the canonical ones. Neither closedness of the submodule
nor a separation condition on either quotient is required.

## References

Mathlib's algebraic tensor-quotient equivalence is due to Antoine Chambert-Loir
and Jujian Zhang; its tensor-map API is due to Kenny Lau and Mario Carneiro.
The continuous quotient-map API is due to Anatole Dedecker and Sharvil Kesarwani.
The one-sided topology and linear generator criterion follow Formal Frontier
Agents' topological tensor development and the Continuous Group Cohomology
formalization, including Beacon's original topological development. Mathlib's
topological-module category, coinduced construction and cokernel API are due to
Richard Hill and Andrew Yang. The target quotient and its projection use their
`TopModuleCat.coker` and `TopModuleCat.cokerπ` constructions. The
continuous-linear-map and equivalence APIs are due to
Jan-David Salchow, Sébastien Gouëzel, Jean Lo, Yury Kudryashov, Frédéric Dupuis
and Heather Macbeth. This module is an original Formal Frontier contribution
developed with AI assistance.
-/

@[expose] public section

open scoped TensorProduct

universe uR uC uM

namespace TopModuleCat

variable (R : Type uR) [CommRing R] [TopologicalSpace R]

/-- Tensoring a topological module quotient is continuously linearly equivalent
to quotienting the one-sided tensor by the range of the submodule tensor map.
The underlying linear equivalence is `TensorProduct.tensorQuotientEquiv C P`. -/
noncomputable def tensorQuotient (C : ModuleCat.{uC} R) (M : TopModuleCat.{uM} R)
    (P : Submodule R M) :
    let φ : TopModuleCat.Hom
        (tensorLeftObj R C (TopModuleCat.of R P)) (tensorLeftObj R C M) :=
      CategoryTheory.ConcreteCategory.ofHom
        (C := TopModuleCat.{max uC uM} R)
        (X := tensorLeftObj R C (TopModuleCat.of R P))
        (Y := tensorLeftObj R C M)
        (tensorMapCLM R (C := C) (D := C)
          (M := TopModuleCat.of R P) (N := M)
          (LinearMap.id : C →ₗ[R] C) P.subtypeL)
    tensorLeftObj R C (TopModuleCat.of R (M ⧸ P)) ≃L[R]
      TopModuleCat.coker φ where
  toLinearEquiv := TensorProduct.tensorQuotientEquiv C P
  continuous_toFun := by
    let K : Submodule R (tensorLeftObj R C M) :=
      LinearMap.range (TensorProduct.map (LinearMap.id : C →ₗ[R] C) P.subtype)
    apply (continuous_tensorLeftObj_iff_tmul R C (TopModuleCat.of R (M ⧸ P))
      (TopModuleCat.of R ((tensorLeftObj R C M) ⧸ K))
      (TensorProduct.tensorQuotientEquiv C P).toLinearMap).mpr
    intro c
    apply P.isQuotientMap_mkQL.continuous_iff.mpr
    exact (K.mkQL.comp (tensorGenerator R C M c)).continuous.congr
      (fun m ↦ (TensorProduct.tensorQuotientEquiv_apply_mk_tmul P c m).symm)
  continuous_invFun := by
    let K : Submodule R (tensorLeftObj R C M) :=
      LinearMap.range (TensorProduct.map (LinearMap.id : C →ₗ[R] C) P.subtype)
    let f := tensorMapCLM R (C := C) (D := C) (M := M)
      (N := TopModuleCat.of R (M ⧸ P)) (LinearMap.id : C →ₗ[R] C) P.mkQL
    have h : (TensorProduct.tensorQuotientEquiv C P).symm.toLinearMap.comp K.mkQ =
        f.toLinearMap := by
      apply TensorProduct.ext'
      intro c m
      exact (TensorProduct.tensorQuotientEquiv_symm_apply_tmul_mk P c m).trans
        (tensorMapCLM_tmul R (C := C) (D := C) (M := M)
          (N := TopModuleCat.of R (M ⧸ P)) (LinearMap.id : C →ₗ[R] C) P.mkQL c m).symm
    change Continuous (show ((tensorLeftObj R C M) ⧸ K) →
      tensorLeftObj R C (TopModuleCat.of R (M ⧸ P)) from
        (TensorProduct.tensorQuotientEquiv C P).symm)
    apply K.isQuotientMap_mkQL.continuous_iff.mpr
    exact f.continuous.congr (fun z ↦ (DFunLike.congr_fun h z).symm)

/-- Forgetting continuity gives Mathlib's algebraic tensor-quotient equivalence. -/
theorem tensorQuotient_toLinearEquiv (C : ModuleCat.{uC} R) (M : TopModuleCat.{uM} R)
    (P : Submodule R M) :
    (tensorQuotient R C M P).toLinearEquiv = TensorProduct.tensorQuotientEquiv C P := by
  rfl

/-- The forward equivalence carries the tensor of the quotient map to the
quotient map of the tensor on every tensor. -/
theorem tensorQuotient_tensorMapCLM (C : ModuleCat.{uC} R) (M : TopModuleCat.{uM} R)
    (P : Submodule R M) (z : tensorLeftObj R C M) :
    let φ : TopModuleCat.Hom
        (tensorLeftObj R C (TopModuleCat.of R P)) (tensorLeftObj R C M) :=
      CategoryTheory.ConcreteCategory.ofHom
        (C := TopModuleCat.{max uC uM} R)
        (X := tensorLeftObj R C (TopModuleCat.of R P))
        (Y := tensorLeftObj R C M)
        (tensorMapCLM R (C := C) (D := C)
          (M := TopModuleCat.of R P) (N := M)
          (LinearMap.id : C →ₗ[R] C) P.subtypeL)
    tensorQuotient R C M P
      (tensorMapCLM R (C := C) (D := C) (M := M)
        (N := TopModuleCat.of R (M ⧸ P)) (LinearMap.id : C →ₗ[R] C) P.mkQL z) =
      (TopModuleCat.cokerπ φ).hom z := by
  let K : Submodule R (tensorLeftObj R C M) :=
    LinearMap.range (TensorProduct.map (LinearMap.id : C →ₗ[R] C) P.subtype)
  let f := tensorMapCLM R (C := C) (D := C) (M := M)
    (N := TopModuleCat.of R (M ⧸ P)) (LinearMap.id : C →ₗ[R] C) P.mkQL
  have h : (TensorProduct.tensorQuotientEquiv C P).toLinearMap.comp f.toLinearMap =
      K.mkQ := by
    apply TensorProduct.ext'
    intro c m
    exact (congrArg (TensorProduct.tensorQuotientEquiv C P)
      (tensorMapCLM_tmul R (C := C) (D := C) (M := M)
        (N := TopModuleCat.of R (M ⧸ P)) (LinearMap.id : C →ₗ[R] C) P.mkQL c m)).trans
          (TensorProduct.tensorQuotientEquiv_apply_mk_tmul P c m)
  exact DFunLike.congr_fun h z

/-- The inverse equivalence carries every class of a tensor to its image under
the tensor of the right quotient map. -/
theorem tensorQuotient_symm_mkQ (C : ModuleCat.{uC} R) (M : TopModuleCat.{uM} R)
    (P : Submodule R M) (z : tensorLeftObj R C M) :
    let φ : TopModuleCat.Hom
        (tensorLeftObj R C (TopModuleCat.of R P)) (tensorLeftObj R C M) :=
      CategoryTheory.ConcreteCategory.ofHom
        (C := TopModuleCat.{max uC uM} R)
        (X := tensorLeftObj R C (TopModuleCat.of R P))
        (Y := tensorLeftObj R C M)
        (tensorMapCLM R (C := C) (D := C)
          (M := TopModuleCat.of R P) (N := M)
          (LinearMap.id : C →ₗ[R] C) P.subtypeL)
    (tensorQuotient R C M P).symm ((TopModuleCat.cokerπ φ).hom z) =
      tensorMapCLM R (C := C) (D := C) (M := M)
        (N := TopModuleCat.of R (M ⧸ P)) (LinearMap.id : C →ₗ[R] C) P.mkQL z := by
  apply (tensorQuotient R C M P).injective
  exact ((tensorQuotient R C M P).apply_symm_apply _).trans
    (tensorQuotient_tensorMapCLM R C M P z).symm

/-- A tensor of a quotient class maps to the quotient class of the pure tensor. -/
@[simp]
theorem tensorQuotient_tmul_mkQ (C : ModuleCat.{uC} R) (M : TopModuleCat.{uM} R)
    (P : Submodule R M) (c : C) (m : M) :
    let φ : TopModuleCat.Hom
        (tensorLeftObj R C (TopModuleCat.of R P)) (tensorLeftObj R C M) :=
      CategoryTheory.ConcreteCategory.ofHom
        (C := TopModuleCat.{max uC uM} R)
        (X := tensorLeftObj R C (TopModuleCat.of R P))
        (Y := tensorLeftObj R C M)
        (tensorMapCLM R (C := C) (D := C)
          (M := TopModuleCat.of R P) (N := M)
          (LinearMap.id : C →ₗ[R] C) P.subtypeL)
    tensorQuotient R C M P (c ⊗ₜ[R] P.mkQL m) =
      (TopModuleCat.cokerπ φ).hom (c ⊗ₜ[R] m) := by
  exact TensorProduct.tensorQuotientEquiv_apply_mk_tmul P c m

/-- The inverse equivalence maps the class of a pure tensor to the tensor of the
right-factor class. -/
@[simp]
theorem tensorQuotient_symm_mkQ_tmul (C : ModuleCat.{uC} R) (M : TopModuleCat.{uM} R)
    (P : Submodule R M) (c : C) (m : M) :
    let φ : TopModuleCat.Hom
        (tensorLeftObj R C (TopModuleCat.of R P)) (tensorLeftObj R C M) :=
      CategoryTheory.ConcreteCategory.ofHom
        (C := TopModuleCat.{max uC uM} R)
        (X := tensorLeftObj R C (TopModuleCat.of R P))
        (Y := tensorLeftObj R C M)
        (tensorMapCLM R (C := C) (D := C)
          (M := TopModuleCat.of R P) (N := M)
          (LinearMap.id : C →ₗ[R] C) P.subtypeL)
    (tensorQuotient R C M P).symm ((TopModuleCat.cokerπ φ).hom (c ⊗ₜ[R] m)) =
      c ⊗ₜ[R] P.mkQL m := by
  exact TensorProduct.tensorQuotientEquiv_symm_apply_tmul_mk P c m

end TopModuleCat
