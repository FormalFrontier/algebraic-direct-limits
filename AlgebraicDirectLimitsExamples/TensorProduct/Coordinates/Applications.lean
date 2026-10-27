/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicDirectLimits.Topology.TensorProduct

/-!
# Evaluation of tensor coordinates

The characteristic laws for tensor coordinates evaluate a pure tensor or a tensor generator
as a basis coefficient acting on the right factor. These examples use the existing laws by
simplification, rewriting and direct application, then compare the continuous coordinates
of the two tensor presentations and the algebraic and continuous coordinates of a generator.
-/

public section

open scoped TensorProduct

namespace TopModuleCat

-- Algebraic coordinates of a tensor generator.
example (R : Type*) [CommRing R] [TopologicalSpace R]
    (C : ModuleCat R) (M : TopModuleCat R) {ι : Type*} [Finite ι]
    (b : Module.Basis ι R C) (c : C) (m : M) (i : ι) :
    tensorCoordinateLinearEquiv R C M b (tensorGenerator R C M c m) i = b.repr c i • m := by
  simp

example (R : Type*) [CommRing R] [TopologicalSpace R]
    (C : ModuleCat R) (M : TopModuleCat R) {ι : Type*} [Finite ι]
    (b : Module.Basis ι R C) (c : C) (m : M) (i : ι) :
    tensorCoordinateLinearEquiv R C M b (tensorGenerator R C M c m) i = b.repr c i • m := by
  rw [tensorCoordinateLinearEquiv_tensorGenerator_apply]

example (R : Type*) [CommRing R] [TopologicalSpace R]
    (C : ModuleCat R) (M : TopModuleCat R) {ι : Type*} [Finite ι]
    (b : Module.Basis ι R C) (c : C) (m : M) (i : ι) :
    tensorCoordinateLinearEquiv R C M b (tensorGenerator R C M c m) i = b.repr c i • m := by
  exact @tensorCoordinateLinearEquiv_tensorGenerator_apply R _ _ C M ι _ b c m i

-- Continuous coordinates of a pure tensor.
example (R : Type*) [CommRing R] [TopologicalSpace R]
    (C : ModuleCat R) (M : TopModuleCat R) {ι : Type*} [Finite ι]
    (b : Module.Basis ι R C) (c : C) (m : M) (i : ι) :
    tensorCoordinateContinuousLinearEquiv R C M b (c ⊗ₜ[R] m) i =
      b.repr c i • m := by
  simp

example (R : Type*) [CommRing R] [TopologicalSpace R]
    (C : ModuleCat R) (M : TopModuleCat R) {ι : Type*} [Finite ι]
    (b : Module.Basis ι R C) (c : C) (m : M) (i : ι) :
    tensorCoordinateContinuousLinearEquiv R C M b (c ⊗ₜ[R] m) i =
      b.repr c i • m := by
  rw [tensorCoordinateContinuousLinearEquiv_tmul_apply]

example (R : Type*) [CommRing R] [TopologicalSpace R]
    (C : ModuleCat R) (M : TopModuleCat R) {ι : Type*} [Finite ι]
    (b : Module.Basis ι R C) (c : C) (m : M) (i : ι) :
    tensorCoordinateContinuousLinearEquiv R C M b (c ⊗ₜ[R] m) i =
      b.repr c i • m := by
  exact @tensorCoordinateContinuousLinearEquiv_tmul_apply R _ _ C M ι _ b c m i

-- Continuous coordinates of a tensor generator.
example (R : Type*) [CommRing R] [TopologicalSpace R]
    (C : ModuleCat R) (M : TopModuleCat R) {ι : Type*} [Finite ι]
    (b : Module.Basis ι R C) (c : C) (m : M) (i : ι) :
    tensorCoordinateContinuousLinearEquiv R C M b
      (tensorGenerator R C M c m) i = b.repr c i • m := by
  simp

example (R : Type*) [CommRing R] [TopologicalSpace R]
    (C : ModuleCat R) (M : TopModuleCat R) {ι : Type*} [Finite ι]
    (b : Module.Basis ι R C) (c : C) (m : M) (i : ι) :
    tensorCoordinateContinuousLinearEquiv R C M b
      (tensorGenerator R C M c m) i = b.repr c i • m := by
  rw [tensorCoordinateContinuousLinearEquiv_tensorGenerator_apply]

example (R : Type*) [CommRing R] [TopologicalSpace R]
    (C : ModuleCat R) (M : TopModuleCat R) {ι : Type*} [Finite ι]
    (b : Module.Basis ι R C) (c : C) (m : M) (i : ι) :
    tensorCoordinateContinuousLinearEquiv R C M b
      (tensorGenerator R C M c m) i = b.repr c i • m := by
  exact @tensorCoordinateContinuousLinearEquiv_tensorGenerator_apply R _ _ C M ι _ b c m i

-- A generator and its pure-tensor presentation have the same continuous coordinates.
example (R : Type*) [CommRing R] [TopologicalSpace R]
    (C : ModuleCat R) (M : TopModuleCat R) {ι : Type*} [Finite ι]
    (b : Module.Basis ι R C) (c : C) (m : M) (i : ι) :
    tensorCoordinateContinuousLinearEquiv R C M b (tensorGenerator R C M c m) i =
      tensorCoordinateContinuousLinearEquiv R C M b (c ⊗ₜ[R] m) i := by
  exact Eq.trans
    (@tensorCoordinateContinuousLinearEquiv_tensorGenerator_apply R _ _ C M ι _ b c m i)
    (@tensorCoordinateContinuousLinearEquiv_tmul_apply R _ _ C M ι _ b c m i).symm

-- Algebraic and continuous coordinates agree pointwise on a tensor generator.
example (R : Type*) [CommRing R] [TopologicalSpace R]
    (C : ModuleCat R) (M : TopModuleCat R) {ι : Type*} [Finite ι]
    (b : Module.Basis ι R C) (c : C) (m : M) (i : ι) :
    tensorCoordinateContinuousLinearEquiv R C M b (tensorGenerator R C M c m) i =
      tensorCoordinateLinearEquiv R C M b (tensorGenerator R C M c m) i := by
  exact Eq.trans
    (@tensorCoordinateContinuousLinearEquiv_tensorGenerator_apply R _ _ C M ι _ b c m i)
    (@tensorCoordinateLinearEquiv_tensorGenerator_apply R _ _ C M ι _ b c m i).symm

end TopModuleCat
