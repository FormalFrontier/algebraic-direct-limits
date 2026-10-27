/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicDirectLimits.Topology.TensorProduct

/-!
# Evaluation of tensor maps

A linear map on the left factor and a continuous linear map on the right factor
send a pure tensor to the tensor of its images. Tensor generators give the same
evaluation, whether the generator is evaluated before or after applying the map.
-/

public section

namespace TopModuleCat

open scoped TensorProduct

example (R : Type*) [CommRing R] [TopologicalSpace R]
    {C : ModuleCat R} {D : ModuleCat R} {M : TopModuleCat R} {N : TopModuleCat R}
    (f : C →ₗ[R] D) (g : M →L[R] N) (c : C) (m : M) :
    tensorMapCLM R f g (c ⊗ₜ[R] m) = f c ⊗ₜ[R] g m := by
  simp

example (R : Type*) [CommRing R] [TopologicalSpace R]
    {C : ModuleCat R} {D : ModuleCat R} {M : TopModuleCat R} {N : TopModuleCat R}
    (f : C →ₗ[R] D) (g : M →L[R] N) (c : C) (m : M) :
    tensorMapCLM R f g (c ⊗ₜ[R] m) = f c ⊗ₜ[R] g m := by
  rw [TopModuleCat.tensorMapCLM_tmul]

example (R : Type*) [CommRing R] [TopologicalSpace R]
    {C : ModuleCat R} {D : ModuleCat R} {M : TopModuleCat R} {N : TopModuleCat R}
    (f : C →ₗ[R] D) (g : M →L[R] N) (c : C) (m : M) :
    tensorMapCLM R f g (c ⊗ₜ[R] m) = f c ⊗ₜ[R] g m := by
  exact @TopModuleCat.tensorMapCLM_tmul R _ _ C D M N f g c m

example (R : Type*) [CommRing R] [TopologicalSpace R]
    {C : ModuleCat R} {D : ModuleCat R} {M : TopModuleCat R} {N : TopModuleCat R}
    (f : C →ₗ[R] D) (g : M →L[R] N) (c : C) (m : M) :
    tensorMapCLM R f g (tensorGenerator R C M c m) =
      tensorGenerator R D N (f c) (g m) := by
  simp

example (R : Type*) [CommRing R] [TopologicalSpace R]
    {C : ModuleCat R} {D : ModuleCat R} {M : TopModuleCat R} {N : TopModuleCat R}
    (f : C →ₗ[R] D) (g : M →L[R] N) (c : C) (m : M) :
    tensorMapCLM R f g (tensorGenerator R C M c m) =
      tensorGenerator R D N (f c) (g m) := by
  rw [TopModuleCat.tensorMapCLM_tensorGenerator_apply]

example (R : Type*) [CommRing R] [TopologicalSpace R]
    {C : ModuleCat R} {D : ModuleCat R} {M : TopModuleCat R} {N : TopModuleCat R}
    (f : C →ₗ[R] D) (g : M →L[R] N) (c : C) (m : M) :
    tensorMapCLM R f g (tensorGenerator R C M c m) =
      tensorGenerator R D N (f c) (g m) := by
  exact @TopModuleCat.tensorMapCLM_tensorGenerator_apply R _ _ C D M N f g c m

example (R : Type*) [CommRing R] [TopologicalSpace R]
    {C : ModuleCat R} {D : ModuleCat R} {M : TopModuleCat R} {N : TopModuleCat R}
    (f : C →ₗ[R] D) (g : M →L[R] N) (c : C) (m : M) :
    tensorMapCLM R f g (tensorGenerator R C M c m) =
      tensorMapCLM R f g (c ⊗ₜ[R] m) := by
  exact
    (@TopModuleCat.tensorMapCLM_tensorGenerator_apply R _ _ C D M N f g c m).trans (by
      rw [tensorGenerator_apply]
      exact (@TopModuleCat.tensorMapCLM_tmul R _ _ C D M N f g c m).symm)

end TopModuleCat
