/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicDirectLimits.Topology.TensorProduct

/-!
# Bilinear tensor maps on pure tensors

The bilinear operator sends a pure tensor to the tensor of the two images.
Its evaluation agrees with the continuous-linear tensor map at the same pure tensor.
-/

public section

namespace TopModuleCat

open scoped TensorProduct

example (R : Type*) [CommRing R] [TopologicalSpace R]
    {C : ModuleCat R} {D : ModuleCat R} {M : TopModuleCat R} {N : TopModuleCat R}
    (f : C →ₗ[R] D) (g : M →L[R] N) (c : C) (m : M) :
    tensorMapBilinear R C D M N f g (c ⊗ₜ[R] m) = f c ⊗ₜ[R] g m := by
  simp

example (R : Type*) [CommRing R] [TopologicalSpace R]
    {C : ModuleCat R} {D : ModuleCat R} {M : TopModuleCat R} {N : TopModuleCat R}
    (f : C →ₗ[R] D) (g : M →L[R] N) (c : C) (m : M) :
    tensorMapBilinear R C D M N f g (c ⊗ₜ[R] m) = f c ⊗ₜ[R] g m := by
  rw [TopModuleCat.tensorMapBilinear_tmul]

example (R : Type*) [CommRing R] [TopologicalSpace R]
    {C : ModuleCat R} {D : ModuleCat R} {M : TopModuleCat R} {N : TopModuleCat R}
    (f : C →ₗ[R] D) (g : M →L[R] N) (c : C) (m : M) :
    tensorMapBilinear R C D M N f g (c ⊗ₜ[R] m) = f c ⊗ₜ[R] g m := by
  exact @TopModuleCat.tensorMapBilinear_tmul R _ _ C D M N f g c m

example (R : Type*) [CommRing R] [TopologicalSpace R]
    {C : ModuleCat R} {D : ModuleCat R} {M : TopModuleCat R} {N : TopModuleCat R}
    (f : C →ₗ[R] D) (g : M →L[R] N) (c : C) (m : M) :
    tensorMapBilinear R C D M N f g (c ⊗ₜ[R] m) =
      tensorMapCLM R f g (c ⊗ₜ[R] m) := by
  exact
    (@TopModuleCat.tensorMapBilinear_tmul R _ _ C D M N f g c m).trans
      (@TopModuleCat.tensorMapCLM_tmul R _ _ C D M N f g c m).symm

end TopModuleCat
