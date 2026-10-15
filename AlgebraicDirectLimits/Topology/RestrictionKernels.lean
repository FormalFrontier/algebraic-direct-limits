/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicDirectLimits.Topology.Restriction
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Additivity and kernels under continuous restriction of scalars

The same-topology functor `TopModuleCat.restrictScalars φ hφ` is additive and
preserves the kernel of every morphism. The scalar rings may be noncommutative,
and their universes are independent of one another and of the carrier universe.
Only the supplied topologies and continuity of the unital ring homomorphism are
required; neither ring needs a topological-ring instance.

The independently leveled continuous-linear interface has zero and addition
characteristics. Categorical zero preservation then follows from additivity.
For kernels, forgetting to `TopCat` commutes with restriction and preserves
limits. Reflection of isomorphisms by that forgetful functor gives reflection
of the parallel-pair limit. This proves the universal property for every
`R`-module cone apex, without requiring it to carry an `S`-action.

The consumer API is Mathlib's `kernelComparison f E` and `PreservesKernel.iso E f`,
where `E = TopModuleCat.restrictScalars φ hφ`. In particular the forward
comparison has characteristic
`kernelComparison f E ≫ kernel.ι (E.map f) = E.map (kernel.ι f)`.
No alternative kernel or comparison is constructed here.

## References

The scalar construction is the one in `AlgebraicDirectLimits.Topology.Restriction`.
The zero/add characteristics follow the continuous-linear restriction API of
Sébastien Gouëzel and Yury Kudryashov in Mathlib. Additivity and its derived
zero-preservation instance use Adam Topaz and Kim Morrison's
`CategoryTheory.Preadditive.AdditiveFunctor`. The proof of kernel preservation
uses Richard Hill and Andrew Yang's topological-module limits and forgetful
functor in `Algebra.Category.ModuleCat.Topology.Basic`, together with the
preservation/reflection framework of Kim Morrison, Reid Barton, Bhavik Mehta and
Jakob von Raumer in `CategoryTheory.Limits.Preserves.Basic`. The comparison and
its inclusion, lift and naturality laws are Kim Morrison's Mathlib kernel API.
-/

@[expose] public section

universe uR uS uM uN

open CategoryTheory CategoryTheory.Limits

namespace TopModuleCat

variable {R : Type uR} {S : Type uS} [Ring R] [Ring S]
variable [TopologicalSpace R] [TopologicalSpace S]
variable (φ : R →+* S) (hφ : Continuous φ)

/-- Restriction of continuous linear maps preserves zero at the canonical
restricted scalar views, with independent source and target carrier universes. -/
@[simp]
theorem restrictScalarsCLM_zero (M : TopModuleCat.{uM} S) (N : TopModuleCat.{uN} S) :
    restrictScalarsCLM φ hφ (0 : M →L[S] N) =
      (0 : restrictScalarsObj φ hφ M →L[R] restrictScalarsObj φ hφ N) := by
  ext x
  rfl

/-- Restriction of continuous linear maps preserves addition at the canonical
restricted scalar views, with independent source and target carrier universes. -/
@[simp]
theorem restrictScalarsCLM_add {M : TopModuleCat.{uM} S} {N : TopModuleCat.{uN} S}
    (f g : M →L[S] N) :
    restrictScalarsCLM φ hφ (f + g) =
      restrictScalarsCLM φ hφ f + restrictScalarsCLM φ hφ g := by
  ext x
  rfl

/-- Continuous same-topology restriction of scalars is additive.
Zero preservation is supplied by Mathlib's instance for additive functors. -/
instance restrictScalars_additive :
    Functor.Additive
      (restrictScalars φ hφ : TopModuleCat.{uM} S ⥤ TopModuleCat.{uM} R) where
  map_add {M N f g} := by
    ext x
    rfl

/-- Continuous same-topology restriction preserves the kernel of every morphism.
The proof uses Mathlib's topological forgetful functor and reflection of limits,
so it applies to cones with arbitrary `R`-module apexes and arrows. -/
instance restrictScalars_preservesKernel {M N : TopModuleCat.{uM} S} (f : M ⟶ N) :
    PreservesLimit (parallelPair f 0)
      (restrictScalars φ hφ : TopModuleCat.{uM} S ⥤ TopModuleCat.{uM} R) := by
  -- The parallel-pair shape lives in universe zero, independently of the rings.
  let : PreservesLimitsOfSize.{0, 0}
      (forget₂ (TopModuleCat.{uM} R) TopCat.{uM}) :=
    preservesSmallestLimits_of_preservesLimits _
  let : PreservesLimitsOfSize.{0, 0}
      (forget₂ (TopModuleCat.{uM} S) TopCat.{uM}) :=
    preservesSmallestLimits_of_preservesLimits _
  let : PreservesLimit (parallelPair f 0)
      ((restrictScalars φ hφ : TopModuleCat.{uM} S ⥤ TopModuleCat.{uM} R) ⋙
        forget₂ (TopModuleCat.{uM} R) TopCat.{uM}) := by
    rw [restrictScalars_comp_forgetTopCat]
    infer_instance
  let : ReflectsLimit ((parallelPair f 0) ⋙ restrictScalars φ hφ)
      (forget₂ (TopModuleCat.{uM} R) TopCat.{uM}) :=
    reflectsLimit_of_reflectsIsomorphisms _ _
  exact preservesLimit_of_reflects_of_preserves (restrictScalars φ hφ)
    (forget₂ (TopModuleCat.{uM} R) TopCat.{uM})

end TopModuleCat
