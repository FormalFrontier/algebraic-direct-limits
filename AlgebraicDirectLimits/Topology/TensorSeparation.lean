/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicDirectLimits.Topology.TensorProduct
public import Mathlib.Topology.Separation.Hausdorff

/-!
# Hausdorffness of finite-basis one-sided tensors

The Hausdorff preservation statements concern the existing
`TopModuleCat.tensorLeftObj`: its left factor is an algebraic module and only
its right factor carries a topology. The first statement takes a basis with a
finite index type. The finite-free specialization uses Mathlib's `Module.Free`
and `Module.Finite` classes, without exposing a chosen basis to the caller.
The scalar ring is any commutative ring with a supplied topology; joint scalar
continuity is part of the right-factor bundle. All carrier and index universes
are independent.

## Limitations

These are forward Hausdorff preservation results, not Hausdorffness reflection
or a preservation theorem for arbitrary projective coefficients. Empty bases and
trivial scalar rings are allowed.
No compactness result, completed tensor product, coefficient topology or global
Hausdorffness instance is introduced.

## References

The finite-coordinate construction is the existing one in
`AlgebraicDirectLimits.Topology.TensorProduct`, by Formal Frontier Agents,
following the earlier coinduced-module and Continuous Group Cohomology
one-sided topology development, including Beacon's original development.
Mathlib's tensor-basis API is due to Jakob von Raumer, and its finite-free
chosen-basis API to Riccardo Brasca. The Hausdorff and product separation APIs
are due to Johannes Hölzl and Mario Carneiro. The continuous-linear-equivalence
API is due to Jan-David Salchow, Sébastien Gouëzel, Jean Lo, Yury Kudryashov,
Frédéric Dupuis and Heather Macbeth; the homeomorphism API is due to Johannes
Hölzl, Patrick Massot, Sébastien Gouëzel, Zhouhang Zhou and Reid Barton.
-/

@[expose] public section

universe uR uC uM uι

namespace TopModuleCat

variable (R : Type uR) [CommRing R] [TopologicalSpace R]
variable (C : ModuleCat.{uC} R) (M : TopModuleCat.{uM} R)

/-- A finite coefficient basis preserves Hausdorffness of the right factor in
the one-sided tensor product. -/
theorem t2Space_tensorLeftObj_of_basis {ι : Type uι} [Finite ι]
    (b : Module.Basis ι R C) [T2Space M] : T2Space (tensorLeftObj R C M) := by
  exact (tensorCoordinateContinuousLinearEquiv R C M b).toHomeomorph.symm.t2Space

/-- Tensoring a Hausdorff topological module on the left with a finite free
algebraic coefficient module preserves Hausdorffness. -/
theorem t2Space_tensorLeftObj [Module.Free R C] [Module.Finite R C] [T2Space M] :
    T2Space (tensorLeftObj R C M) := by
  exact t2Space_tensorLeftObj_of_basis R C M (Module.Free.chooseBasis R C)

end TopModuleCat
