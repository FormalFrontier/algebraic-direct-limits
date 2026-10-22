/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicDirectLimits.Topology.TensorProduct
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.Topology.Instances.AddCircle.Real

/-!
# Rational coefficients and the real circle

The coefficient module is the algebraic integer module `ℚ`. The right factor is
`AddCircle (1 : ℝ)` with its usual quotient topology and canonical integer action.
The coefficient is flat by localization, and the circle is compact and Hausdorff.

`rationalCircleTensor` specializes the one-sided tensor topology to these factors.
Its continuous integer-linear generator at coefficient `1` sends a circle point
`m` to `1 ⊗ₜ[ℤ] m`. The element `irrationalGenerator` records the value of this map
at the class of `Real.sqrt 2` through its pure-tensor formula.

## References

* Formal Frontier Agents, *Rational coefficients do not preserve tensor
  Hausdorffness*, for the rational-circle model and generator at coefficient `1`.
* Mathlib's `RingTheory.Localization.FractionRing` and `RingTheory.Flat.Localization`,
  by Kenny Lau, Mario Carneiro, Johan Commelin, Amelia Livingston, Anne Baanen and
  Junyan Xu, for rational localization and flatness.
* Mathlib's `Topology.Instances.AddCircle.Real`, by Oliver Nash, and
  `Topology.Instances.ZMultiples`, by Johannes Hölzl and Mario Carneiro, for the
  circle with its quotient topology, compactness and separation.
* `TopModuleCat.tensorLeftObj` and `TopModuleCat.tensorGenerator`, by Formal
  Frontier Agents, following the topological-module constructions of Richard Hill
  and Andrew Yang in Mathlib.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

namespace TensorCircleExamples

/-- The rational numbers as an algebraic integer module. -/
abbrev rationalCoefficients : ModuleCat ℤ :=
  ModuleCat.of ℤ ℚ

/-- The rational coefficient module is flat over the integers, since it is the
localization at `nonZeroDivisors ℤ`. -/
theorem rationalCoefficients_flat : Module.Flat ℤ rationalCoefficients := by
  let _ : IsLocalization (nonZeroDivisors ℤ) ℚ := Rat.isFractionRing
  exact IsLocalization.flat ℚ (nonZeroDivisors ℤ)

/-- The real circle modulo integer periods, with its usual quotient topology
and canonical jointly continuous integer action. -/
abbrev circleModule : TopModuleCat ℤ :=
  TopModuleCat.of ℤ (AddCircle (1 : ℝ))

/-- Bundling the circle retains its quotient topology. -/
theorem circleModule_topologicalSpace :
    circleModule.topologicalSpace =
      (inferInstance : TopologicalSpace (AddCircle (1 : ℝ))) := rfl

/-- The canonical integer action on the circle is jointly continuous. -/
theorem circleModule_continuousSMul : ContinuousSMul ℤ circleModule :=
  AddGroup.continuousSMul_int

/-- The real circle is Hausdorff in its quotient topology. -/
theorem circleModule_t2 : T2Space circleModule :=
  inferInstanceAs (T2Space (AddCircle (1 : ℝ)))

/-- The circle with period `1` is compact. -/
theorem circleModule_compact : CompactSpace circleModule := by
  let _ : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  exact AddCircle.compactSpace (1 : ℝ)

/-- The one-sided tensor of the rational coefficient module with the real circle. -/
abbrev rationalCircleTensor : TopModuleCat ℤ :=
  TopModuleCat.tensorLeftObj ℤ rationalCoefficients circleModule

/-- The carrier of the circle tensor is the algebraic integer tensor product. -/
@[simp]
theorem rationalCircleTensor_coe :
    (rationalCircleTensor : Type) = TensorProduct ℤ ℚ (AddCircle (1 : ℝ)) :=
  TopModuleCat.coe_tensorLeftObj ℤ rationalCoefficients circleModule

/-- The continuous integer-linear tensor generator at rational coefficient `1`. -/
def circleTensorGenerator : circleModule →L[ℤ] rationalCircleTensor :=
  TopModuleCat.tensorGenerator ℤ rationalCoefficients circleModule (1 : ℚ)

/-- The topology carried by `rationalCircleTensor` on its underlying integer tensor product. -/
public abbrev tensorTopology :
    TopologicalSpace (TensorProduct ℤ ℚ (AddCircle (1 : ℝ))) :=
  rationalCircleTensor.topologicalSpace
attribute [local instance] tensorTopology

/-- The circle tensor generator is the pure tensor with left factor `1`. -/
@[simp]
theorem circleTensorGenerator_apply (m : circleModule) :
    DFunLike.coe
      (F := AddCircle (1 : ℝ) →L[ℤ]
        TensorProduct ℤ ℚ (AddCircle (1 : ℝ)))
      circleTensorGenerator m = (1 : ℚ) ⊗ₜ[ℤ] m :=
  TopModuleCat.tensorGenerator_apply ℤ rationalCoefficients circleModule (1 : ℚ) m

/-- Forgetting continuity gives the algebraic tensor generator at `1`. -/
@[simp]
theorem circleTensorGenerator_toLinearMap :
    circleTensorGenerator.toLinearMap =
      (TensorProduct.mk ℤ rationalCoefficients circleModule) (1 : ℚ) :=
  TopModuleCat.tensorGenerator_toLinearMap ℤ rationalCoefficients circleModule (1 : ℚ)

/-- The tensor generator at `1` is continuous for the one-sided tensor topology. -/
theorem circleTensorGenerator_continuous : Continuous circleTensorGenerator :=
  circleTensorGenerator.continuous

/-- The generator sends the zero circle point to zero. -/
@[simp]
theorem circleTensorGenerator_zero :
    DFunLike.coe
      (F := AddCircle (1 : ℝ) →L[ℤ]
        TensorProduct ℤ ℚ (AddCircle (1 : ℝ)))
      circleTensorGenerator 0 = 0 :=
  circleTensorGenerator.map_zero

/-- The generator vanishes on the class of the integer period `1`. -/
@[simp]
theorem circleTensorGenerator_period :
    DFunLike.coe
      (F := AddCircle (1 : ℝ) →L[ℤ]
        TensorProduct ℤ ℚ (AddCircle (1 : ℝ)))
      circleTensorGenerator ((1 : ℝ) : AddCircle (1 : ℝ)) = 0 := by
  rw [AddCircle.coe_period]
  exact circleTensorGenerator_zero

/-- The value of the circle tensor generator at the class of `√2`. -/
def irrationalGenerator : rationalCircleTensor :=
  circleTensorGenerator ((Real.sqrt 2 : ℝ) : AddCircle (1 : ℝ))

/-- The generator value at the class of `√2` is its pure tensor with `1`. -/
theorem irrationalGenerator_eq_tmul :
    irrationalGenerator = (1 : ℚ) ⊗ₜ[ℤ] ((Real.sqrt 2 : ℝ) : AddCircle (1 : ℝ)) :=
  circleTensorGenerator_apply _

end TensorCircleExamples
