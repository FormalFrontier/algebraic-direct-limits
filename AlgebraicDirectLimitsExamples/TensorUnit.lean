/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicDirectLimits.Topology.TensorUnit
public import Mathlib.Topology.Instances.Int

/-!
# The scalar tensor unit on integer pairs

The right factor is `ℤ × ℤ` with its canonical product topology and pointwise
integer action. Both integer factors are discrete. The scalar tensor unit sends
`2 ⊗ₜ (1, 0)` to `(2, 0)`, and its inverse sends the nonzero vector `(1, 0)`
to `1 ⊗ₜ (1, 0)`. Continuous right-factor doubling induces a tensor endomorphism
that moves this inverse image and commutes with the unit.

These calculations use the continuous scalar unit itself, the existing tensor
generators and the existing two-variable continuous tensor map. They require no
basis coordinates or projections.

## References

The tensor unit is that of `AlgebraicDirectLimits.Topology.TensorUnit`, using
Mathlib's algebraic tensor identity and the preceding one-sided tensor topology.
Mathlib's integer topology is due to Johannes Hölzl and Mario Carneiro. The pair
and doubling calculations are elementary specializations.
-/

@[expose] public section

open scoped TensorProduct

namespace TensorUnitExamples

/-- Integer pairs with the canonical product topology and pointwise module action. -/
abbrev integerPairModule : TopModuleCat ℤ := TopModuleCat.of ℤ (ℤ × ℤ)

/-- The continuous scalar tensor unit for the integer-pair module. -/
noncomputable def integerPairUnit :
    TopModuleCat.tensorLeftObj ℤ (ModuleCat.of ℤ ℤ) integerPairModule ≃L[ℤ]
      integerPairModule :=
  TopModuleCat.tensorUnitContinuousLinearEquiv ℤ integerPairModule

/-- The first nonzero integer-pair vector. -/
def firstVector : ℤ × ℤ := (1, 0)

/-- The first vector is not zero. -/
theorem firstVector_ne_zero : firstVector ≠ 0 := by
  intro h
  have hf := congrArg Prod.fst h
  simp [firstVector] at hf

/-- The inverse image of the first vector under the continuous scalar tensor unit. -/
noncomputable def firstUnitTensor :
    TopModuleCat.tensorLeftObj ℤ (ModuleCat.of ℤ ℤ) integerPairModule :=
  integerPairUnit.symm firstVector

/-- The inverse image is the pure tensor with scalar coefficient `1`. -/
theorem firstUnitTensor_eq_tmul :
    firstUnitTensor = (1 : ℤ) ⊗ₜ[ℤ] (firstVector : integerPairModule) := by
  exact TopModuleCat.tensorUnitContinuousLinearEquiv_symm_apply ℤ integerPairModule firstVector

/-- Applying the continuous unit to its inverse image recovers the first vector. -/
theorem firstUnitTensor_image : integerPairUnit firstUnitTensor = firstVector := by
  exact integerPairUnit.apply_symm_apply firstVector

/-- The tensor generator with coefficient `2` at the first integer-pair vector. -/
noncomputable def twiceFirstUnitTensor :
    TopModuleCat.tensorLeftObj ℤ (ModuleCat.of ℤ ℤ) integerPairModule :=
  TopModuleCat.tensorGenerator ℤ (ModuleCat.of ℤ ℤ) integerPairModule 2 firstVector

/-- The continuous unit sends `2 ⊗ₜ (1, 0)` to `(2, 0)`. -/
theorem twiceFirstUnitTensor_image :
    integerPairUnit twiceFirstUnitTensor = ((2, 0) : integerPairModule) := by
  change TopModuleCat.tensorUnitContinuousLinearEquiv ℤ integerPairModule
    (TopModuleCat.tensorGenerator ℤ (ModuleCat.of ℤ ℤ) integerPairModule 2 firstVector) = _
  rw [TopModuleCat.tensorUnitContinuousLinearEquiv_tensorGenerator_apply]
  simp [firstVector, Prod.smul_mk]

/-- The tensor inverse image of the first vector is nonzero. -/
theorem firstUnitTensor_ne_zero : firstUnitTensor ≠ 0 := by
  intro h
  apply firstVector_ne_zero
  calc
    firstVector = integerPairUnit firstUnitTensor := firstUnitTensor_image.symm
    _ = 0 := by rw [h, map_zero]

/-- The tensor with scalar coefficient `2` is nonzero. -/
theorem twiceFirstUnitTensor_ne_zero : twiceFirstUnitTensor ≠ 0 := by
  intro h
  have hv : ((2, 0) : integerPairModule) = 0 := by
    calc
      (2, 0) = integerPairUnit twiceFirstUnitTensor := twiceFirstUnitTensor_image.symm
      _ = 0 := by rw [h, map_zero]
  have hf := congrArg (fun m : integerPairModule ↦ m.1) hv
  simp at hf

/-- Doubling as a continuous linear endomorphism of the integer-pair module. -/
noncomputable def integerPairDoubling : integerPairModule →L[ℤ] integerPairModule :=
  2 • ContinuousLinearMap.id ℤ integerPairModule

/-- Right-factor doubling sends the first vector to `(2, 0)`. -/
theorem integerPairDoubling_apply_firstVector :
    integerPairDoubling firstVector = ((2, 0) : integerPairModule) := by
  simp [integerPairDoubling, firstVector, Prod.smul_mk]

/-- Right-factor doubling is not the identity continuous linear map. -/
theorem integerPairDoubling_ne_id :
    integerPairDoubling ≠ ContinuousLinearMap.id ℤ integerPairModule := by
  intro h
  have hv : ((2, 0) : integerPairModule) = firstVector := by
    calc
      (2, 0) = integerPairDoubling firstVector := integerPairDoubling_apply_firstVector.symm
      _ = firstVector := by rw [h, ContinuousLinearMap.id_apply]
  have hf := congrArg (fun m : integerPairModule ↦ m.1) hv
  simp [firstVector] at hf

/-- Tensor doubling induced by algebraic scalar identity and continuous pair doubling. -/
noncomputable def integerPairTensorDoubling :
    TopModuleCat.tensorLeftObj ℤ (ModuleCat.of ℤ ℤ) integerPairModule →L[ℤ]
      TopModuleCat.tensorLeftObj ℤ (ModuleCat.of ℤ ℤ) integerPairModule :=
  TopModuleCat.tensorMapCLM ℤ
    (LinearMap.id : (ModuleCat.of ℤ ℤ) →ₗ[ℤ] (ModuleCat.of ℤ ℤ)) integerPairDoubling

/-- Tensor doubling sends `1 ⊗ₜ (1, 0)` to `2 ⊗ₜ (1, 0)`. -/
theorem integerPairTensorDoubling_firstUnitTensor :
    integerPairTensorDoubling firstUnitTensor = twiceFirstUnitTensor := by
  apply integerPairUnit.injective
  have h : integerPairUnit (integerPairTensorDoubling firstUnitTensor) =
      integerPairDoubling (integerPairUnit firstUnitTensor) :=
    DFunLike.congr_fun
      (TopModuleCat.tensorUnitContinuousLinearEquiv_naturality ℤ integerPairDoubling)
      firstUnitTensor
  calc
    _ = integerPairDoubling (integerPairUnit firstUnitTensor) := h
    _ = integerPairDoubling firstVector :=
      congrArg integerPairDoubling firstUnitTensor_image
    _ = ((2, 0) : integerPairModule) := integerPairDoubling_apply_firstVector
    _ = _ := twiceFirstUnitTensor_image.symm

/-- Tensor doubling moves the nonzero inverse image of the first vector. -/
theorem integerPairTensorDoubling_firstUnitTensor_ne :
    integerPairTensorDoubling firstUnitTensor ≠ firstUnitTensor := by
  intro h
  have ht : twiceFirstUnitTensor = firstUnitTensor :=
    integerPairTensorDoubling_firstUnitTensor.symm.trans h
  have hv : ((2, 0) : integerPairModule) = firstVector := by
    calc
      (2, 0) = integerPairUnit twiceFirstUnitTensor := twiceFirstUnitTensor_image.symm
      _ = integerPairUnit firstUnitTensor := congrArg (fun x ↦ integerPairUnit x) ht
      _ = firstVector := firstUnitTensor_image
  have hf := congrArg (fun m : integerPairModule ↦ m.1) hv
  simp [firstVector] at hf

/-- The induced tensor doubling map is not the identity. -/
theorem integerPairTensorDoubling_ne_id :
    integerPairTensorDoubling ≠ ContinuousLinearMap.id ℤ
      (TopModuleCat.tensorLeftObj ℤ (ModuleCat.of ℤ ℤ) integerPairModule) := by
  intro h
  apply integerPairTensorDoubling_firstUnitTensor_ne
  simpa only [ContinuousLinearMap.id_apply] using DFunLike.congr_fun h firstUnitTensor

/-- The continuous unit intertwines tensor doubling and right-factor doubling. -/
theorem integerPairUnit_doubling :
    integerPairUnit.toContinuousLinearMap.comp integerPairTensorDoubling =
      integerPairDoubling.comp integerPairUnit.toContinuousLinearMap := by
  exact TopModuleCat.tensorUnitContinuousLinearEquiv_naturality ℤ integerPairDoubling

end TensorUnitExamples
