/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicDirectLimits.Topology.TensorProduct.Prod
public import AlgebraicDirectLimitsExamples.ProjectiveTensorSeparation

/-!
# Binary-product tensor calculations with infinite integer coefficients

The coefficient module is the canonical `ℕ →₀ ℤ` from the projective tensor
separation examples. Both right factors are the usual real topological integer
module. The binary-product equivalence acts on a sum supported in two different
coefficient and right-factor positions, and on a pure tensor with both right
coordinates nonzero. The coordinate maps detect these values without any tensor
Hausdorffness assumption.

The maps used for naturality double the algebraic coefficients, leave the first
real factor fixed and negate the second. The resulting two detector values are
`2` and `-4`. The final calculation allows all source and target carrier universes
to vary independently.

## References

The coefficient basis, real module and coordinate detectors reuse
`ProjectiveTensorSeparationExamples`. Mathlib's product tensor equivalence is due
to Eric Wieser; its tensor-map API is due to Kenny Lau and Mario Carneiro. The
one-sided tensor topology, generators and continuity criterion follow Formal
Frontier Agents' topological tensor development. The Finsupp and basis APIs are
due to Johannes Hölzl, Kim Morrison, Mario Carneiro, Alexander Bentkamp and Jakob
von Raumer. Integer-action continuity is due to Johannes Hölzl, Mario Carneiro
and Patrick Massot. The continuous linear APIs are credited in
`AlgebraicDirectLimits.Topology.TensorProduct.Prod`.
-/

@[expose] public section

open scoped TensorProduct
open ProjectiveTensorSeparationExamples

universe uR uC uM uN uD uM' uN'

namespace TensorProductExamples.BinaryProducts

/-- The canonical commutative ring dictionary for the scalar integers. -/
abbrev integerRing : CommRing ℤ := inferInstance

/-- The usual topology dictionary on the integers. -/
abbrev integerTopology : TopologicalSpace ℤ := inferInstance

/-- The self-algebra dictionary used by the two-scalar tensor equivalence. -/
abbrev integerSelfAlgebra : Algebra ℤ ℤ := inferInstance

/-- The canonical integer module dictionary on the Finsupp coefficients. -/
noncomputable abbrev coefficientModule : Module ℤ infiniteCoefficients := inferInstance

/-- The self-scalar tower on the coefficient module. -/
abbrev coefficientSelfTower : IsScalarTower ℤ ℤ infiniteCoefficients := inferInstance

/-- The existing countably infinite basis of the concrete coefficient module. -/
noncomputable def coefficientBasis : Module.Basis ℕ ℤ infiniteCoefficients :=
  ProjectiveTensorSeparationExamples.infiniteBasis

/-- The canonical integer action on the usual real module. -/
abbrev realIntegerModule : Module ℤ realModule := inferInstance

/-- The usual real topology on the right factor. -/
abbrev realTopology : TopologicalSpace realModule := inferInstance

/-- Addition is continuous for the usual real right factor. -/
abbrev realContinuousAdd : ContinuousAdd realModule := inferInstance

/-- The jointly continuous integer action on the usual real right factor. -/
abbrev realContinuousSMul : ContinuousSMul ℤ realModule := inferInstance

/-- The right product with the product topology and componentwise integer action. -/
abbrev realProductObj : TopModuleCat ℤ :=
  TopModuleCat.of ℤ (realModule × realModule)

/-- The canonical module dictionary on the right product. -/
abbrev realProductModule : Module ℤ (realModule × realModule) := inferInstance

/-- The product topology dictionary on the two real right factors. -/
abbrev realProductTopology : TopologicalSpace (realModule × realModule) := inferInstance

/-- Continuous addition on the product of the usual real modules. -/
abbrev realProductContinuousAdd : ContinuousAdd (realModule × realModule) := inferInstance

/-- The jointly continuous componentwise integer action on the right product. -/
abbrev realProductContinuousSMul : ContinuousSMul ℤ (realModule × realModule) := inferInstance

/-- The tensor of the infinite coefficient module with the real product. -/
noncomputable abbrev productTensorObj : TopModuleCat ℤ :=
  TopModuleCat.tensorLeftObj ℤ infiniteCoefficients realProductObj

/-- The product of the two existing tensor carriers as a topological integer module. -/
noncomputable abbrev tensorPairObj : TopModuleCat ℤ :=
  TopModuleCat.of ℤ (infiniteTensor × infiniteTensor)

/-- The canonical integer module dictionary on the source tensor object. -/
noncomputable abbrev productTensorModule : Module ℤ productTensorObj := inferInstance

/-- The supplied topology dictionary on the source tensor object. -/
noncomputable abbrev productTensorTopology : TopologicalSpace productTensorObj := inferInstance

/-- Continuous addition on the source tensor object. -/
noncomputable abbrev productTensorContinuousAdd : ContinuousAdd productTensorObj := inferInstance

/-- The jointly continuous integer action on the source tensor object. -/
noncomputable abbrev productTensorContinuousSMul :
    ContinuousSMul ℤ productTensorObj := inferInstance

/-- The componentwise integer module dictionary on the target tensor pair. -/
noncomputable abbrev tensorPairModule : Module ℤ (infiniteTensor × infiniteTensor) := inferInstance

/-- The ordinary product topology dictionary on the target tensor pair. -/
noncomputable abbrev tensorPairTopology : TopologicalSpace (infiniteTensor × infiniteTensor) :=
  inferInstance

/-- Continuous addition on the target tensor pair. -/
noncomputable abbrev tensorPairContinuousAdd : ContinuousAdd (infiniteTensor × infiniteTensor) :=
  inferInstance

/-- The jointly continuous integer action on the target tensor pair. -/
noncomputable abbrev tensorPairContinuousSMul :
    ContinuousSMul ℤ (infiniteTensor × infiniteTensor) := inferInstance

/-- The infinite coefficients are not finitely generated, by the existing basis theorem. -/
abbrev coefficientNotFinite : ¬ Module.Finite ℤ infiniteCoefficients :=
  ProjectiveTensorSeparationExamples.infiniteCoefficients_not_finite

/-- The real right factor is nondiscrete, by the existing real-topology theorem. -/
abbrev realNotDiscrete : ¬ DiscreteTopology realModule :=
  ProjectiveTensorSeparationExamples.realModule_not_discrete

/-- The first real factor embeds in the product along the zero second coordinate. -/
abbrev realProductFirstEmbedding :
    Topology.IsEmbedding (fun m : realModule ↦ (m, (0 : realModule))) :=
  isEmbedding_prodMkLeft (0 : realModule)

/-- Discreteness of the product would restrict to discreteness of its first real factor. -/
abbrev realDiscreteOfProduct [DiscreteTopology (realModule × realModule)] :
    DiscreteTopology realModule := realProductFirstEmbedding.discreteTopology

/-- The product of the usual real right factors is nondiscrete. -/
theorem realProduct_not_discrete : ¬ DiscreteTopology realProductObj := by
  intro h
  let : DiscreteTopology (realModule × realModule) := h
  exact realNotDiscrete realDiscreteOfProduct

/-- Distribution for infinite integer coefficients and two usual real factors. -/
noncomputable def productEquiv : productTensorObj ≃L[ℤ] (infiniteTensor × infiniteTensor) :=
  TopModuleCat.tensorProdRight ℤ infiniteCoefficients realModule realModule

/-- The forward equivalence map with its target packaged as a product of tensor objects. -/
noncomputable def productMapToPairObj : productTensorObj →L[ℤ] tensorPairObj :=
  productEquiv.toContinuousLinearMap

/-- The product map of the two real generators at coefficient `e₀`. -/
noncomputable def firstCoefficientGeneratorPair : realProductObj →L[ℤ] tensorPairObj :=
  (TopModuleCat.tensorGenerator ℤ infiniteCoefficients realModule (integerBasisVector 0)).prodMap
    (TopModuleCat.tensorGenerator ℤ infiniteCoefficients realModule (integerBasisVector 0))

/-- The first output tensor, with coefficient `e₀` and right value `1`. -/
noncomputable def a : infiniteTensor := integerBasisVector 0 ⊗ₜ[ℤ] (1 : realModule)

/-- The second output tensor, with coefficient `e₁` and right value `2`. -/
noncomputable def b : infiniteTensor := integerBasisVector 1 ⊗ₜ[ℤ] (2 : realModule)

/-- The first output tensor is nonzero by the existing first-tensor detector. -/
abbrev aNonzero : a ≠ 0 := ProjectiveTensorSeparationExamples.infiniteFirstTensor_ne_zero

/-- The existing basis-coordinate formula evaluated on the first output tensor. -/
abbrev aCoordinateFormula :
    infiniteCoordinates a 0 = if (0 : ℕ) = 0 then (1 : realModule) else 0 :=
  ProjectiveTensorSeparationExamples.infiniteCoordinates_basis_tmul 0 0 (1 : realModule)

/-- The existing basis-coordinate formula evaluated on the second output tensor. -/
abbrev bCoordinateFormula :
    infiniteCoordinates b 1 = if (1 : ℕ) = 1 then (2 : realModule) else 0 :=
  ProjectiveTensorSeparationExamples.infiniteCoordinates_basis_tmul 1 1 (2 : realModule)

/-- A pure tensor supported in the first right-factor position. -/
noncomputable def zL : productTensorObj :=
  integerBasisVector 0 ⊗ₜ[ℤ] ((1 : realModule), (0 : realModule))

/-- A pure tensor supported in the second right-factor position. -/
noncomputable def zR : productTensorObj :=
  integerBasisVector 1 ⊗ₜ[ℤ] ((0 : realModule), (2 : realModule))

/-- The sum of the two differently supported pure tensors. -/
noncomputable def z : productTensorObj := zL + zR

/-- A pure tensor with the same coefficient in both nonzero right positions. -/
noncomputable def w : productTensorObj :=
  integerBasisVector 0 ⊗ₜ[ℤ] ((1 : realModule), (2 : realModule))

/-- The tensor map of the first right projection. -/
noncomputable def tensorFirst : productTensorObj →L[ℤ] infiniteTensor :=
  TopModuleCat.tensorMapCLM ℤ (C := infiniteCoefficients) (D := infiniteCoefficients)
    (M := realProductObj) (N := realModule)
    (LinearMap.id : infiniteCoefficients →ₗ[ℤ] infiniteCoefficients)
    (ContinuousLinearMap.fst ℤ realModule realModule)

/-- The tensor map of the second right projection. -/
noncomputable def tensorSecond : productTensorObj →L[ℤ] infiniteTensor :=
  TopModuleCat.tensorMapCLM ℤ (C := infiniteCoefficients) (D := infiniteCoefficients)
    (M := realProductObj) (N := realModule)
    (LinearMap.id : infiniteCoefficients →ₗ[ℤ] infiniteCoefficients)
    (ContinuousLinearMap.snd ℤ realModule realModule)

/-- The tensor map of the first right inclusion. -/
noncomputable def tensorInl : infiniteTensor →L[ℤ] productTensorObj :=
  TopModuleCat.tensorMapCLM ℤ (C := infiniteCoefficients) (D := infiniteCoefficients)
    (M := realModule) (N := realProductObj)
    (LinearMap.id : infiniteCoefficients →ₗ[ℤ] infiniteCoefficients)
    (ContinuousLinearMap.inl ℤ realModule realModule)

/-- The tensor map of the second right inclusion. -/
noncomputable def tensorInr : infiniteTensor →L[ℤ] productTensorObj :=
  TopModuleCat.tensorMapCLM ℤ (C := infiniteCoefficients) (D := infiniteCoefficients)
    (M := realModule) (N := realProductObj)
    (LinearMap.id : infiniteCoefficients →ₗ[ℤ] infiniteCoefficients)
    (ContinuousLinearMap.inr ℤ realModule realModule)

/-- The product equivalence has exactly the stock underlying algebraic equivalence. -/
theorem productEquiv_toLinearEquiv :
    productEquiv.toLinearEquiv =
      (show productTensorObj ≃ₗ[ℤ] (infiniteTensor × infiniteTensor) from
        TensorProduct.prodRight ℤ ℤ infiniteCoefficients realModule realModule) := by
  exact TopModuleCat.tensorProdRight_toLinearEquiv ℤ infiniteCoefficients realModule realModule

/-- The forward map is the product of the constructed tensor projections. -/
theorem productEquiv_toContinuousLinearMap :
    productEquiv.toContinuousLinearMap = tensorFirst.prod tensorSecond := by
  exact TopModuleCat.tensorProdRight_toContinuousLinearMap
    ℤ infiniteCoefficients realModule realModule

/-- The inverse map is the coproduct of the constructed tensor inclusions. -/
theorem productEquiv_symm_toContinuousLinearMap :
    productEquiv.symm.toContinuousLinearMap = tensorInl.coprod tensorInr := by
  exact TopModuleCat.tensorProdRight_symm_toContinuousLinearMap
    ℤ infiniteCoefficients realModule realModule

/-- The first supported input maps to a pair supported in the first tensor position. -/
theorem productEquiv_zL : productEquiv zL = (a, 0) := by
  have hdist : productEquiv zL =
      (show infiniteTensor × infiniteTensor from
        (integerBasisVector 0 ⊗ₜ[ℤ] (1 : realModule),
         integerBasisVector 0 ⊗ₜ[ℤ] (0 : realModule))) :=
    TopModuleCat.tensorProdRight_tmul ℤ infiniteCoefficients realModule realModule
      (integerBasisVector 0) (1 : realModule) (0 : realModule)
  have hzero : (show infiniteTensor from
      integerBasisVector 0 ⊗ₜ[ℤ] (0 : realModule)) = 0 :=
    TensorProduct.tmul_zero (R := ℤ) (M := infiniteCoefficients) (N := realModule)
      (integerBasisVector 0)
  exact hdist.trans (congrArg (fun y : infiniteTensor ↦ (a, y)) hzero)

/-- The second supported input maps to a pair supported in the second tensor position. -/
theorem productEquiv_zR : productEquiv zR = (0, b) := by
  have hdist : productEquiv zR =
      (show infiniteTensor × infiniteTensor from
        (integerBasisVector 1 ⊗ₜ[ℤ] (0 : realModule),
         integerBasisVector 1 ⊗ₜ[ℤ] (2 : realModule))) :=
    TopModuleCat.tensorProdRight_tmul ℤ infiniteCoefficients realModule realModule
      (integerBasisVector 1) (0 : realModule) (2 : realModule)
  have hzero : (show infiniteTensor from
      integerBasisVector 1 ⊗ₜ[ℤ] (0 : realModule)) = 0 :=
    TensorProduct.tmul_zero (R := ℤ) (M := infiniteCoefficients) (N := realModule)
      (integerBasisVector 1)
  exact hdist.trans (congrArg (fun x : infiniteTensor ↦ (x, b)) hzero)

/-- The mixed sum distributes to the two independently-coefficient output tensors. -/
theorem productEquiv_z : productEquiv z = (a, b) := by
  have hadd : productEquiv z = productEquiv zL + productEquiv zR :=
    map_add productEquiv zL zR
  have hpair : productEquiv zL + productEquiv zR =
      (show infiniteTensor × infiniteTensor from (a, 0) + (0, b)) :=
    congrArg₂ (fun p q : infiniteTensor × infiniteTensor ↦ p + q)
      productEquiv_zL productEquiv_zR
  have hsum : (show infiniteTensor × infiniteTensor from (a, 0) + (0, b)) = (a, b) := by
    simp only [Prod.mk_add_mk, add_zero, zero_add]
  exact hadd.trans (hpair.trans hsum)

/-- The mixed pure tensor distributes with coefficient `e₀` in both output positions. -/
theorem productEquiv_w :
    productEquiv w =
      (a, integerBasisVector 0 ⊗ₜ[ℤ] (2 : realModule)) := by
  exact TopModuleCat.tensorProdRight_tmul ℤ infiniteCoefficients realModule realModule
    (integerBasisVector 0) 1 2

/-- The generator at `e₀` maps the pair `(1, 2)` to its two factor generators. -/
theorem productEquiv_generator :
    productEquiv (TopModuleCat.tensorGenerator ℤ infiniteCoefficients realProductObj
      (integerBasisVector 0) ((1 : realModule), (2 : realModule))) =
        (TopModuleCat.tensorGenerator ℤ infiniteCoefficients realModule (integerBasisVector 0) 1,
         TopModuleCat.tensorGenerator ℤ infiniteCoefficients realModule
           (integerBasisVector 0) 2) := by
  exact TopModuleCat.tensorProdRight_tensorGenerator_apply
    ℤ infiniteCoefficients realModule realModule (integerBasisVector 0) 1 2

/-- Distribution after the real-product generator at `e₀` is its factorwise generator map. -/
theorem productMapToPairObj_comp_generator :
    productMapToPairObj.comp (TopModuleCat.tensorGenerator ℤ infiniteCoefficients realProductObj
      (integerBasisVector 0)) = firstCoefficientGeneratorPair := by
  exact TopModuleCat.tensorProdRight_comp_tensorGenerator
    ℤ infiniteCoefficients realModule realModule (integerBasisVector 0)

/-- The two output tensors have detector values `1` and `2` at their respective basis positions. -/
theorem output_coordinates :
    infiniteCoordinates a 0 = 1 ∧ infiniteCoordinates b 1 = 2 := by
  constructor
  · simpa using aCoordinateFormula
  · simpa using bCoordinateFormula

/-- The second tensor is nonzero, as detected at coefficient position `1`. -/
theorem b_ne_zero : b ≠ 0 := by
  intro h
  have hc := output_coordinates.2
  rw [h, map_zero] at hc
  norm_num at hc

/-- Both components of the image of the mixed sum are nonzero. -/
theorem productEquiv_z_components_ne_zero :
    (productEquiv z).1 ≠ 0 ∧ (productEquiv z).2 ≠ 0 := by
  simpa only [productEquiv_z] using And.intro aNonzero b_ne_zero

/-- The two supported inputs are nonzero and distinct, and their sum is nonzero. -/
theorem supported_inputs_nonzero_distinct :
    zL ≠ 0 ∧ zR ≠ 0 ∧ zL ≠ zR ∧ z ≠ 0 := by
  have hzero : productEquiv (0 : productTensorObj) =
      (0 : infiniteTensor × infiniteTensor) := map_zero productEquiv
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    have hp : (a, (0 : infiniteTensor)) = (0 : infiniteTensor × infiniteTensor) :=
      productEquiv_zL.symm.trans ((congrArg productEquiv h).trans hzero)
    exact aNonzero (congrArg (fun p : infiniteTensor × infiniteTensor ↦ p.1) hp)
  · intro h
    have hp : ((0 : infiniteTensor), b) = (0 : infiniteTensor × infiniteTensor) :=
      productEquiv_zR.symm.trans ((congrArg productEquiv h).trans hzero)
    exact b_ne_zero (congrArg (fun p : infiniteTensor × infiniteTensor ↦ p.2) hp)
  · intro h
    apply aNonzero
    simpa only [productEquiv_zL, productEquiv_zR] using
      congrArg (fun x : productTensorObj ↦ (productEquiv x).1) h
  · intro h
    have hp : (a, b) = (0 : infiniteTensor × infiniteTensor) :=
      productEquiv_z.symm.trans ((congrArg productEquiv h).trans hzero)
    exact aNonzero (congrArg (fun p : infiniteTensor × infiniteTensor ↦ p.1) hp)

/-- Each supported image differs from the image of their mixed sum. -/
theorem supported_images_proper :
    productEquiv zL ≠ productEquiv z ∧ productEquiv zR ≠ productEquiv z := by
  constructor
  · intro h
    apply b_ne_zero
    simpa only [productEquiv_zL, productEquiv_z] using (congrArg Prod.snd h).symm
  · intro h
    apply aNonzero
    simpa only [productEquiv_zR, productEquiv_z] using (congrArg Prod.fst h).symm

/-- Distinct coefficient supports distinguish the two output tensors. -/
theorem a_ne_b : a ≠ b := by
  -- The zeroth coordinate is one for `a` and zero for the differently supported `b`.
  intro h
  have hb : infiniteCoordinates b 0 = 0 := by
    simpa [b] using infiniteCoordinates_basis_tmul 1 0 (2 : realModule)
  have ha := output_coordinates.1
  rw [h, hb] at ha
  exact (zero_ne_one : (0 : ℝ) ≠ 1) ha

/-- Differently-coefficient and same-coefficient inputs are distinct. -/
theorem z_ne_w : z ≠ w := by
  -- The second output has coefficient support one for `z` and zero for `w`.
  intro h
  have hp : b = integerBasisVector 0 ⊗ₜ[ℤ] (2 : realModule) := by
    simpa only [productEquiv_z, productEquiv_w] using
      congrArg (fun x : productTensorObj ↦ (productEquiv x).2) h
  have hb := output_coordinates.2
  rw [hp, infiniteCoordinates_basis_tmul] at hb
  norm_num at hb

/-- Arbitrary inverse reconstruction recovers the mixed sum from its output pair. -/
theorem productEquiv_symm_pair : productEquiv.symm (a, b) = z := by
  rw [← productEquiv_z]
  exact productEquiv.symm_apply_apply z

/-- The inverse reconstruction is the sum of the two constructed tensor inclusions. -/
theorem productEquiv_symm_pair_inclusions :
    productEquiv.symm (a, b) = tensorInl a + tensorInr b := by
  exact TopModuleCat.tensorProdRight_symm_apply_pair
    ℤ infiniteCoefficients realModule realModule a b

/-- The same-coefficient inverse formula separately recovers the mixed pure tensor. -/
theorem productEquiv_symm_same_coefficient :
    productEquiv.symm (a, integerBasisVector 0 ⊗ₜ[ℤ] (2 : realModule)) = w := by
  exact TopModuleCat.tensorProdRight_symm_tmul ℤ infiniteCoefficients realModule realModule
    (integerBasisVector 0) (1 : realModule) (2 : realModule)

/-- Both projections after distribution agree with the constructed tensor projections. -/
theorem productEquiv_projection_comp :
    (ContinuousLinearMap.fst ℤ infiniteTensor infiniteTensor).comp
      productEquiv.toContinuousLinearMap = tensorFirst ∧
    (ContinuousLinearMap.snd ℤ infiniteTensor infiniteTensor).comp
      productEquiv.toContinuousLinearMap = tensorSecond := by
  exact ⟨TopModuleCat.tensorProdRight_fst_comp
      ℤ infiniteCoefficients realModule realModule,
    TopModuleCat.tensorProdRight_snd_comp ℤ infiniteCoefficients realModule realModule⟩

/-- Both inclusions before inverse distribution agree with the tensor inclusions. -/
theorem productEquiv_inverse_inclusion_comp :
    productEquiv.symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.inl ℤ infiniteTensor infiniteTensor) = tensorInl ∧
    productEquiv.symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.inr ℤ infiniteTensor infiniteTensor) = tensorInr := by
  exact ⟨TopModuleCat.tensorProdRight_symm_comp_inl
      ℤ infiniteCoefficients realModule realModule,
    TopModuleCat.tensorProdRight_symm_comp_inr ℤ infiniteCoefficients realModule realModule⟩

/-- The tensor projections recover the mixed sum's two output tensors. -/
theorem tensor_projections_z : tensorFirst z = a ∧ tensorSecond z = b := by
  have hmap : (tensorFirst.prod tensorSecond) z = productEquiv z :=
    (DFunLike.congr_fun productEquiv_toContinuousLinearMap z).symm
  have happly : (tensorFirst.prod tensorSecond) z = (tensorFirst z, tensorSecond z) :=
    ContinuousLinearMap.prod_apply tensorFirst tensorSecond z
  have hp : (tensorFirst z, tensorSecond z) = (a, b) :=
    happly.symm.trans (hmap.trans productEquiv_z)
  exact ⟨congrArg Prod.fst hp, congrArg Prod.snd hp⟩

/-- The tensor inclusions recover the two supported input tensors. -/
theorem tensor_inclusions_outputs : tensorInl a = zL ∧ tensorInr b = zR := by
  constructor
  · exact TopModuleCat.tensorMapCLM_tmul ℤ
      (C := infiniteCoefficients) (D := infiniteCoefficients)
      (M := realModule) (N := realProductObj)
      (LinearMap.id : infiniteCoefficients →ₗ[ℤ] infiniteCoefficients)
      (ContinuousLinearMap.inl ℤ realModule realModule)
      (integerBasisVector 0) (1 : realModule)
  · exact TopModuleCat.tensorMapCLM_tmul ℤ
      (C := infiniteCoefficients) (D := infiniteCoefficients)
      (M := realModule) (N := realProductObj)
      (LinearMap.id : infiniteCoefficients →ₗ[ℤ] infiniteCoefficients)
      (ContinuousLinearMap.inr ℤ realModule realModule)
      (integerBasisVector 1) (2 : realModule)

/-- The equivalence round trips recover the mixed sum and its output pair. -/
theorem mixed_round_trips :
    productEquiv.symm (productEquiv z) = z ∧
      productEquiv (productEquiv.symm (a, b)) = (a, b) := by
  exact ⟨productEquiv.symm_apply_apply z, productEquiv.apply_symm_apply (a, b)⟩

/-- The original one-factor mixed tensors' coordinate data remain available. -/
abbrev mixedXCoordinates :
    infiniteCoordinates infiniteMixedX 0 = 1 ∧ infiniteCoordinates infiniteMixedX 1 = 2 :=
  ProjectiveTensorSeparationExamples.infiniteMixedX_coordinates

/-- The original interchanged one-factor mixed tensors have different coordinate data. -/
abbrev mixedYCoordinates :
    infiniteCoordinates infiniteMixedY 0 = 2 ∧ infiniteCoordinates infiniteMixedY 1 = 1 :=
  ProjectiveTensorSeparationExamples.infiniteMixedY_coordinates

/-- The existing coordinate API distinguishes the original one-factor mixed tensors. -/
abbrev mixedXYDistinct : infiniteMixedX ≠ infiniteMixedY :=
  ProjectiveTensorSeparationExamples.infiniteMixedX_ne_mixedY

/-- Doubling on the algebraic coefficient module. -/
noncomputable def coefficientDoubling : infiniteCoefficients →ₗ[ℤ] infiniteCoefficients :=
  (2 : ℤ) • (LinearMap.id : infiniteCoefficients →ₗ[ℤ] infiniteCoefficients)

/-- The identity continuous linear map on the first real factor. -/
def firstRealMap : realModule →L[ℤ] realModule := ContinuousLinearMap.id ℤ realModule

/-- Negation as a continuous linear map on the second real factor. -/
def secondRealMap : realModule →L[ℤ] realModule := -(ContinuousLinearMap.id ℤ realModule)

/-- The product map fixing the first real coordinate and negating the second. -/
def realProductMap : realProductObj →L[ℤ] realProductObj :=
  firstRealMap.prodMap secondRealMap

/-- The tensor map doubling coefficients and applying the right product map. -/
noncomputable def inputTensorMap : productTensorObj →L[ℤ] productTensorObj :=
  TopModuleCat.tensorMapCLM ℤ (C := infiniteCoefficients) (D := infiniteCoefficients)
    (M := realProductObj) (N := realProductObj) coefficientDoubling realProductMap

/-- The first output tensor map doubles coefficients and leaves real values fixed. -/
noncomputable def firstOutputMap : infiniteTensor →L[ℤ] infiniteTensor :=
  TopModuleCat.tensorMapCLM ℤ (C := infiniteCoefficients) (D := infiniteCoefficients)
    (M := realModule) (N := realModule) coefficientDoubling firstRealMap

/-- The second output tensor map doubles coefficients and negates real values. -/
noncomputable def secondOutputMap : infiniteTensor →L[ℤ] infiniteTensor :=
  TopModuleCat.tensorMapCLM ℤ (C := infiniteCoefficients) (D := infiniteCoefficients)
    (M := realModule) (N := realModule) coefficientDoubling secondRealMap

/-- The ordinary product of the two constructed output tensor maps. -/
noncomputable def outputTensorMap :
    (infiniteTensor × infiniteTensor) →L[ℤ] (infiniteTensor × infiniteTensor) :=
  firstOutputMap.prodMap secondOutputMap

/-- Distribute the image of the mixed sum under the constructed input tensor map. -/
noncomputable def mappedMixedPair : infiniteTensor × infiniteTensor :=
  productEquiv (inputTensorMap z)

/-- The constructed nontrivial maps commute with binary-product distribution. -/
theorem productEquiv_naturality :
    outputTensorMap.comp productEquiv.toContinuousLinearMap =
      productEquiv.toContinuousLinearMap.comp inputTensorMap := by
  exact TopModuleCat.tensorProdRight_naturality ℤ coefficientDoubling firstRealMap secondRealMap

/-- The mapped mixed sum has the coefficient- and right-scaled output tensors. -/
theorem mappedMixedPair_tensors :
    mappedMixedPair =
      ((2 : ℤ) • a, (-2 : ℤ) • b) := by
  have hleft : (outputTensorMap.comp productEquiv.toContinuousLinearMap) z =
      outputTensorMap (productEquiv z) :=
    ContinuousLinearMap.comp_apply outputTensorMap productEquiv.toContinuousLinearMap z
  have hright : (productEquiv.toContinuousLinearMap.comp inputTensorMap) z =
      mappedMixedPair :=
    ContinuousLinearMap.comp_apply productEquiv.toContinuousLinearMap inputTensorMap z
  have hcomm : mappedMixedPair = outputTensorMap (productEquiv z) :=
    hright.symm.trans ((DFunLike.congr_fun productEquiv_naturality z).symm.trans hleft)
  have hprod : outputTensorMap (a, b) = (firstOutputMap a, secondOutputMap b) :=
    congrFun (ContinuousLinearMap.coe_prodMap' firstOutputMap secondOutputMap) (a, b)
  have hp : mappedMixedPair = (firstOutputMap a, secondOutputMap b) :=
    hcomm.trans ((congrArg outputTensorMap productEquiv_z).trans hprod)
  have ha : firstOutputMap a = (2 : ℤ) • a := by
    have hmap : firstOutputMap a =
        (show infiniteTensor from coefficientDoubling (integerBasisVector 0) ⊗ₜ[ℤ]
          firstRealMap (1 : realModule)) :=
      TopModuleCat.tensorMapCLM_tmul ℤ
        (C := infiniteCoefficients) (D := infiniteCoefficients)
        (M := realModule) (N := realModule) coefficientDoubling firstRealMap
        (integerBasisVector 0) (1 : realModule)
    have hc : coefficientDoubling (integerBasisVector 0) =
        (2 : ℤ) • integerBasisVector 0 :=
      LinearMap.smul_apply (2 : ℤ)
        (LinearMap.id : infiniteCoefficients →ₗ[ℤ] infiniteCoefficients) (integerBasisVector 0)
    have hr : firstRealMap (1 : realModule) = (1 : realModule) :=
      ContinuousLinearMap.id_apply (R₁ := ℤ) (1 : realModule)
    have himages : (show infiniteTensor from
        coefficientDoubling (integerBasisVector 0) ⊗ₜ[ℤ] firstRealMap (1 : realModule)) =
          (show infiniteTensor from ((2 : ℤ) • integerBasisVector 0) ⊗ₜ[ℤ] (1 : realModule)) :=
      congrArg₂ (fun (c : infiniteCoefficients) (m : realModule) ↦
        (show infiniteTensor from c ⊗ₜ[ℤ] m)) hc hr
    have hsmul : (show infiniteTensor from
        ((2 : ℤ) • integerBasisVector 0) ⊗ₜ[ℤ] (1 : realModule)) = (2 : ℤ) • a :=
      (TensorProduct.smul_tmul' (R := ℤ) (M := infiniteCoefficients) (N := realModule)
        (2 : ℤ) (integerBasisVector 0) (1 : realModule)).symm
    exact hmap.trans (himages.trans hsmul)
  have hb : secondOutputMap b = (-2 : ℤ) • b := by
    have hmap : secondOutputMap b =
        (show infiniteTensor from coefficientDoubling (integerBasisVector 1) ⊗ₜ[ℤ]
          secondRealMap (2 : realModule)) :=
      TopModuleCat.tensorMapCLM_tmul ℤ
        (C := infiniteCoefficients) (D := infiniteCoefficients)
        (M := realModule) (N := realModule) coefficientDoubling secondRealMap
        (integerBasisVector 1) (2 : realModule)
    have hc : coefficientDoubling (integerBasisVector 1) =
        (2 : ℤ) • integerBasisVector 1 :=
      LinearMap.smul_apply (2 : ℤ)
        (LinearMap.id : infiniteCoefficients →ₗ[ℤ] infiniteCoefficients) (integerBasisVector 1)
    have hr : secondRealMap (2 : realModule) = -(2 : realModule) :=
      neg_apply (ContinuousLinearMap.id ℤ realModule) (2 : realModule)
    have himages : (show infiniteTensor from
        coefficientDoubling (integerBasisVector 1) ⊗ₜ[ℤ] secondRealMap (2 : realModule)) =
          (show infiniteTensor from ((2 : ℤ) • integerBasisVector 1) ⊗ₜ[ℤ]
            (-(2 : realModule))) :=
      congrArg₂ (fun (c : infiniteCoefficients) (m : realModule) ↦
        (show infiniteTensor from c ⊗ₜ[ℤ] m)) hc hr
    have hneg : (show infiniteTensor from
        ((2 : ℤ) • integerBasisVector 1) ⊗ₜ[ℤ] (-(2 : realModule))) =
          -(show infiniteTensor from
            ((2 : ℤ) • integerBasisVector 1) ⊗ₜ[ℤ] (2 : realModule)) :=
      TensorProduct.tmul_neg (R := ℤ) ((2 : ℤ) • integerBasisVector 1) (2 : realModule)
    have hsmul : (show infiniteTensor from
        ((2 : ℤ) • integerBasisVector 1) ⊗ₜ[ℤ] (2 : realModule)) = (2 : ℤ) • b :=
      (TensorProduct.smul_tmul' (R := ℤ) (M := infiniteCoefficients) (N := realModule)
        (2 : ℤ) (integerBasisVector 1) (2 : realModule)).symm
    have hscaled : -(show infiniteTensor from
        ((2 : ℤ) • integerBasisVector 1) ⊗ₜ[ℤ] (2 : realModule)) = -((2 : ℤ) • b) :=
      congrArg (fun x : infiniteTensor ↦ -x) hsmul
    exact hmap.trans (himages.trans (hneg.trans (hscaled.trans (neg_smul (2 : ℤ) b).symm)))
  exact hp.trans (congrArg₂ (fun x y : infiniteTensor ↦ (x, y)) ha hb)

/-- The two detector values of the mapped mixed sum are `2` and `-4`. -/
theorem mappedMixedPair_coordinates :
    infiniteCoordinates mappedMixedPair.1 0 = 2 ∧
      infiniteCoordinates mappedMixedPair.2 1 = -4 := by
  rw [mappedMixedPair_tensors]
  constructor
  · exact (congrFun (infiniteCoordinates.map_smul (2 : ℤ) a) 0).trans (by
      rw [Pi.smul_apply, output_coordinates.1]
      norm_num [zsmul_eq_mul])
  · exact (congrFun (infiniteCoordinates.map_smul (-2 : ℤ) b) 1).trans (by
      rw [Pi.smul_apply, output_coordinates.2]
      norm_num [zsmul_eq_mul])

/-- The nontrivial maps move the exhibited mixed output pair. -/
theorem mappedMixedPair_ne_original : mappedMixedPair ≠ (a, b) := by
  intro h
  have hc := mappedMixedPair_coordinates.1
  rw [h, output_coordinates.1] at hc
  norm_num at hc

section IndependentUniverses

variable (R : Type uR) [CommRing R] [TopologicalSpace R]
variable (C : ModuleCat.{uC} R) (M : TopModuleCat.{uM} R) (N : TopModuleCat.{uN} R)
variable (D : ModuleCat.{uD} R) (M' : TopModuleCat.{uM'} R) (N' : TopModuleCat.{uN'} R)

/-- Mapping a pure tensor between independently leveled products and then distributing
has the independently mapped coefficient and right factors in its two output positions. -/
theorem mapped_pure_tensor (f : C →ₗ[R] D) (g : M →L[R] M') (h : N →L[R] N')
    (c : C) (m : M) (n : N) :
    TopModuleCat.tensorProdRight R D M' N'
      (TopModuleCat.tensorMapCLM R (C := C) (D := D)
        (M := TopModuleCat.of R (M × N)) (N := TopModuleCat.of R (M' × N'))
        f (g.prodMap h) (c ⊗ₜ[R] (m, n))) =
          (f c ⊗ₜ[R] g m, f c ⊗ₜ[R] h n) := by
  have hmap : TopModuleCat.tensorMapCLM R (C := C) (D := D)
      (M := TopModuleCat.of R (M × N)) (N := TopModuleCat.of R (M' × N'))
      f (g.prodMap h) (c ⊗ₜ[R] (m, n)) =
        (show TopModuleCat.tensorLeftObj R D (TopModuleCat.of R (M' × N')) from
          f c ⊗ₜ[R] (g m, h n)) :=
    TopModuleCat.tensorMapCLM_tmul R (C := C) (D := D)
      (M := TopModuleCat.of R (M × N)) (N := TopModuleCat.of R (M' × N'))
      f (g.prodMap h) c (m, n)
  have hdist : TopModuleCat.tensorProdRight R D M' N' (f c ⊗ₜ[R] (g m, h n)) =
      (show TopModuleCat.tensorLeftObj R D M' × TopModuleCat.tensorLeftObj R D N' from
        (f c ⊗ₜ[R] g m, f c ⊗ₜ[R] h n)) :=
    TopModuleCat.tensorProdRight_tmul R D M' N' (f c) (g m) (h n)
  exact (congrArg (TopModuleCat.tensorProdRight R D M' N') hmap).trans hdist

end IndependentUniverses

end TensorProductExamples.BinaryProducts
