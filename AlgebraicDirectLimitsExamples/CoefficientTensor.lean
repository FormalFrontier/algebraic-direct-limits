/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicDirectLimits.Topology.CoefficientTensor
public import AlgebraicDirectLimitsExamples.TensorHom
public import AlgebraicDirectLimitsExamples.TensorProduct.Map
public import AlgebraicDirectLimitsExamples.Restriction

/-!
# Coefficient tensor maps and categorical continuous-map families

Integer dot maps, infinitely many real coordinates, a nonfree ideal coefficient,
and regular and swapped product-ring actions give whole-map uses of the
coefficient tensor functor and its Hom equivalence. Coefficient changes and
target postcomposition are separate operations. The ideal coefficient has the
whole regular product module as both right factor and target; target doubling
acts on both coordinates. The infinite target is an ordinary unrestricted Pi
with its usual coordinate topology, not a finitely supported or discrete model.

The regular and swapped examples use their own stored module actions. No
linear identity between the two actions is constructed.

## Limitations

The characteristic identities in the coefficient-tensor API describe concrete Hom,
tensor maps, and currying. None of the definitions here uses those identities.

## References

These examples follow the integer and rank-one tensor maps in
`AlgebraicDirectLimitsExamples.TensorHom`, the coordinate and ideal models in
`AlgebraicDirectLimitsExamples.ProjectiveTensorSeparation`, and the scalar-action
comparison in `AlgebraicDirectLimitsExamples.Restriction`, by Formal Frontier
Agents, including Lantern's coordinate and split-cover constructions and Beacon's
topological formalization. The categorical family construction follows Wick's
coefficient tensor formulation. Mathlib supplies the categorical wrappers,
product linear maps and continuous coordinate projections. Prior mathematical
and formalization credit is separate from the Apache-2.0 licensing notice above.
-/

@[expose] public section

open CategoryTheory
open scoped TensorProduct

namespace CoefficientTensorExamples

/-- The integer dot pairing as an outgoing categorical tensor map. -/
noncomputable def integerOutgoing :
    (TopModuleCat.coefficientTensor ℤ TensorHomExamples.integerPairModule).obj
      TensorHomExamples.integerPairCoefficients ⟶ TensorHomExamples.integerModule :=
  CategoryTheory.ConcreteCategory.ofHom
    (C := TopModuleCat ℤ)
    (X := TopModuleCat.tensorLeftObj ℤ TensorHomExamples.integerPairCoefficients
      TensorHomExamples.integerPairModule)
    (Y := TensorHomExamples.integerModule)
    TensorHomExamples.integerDotTensor

/-- The inclusion of the first integer coefficient. -/
noncomputable def integerCoefficientInclusion :
    (ModuleCat.of ℤ ℤ) ⟶ TensorHomExamples.integerPairCoefficients :=
  ModuleCat.ofHom (LinearMap.inl ℤ ℤ ℤ)

/-- The first-coordinate projection of the integer coefficient module. -/
noncomputable def integerCoefficientProjection :
    TensorHomExamples.integerPairCoefficients ⟶ (ModuleCat.of ℤ ℤ) :=
  ModuleCat.ofHom (LinearMap.fst ℤ ℤ ℤ)

/-- The tensor map induced by inclusion of the first integer coefficient. -/
noncomputable def integerTensorInclusion :
    (TopModuleCat.coefficientTensor ℤ TensorHomExamples.integerPairModule).obj (ModuleCat.of ℤ
      ℤ) ⟶ (TopModuleCat.coefficientTensor ℤ TensorHomExamples.integerPairModule).obj
      TensorHomExamples.integerPairCoefficients :=
  (TopModuleCat.coefficientTensor ℤ TensorHomExamples.integerPairModule).map
    integerCoefficientInclusion

/-- The tensor map induced by first-coordinate coefficient projection. -/
noncomputable def integerTensorProjection :
    (TopModuleCat.coefficientTensor ℤ TensorHomExamples.integerPairModule).obj
      TensorHomExamples.integerPairCoefficients ⟶ (TopModuleCat.coefficientTensor ℤ
      TensorHomExamples.integerPairModule).obj (ModuleCat.of ℤ ℤ) :=
  (TopModuleCat.coefficientTensor ℤ TensorHomExamples.integerPairModule).map
    integerCoefficientProjection

/-- Doubling on the integer target module. -/
noncomputable def integerTargetDoubling :
    TensorHomExamples.integerModule ⟶ TensorHomExamples.integerModule :=
  TopModuleCat.ofHom ((2 : ℤ) • ContinuousLinearMap.id ℤ TensorHomExamples.integerModule)

/-- Postcomposition of the integer outgoing map by target doubling. -/
noncomputable def integerTargetComposite :
    (TopModuleCat.coefficientTensor ℤ TensorHomExamples.integerPairModule).obj
      TensorHomExamples.integerPairCoefficients ⟶ TensorHomExamples.integerModule :=
  integerOutgoing ≫ integerTargetDoubling

/-- Precomposition of the integer outgoing map by coefficient inclusion. -/
noncomputable def integerCoefficientComposite :
    (TopModuleCat.coefficientTensor ℤ TensorHomExamples.integerPairModule).obj (ModuleCat.of ℤ
      ℤ) ⟶ TensorHomExamples.integerModule :=
  integerTensorInclusion ≫ integerOutgoing

/-- The coefficient-indexed categorical family of integer dot maps. -/
noncomputable def integerCurried :
    TensorHomExamples.integerPairCoefficients ⟶ ((CategoryTheory.linearCoyoneda ℤ
      (TopModuleCat.{0} ℤ)).obj (Opposite.op TensorHomExamples.integerPairModule)).obj
      TensorHomExamples.integerModule :=
  TopModuleCat.coefficientTensorHomEquiv ℤ TensorHomExamples.integerPairModule
    TensorHomExamples.integerPairCoefficients TensorHomExamples.integerModule integerOutgoing

/-- The outgoing integer map recovered from its categorical family. -/
noncomputable def integerRecovered :
    (TopModuleCat.coefficientTensor ℤ TensorHomExamples.integerPairModule).obj
      TensorHomExamples.integerPairCoefficients ⟶ TensorHomExamples.integerModule :=
  (TopModuleCat.coefficientTensorHomEquiv ℤ TensorHomExamples.integerPairModule
    TensorHomExamples.integerPairCoefficients TensorHomExamples.integerModule).symm
    integerCurried

/-- The unrestricted product of copies of the usual real integer module. -/
noncomputable def infiniteProductTarget :
    TopModuleCat.{0} ℤ :=
  TopModuleCat.of ℤ (ℕ → ProjectiveTensorSeparationExamples.realModule)

/-- The all-coordinate outgoing map for infinitely many integer coefficients. -/
noncomputable def infiniteOutgoing :
    (TopModuleCat.coefficientTensor ℤ ProjectiveTensorSeparationExamples.realModule).obj
      ProjectiveTensorSeparationExamples.infiniteCoefficients ⟶ infiniteProductTarget :=
  CategoryTheory.ConcreteCategory.ofHom
    (C := TopModuleCat ℤ)
    (X := TopModuleCat.tensorLeftObj ℤ
      ProjectiveTensorSeparationExamples.infiniteCoefficients
      ProjectiveTensorSeparationExamples.realModule)
    (Y := infiniteProductTarget)
    ProjectiveTensorSeparationExamples.infiniteCoordinates

/-- The family of coefficient projections onto individual integer basis positions. -/
noncomputable def infiniteCoefficientProjection :
    (n : ℕ) → (ProjectiveTensorSeparationExamples.infiniteCoefficients ⟶
      ProjectiveTensorSeparationExamples.infiniteCoefficients) :=
  fun n => ModuleCat.ofHom (TensorMapExamples.coefficientProjection n)

/-- The tensor-map family induced by individual coefficient projections. -/
noncomputable def infiniteTensorProjection :
    (n : ℕ) → ((TopModuleCat.coefficientTensor ℤ
      ProjectiveTensorSeparationExamples.realModule).obj
      ProjectiveTensorSeparationExamples.infiniteCoefficients ⟶ (TopModuleCat.coefficientTensor
      ℤ ProjectiveTensorSeparationExamples.realModule).obj
      ProjectiveTensorSeparationExamples.infiniteCoefficients) :=
  fun n => (TopModuleCat.coefficientTensor ℤ ProjectiveTensorSeparationExamples.realModule).map
    (infiniteCoefficientProjection n)

/-- The continuous categorical projection from the real product onto a coordinate. -/
noncomputable def infiniteTargetProjection :
    (n : ℕ) → (infiniteProductTarget ⟶ ProjectiveTensorSeparationExamples.realModule) :=
  fun n => TopModuleCat.ofHom (ContinuousLinearMap.proj n)

/-- The coordinate readout family of the outgoing infinite tensor map. -/
noncomputable def infiniteTargetReadout :
    (n : ℕ) → ((TopModuleCat.coefficientTensor ℤ
      ProjectiveTensorSeparationExamples.realModule).obj
      ProjectiveTensorSeparationExamples.infiniteCoefficients ⟶
      ProjectiveTensorSeparationExamples.realModule) :=
  fun n => infiniteOutgoing ≫ infiniteTargetProjection n

/-- The outgoing infinite tensor map after projecting its coefficient. -/
noncomputable def infiniteCoefficientComposite :
    (n : ℕ) → ((TopModuleCat.coefficientTensor ℤ
      ProjectiveTensorSeparationExamples.realModule).obj
      ProjectiveTensorSeparationExamples.infiniteCoefficients ⟶ infiniteProductTarget) :=
  fun n => infiniteTensorProjection n ≫ infiniteOutgoing

/-- The categorical continuous-map family for the infinite coefficient module. -/
noncomputable def infiniteCurried :
    ProjectiveTensorSeparationExamples.infiniteCoefficients ⟶ ((CategoryTheory.linearCoyoneda ℤ
      (TopModuleCat.{0} ℤ)).obj (Opposite.op ProjectiveTensorSeparationExamples.realModule)).obj
      infiniteProductTarget :=
  TopModuleCat.coefficientTensorHomEquiv ℤ ProjectiveTensorSeparationExamples.realModule
    ProjectiveTensorSeparationExamples.infiniteCoefficients infiniteProductTarget
    infiniteOutgoing

/-- The outgoing infinite tensor map recovered from its categorical family. -/
noncomputable def infiniteRecovered :
    (TopModuleCat.coefficientTensor ℤ ProjectiveTensorSeparationExamples.realModule).obj
      ProjectiveTensorSeparationExamples.infiniteCoefficients ⟶ infiniteProductTarget :=
  (TopModuleCat.coefficientTensorHomEquiv ℤ ProjectiveTensorSeparationExamples.realModule
    ProjectiveTensorSeparationExamples.infiniteCoefficients infiniteProductTarget).symm
    infiniteCurried

/-- The ideal-coefficient tensor map into the whole regular product module. -/
noncomputable def idealOutgoing :
    (TopModuleCat.coefficientTensor ProjectiveTensorSeparationExamples.productRing
      ProjectiveTensorSeparationExamples.productModule).obj
      ProjectiveTensorSeparationExamples.firstAxisCoefficients ⟶
      ProjectiveTensorSeparationExamples.productModule :=
  CategoryTheory.ConcreteCategory.ofHom
    (C := TopModuleCat ProjectiveTensorSeparationExamples.productRing)
    (X := TopModuleCat.tensorLeftObj ProjectiveTensorSeparationExamples.productRing
      ProjectiveTensorSeparationExamples.firstAxisCoefficients
      ProjectiveTensorSeparationExamples.productModule)
    (Y := ProjectiveTensorSeparationExamples.productModule)
    ProjectiveTensorSeparationExamples.firstAxisTensorValue

/-- The canonical inclusion of the first-axis coefficient ideal. -/
noncomputable def idealCoefficientInclusion :
    ProjectiveTensorSeparationExamples.firstAxisCoefficients ⟶ (ModuleCat.of
      ProjectiveTensorSeparationExamples.productRing
      ProjectiveTensorSeparationExamples.productRing) :=
  ModuleCat.ofHom ProjectiveTensorSeparationExamples.firstAxisIdeal.subtype

/-- The coefficient retraction onto the first-axis ideal. -/
noncomputable def idealCoefficientRetraction :
    (ModuleCat.of ProjectiveTensorSeparationExamples.productRing
      ProjectiveTensorSeparationExamples.productRing) ⟶
      ProjectiveTensorSeparationExamples.firstAxisCoefficients :=
  ModuleCat.ofHom ProjectiveTensorSeparationExamples.firstAxisRetraction

/-- The tensor map induced by inclusion of the coefficient ideal. -/
noncomputable def idealTensorInclusion :
    (TopModuleCat.coefficientTensor ProjectiveTensorSeparationExamples.productRing
      ProjectiveTensorSeparationExamples.productModule).obj
      ProjectiveTensorSeparationExamples.firstAxisCoefficients ⟶ (TopModuleCat.coefficientTensor
      ProjectiveTensorSeparationExamples.productRing
      ProjectiveTensorSeparationExamples.productModule).obj (ModuleCat.of
      ProjectiveTensorSeparationExamples.productRing
      ProjectiveTensorSeparationExamples.productRing) :=
  (TopModuleCat.coefficientTensor ProjectiveTensorSeparationExamples.productRing
    ProjectiveTensorSeparationExamples.productModule).map idealCoefficientInclusion

/-- The tensor map induced by retraction onto the coefficient ideal. -/
noncomputable def idealTensorRetraction :
    (TopModuleCat.coefficientTensor ProjectiveTensorSeparationExamples.productRing
      ProjectiveTensorSeparationExamples.productModule).obj (ModuleCat.of
      ProjectiveTensorSeparationExamples.productRing
      ProjectiveTensorSeparationExamples.productRing) ⟶ (TopModuleCat.coefficientTensor
      ProjectiveTensorSeparationExamples.productRing
      ProjectiveTensorSeparationExamples.productModule).obj
      ProjectiveTensorSeparationExamples.firstAxisCoefficients :=
  (TopModuleCat.coefficientTensor ProjectiveTensorSeparationExamples.productRing
    ProjectiveTensorSeparationExamples.productModule).map idealCoefficientRetraction

/-- Doubling both coordinates of the whole regular product target. -/
noncomputable def idealTargetDoubling :
    ProjectiveTensorSeparationExamples.productModule ⟶
      ProjectiveTensorSeparationExamples.productModule :=
  TopModuleCat.ofHom ((2 : ProjectiveTensorSeparationExamples.productRing) •
    ContinuousLinearMap.id ProjectiveTensorSeparationExamples.productRing
    ProjectiveTensorSeparationExamples.productModule)

/-- Postcomposition of the ideal-coefficient map by whole-target doubling. -/
noncomputable def idealTargetComposite :
    (TopModuleCat.coefficientTensor ProjectiveTensorSeparationExamples.productRing
      ProjectiveTensorSeparationExamples.productModule).obj
      ProjectiveTensorSeparationExamples.firstAxisCoefficients ⟶
      ProjectiveTensorSeparationExamples.productModule :=
  idealOutgoing ≫ idealTargetDoubling

/-- Precomposition of the ideal-coefficient map by coefficient retraction. -/
noncomputable def idealCoefficientComposite :
    (TopModuleCat.coefficientTensor ProjectiveTensorSeparationExamples.productRing
      ProjectiveTensorSeparationExamples.productModule).obj (ModuleCat.of
      ProjectiveTensorSeparationExamples.productRing
      ProjectiveTensorSeparationExamples.productRing) ⟶
      ProjectiveTensorSeparationExamples.productModule :=
  idealTensorRetraction ≫ idealOutgoing

/-- The categorical continuous-map family indexed by the nonfree ideal. -/
noncomputable def idealCurried :
    ProjectiveTensorSeparationExamples.firstAxisCoefficients ⟶ ((CategoryTheory.linearCoyoneda
      ProjectiveTensorSeparationExamples.productRing (TopModuleCat.{0}
      ProjectiveTensorSeparationExamples.productRing)).obj (Opposite.op
      ProjectiveTensorSeparationExamples.productModule)).obj
      ProjectiveTensorSeparationExamples.productModule :=
  TopModuleCat.coefficientTensorHomEquiv ProjectiveTensorSeparationExamples.productRing
    ProjectiveTensorSeparationExamples.productModule
    ProjectiveTensorSeparationExamples.firstAxisCoefficients
    ProjectiveTensorSeparationExamples.productModule idealOutgoing

/-- The whole-product outgoing map recovered from its ideal-indexed family. -/
noncomputable def idealRecovered :
    (TopModuleCat.coefficientTensor ProjectiveTensorSeparationExamples.productRing
      ProjectiveTensorSeparationExamples.productModule).obj
      ProjectiveTensorSeparationExamples.firstAxisCoefficients ⟶
      ProjectiveTensorSeparationExamples.productModule :=
  (TopModuleCat.coefficientTensorHomEquiv ProjectiveTensorSeparationExamples.productRing
    ProjectiveTensorSeparationExamples.productModule
    ProjectiveTensorSeparationExamples.firstAxisCoefficients
    ProjectiveTensorSeparationExamples.productModule).symm idealCurried

/-- The rank-one outgoing map for the regular real product action. -/
noncomputable def regularOutgoing :
    (TopModuleCat.coefficientTensor (ℝ × ℝ) ScalarRestriction.realPairModule).obj
      (ModuleCat.of (ℝ × ℝ) (ℝ × ℝ)) ⟶ ScalarRestriction.realPairModule :=
  CategoryTheory.ConcreteCategory.ofHom
    (C := TopModuleCat (ℝ × ℝ))
    (X := TopModuleCat.tensorLeftObj (ℝ × ℝ)
      (ModuleCat.of (ℝ × ℝ) (ℝ × ℝ)) ScalarRestriction.realPairModule)
    (Y := ScalarRestriction.realPairModule)
    (TopModuleCat.tensorLiftCLM (ℝ × ℝ)
      (C := ModuleCat.of (ℝ × ℝ) (ℝ × ℝ))
      (M := ScalarRestriction.realPairModule) (N := ScalarRestriction.realPairModule)
      (TensorHomExamples.rankOnePairing (ℝ × ℝ)
        (M := ScalarRestriction.realPairModule) (N := ScalarRestriction.realPairModule)
        (TopModuleCat.Hom.hom (R := ℝ × ℝ)
          (X := ScalarRestriction.realPairModule) (Y := ScalarRestriction.realPairModule)
          (𝟙 ScalarRestriction.realPairModule))))

/-- Doubling within the regular real product target action. -/
noncomputable def regularTargetDoubling :
    ScalarRestriction.realPairModule ⟶ ScalarRestriction.realPairModule :=
  TopModuleCat.ofHom
    ((2 : ℝ × ℝ) • ContinuousLinearMap.id (ℝ × ℝ) ScalarRestriction.realPairModule)

/-- The regular-action outgoing map followed by target doubling. -/
noncomputable def regularTargetComposite :
    (TopModuleCat.coefficientTensor (ℝ × ℝ) ScalarRestriction.realPairModule).obj
      (ModuleCat.of (ℝ × ℝ) (ℝ × ℝ)) ⟶ ScalarRestriction.realPairModule :=
  regularOutgoing ≫ regularTargetDoubling

/-- The categorical family associated to the regular-action rank-one map. -/
noncomputable def regularCurried :
    (ModuleCat.of (ℝ × ℝ) (ℝ × ℝ)) ⟶
      ((CategoryTheory.linearCoyoneda (ℝ × ℝ) (TopModuleCat.{0} (ℝ × ℝ))).obj
        (Opposite.op ScalarRestriction.realPairModule)).obj ScalarRestriction.realPairModule :=
  TopModuleCat.coefficientTensorHomEquiv (ℝ × ℝ) ScalarRestriction.realPairModule
    (ModuleCat.of (ℝ × ℝ) (ℝ × ℝ)) ScalarRestriction.realPairModule regularOutgoing

/-- The regular-action outgoing map recovered from its categorical family. -/
noncomputable def regularRecovered :
    (TopModuleCat.coefficientTensor (ℝ × ℝ) ScalarRestriction.realPairModule).obj
      (ModuleCat.of (ℝ × ℝ) (ℝ × ℝ)) ⟶ ScalarRestriction.realPairModule :=
  (TopModuleCat.coefficientTensorHomEquiv (ℝ × ℝ) ScalarRestriction.realPairModule
    (ModuleCat.of (ℝ × ℝ) (ℝ × ℝ)) ScalarRestriction.realPairModule).symm regularCurried

/-- The rank-one outgoing map within the swapped real product action. -/
noncomputable def swappedOutgoing :
    (TopModuleCat.coefficientTensor (ℝ × ℝ) ScalarRestriction.swappedRealPair).obj
      (ModuleCat.of (ℝ × ℝ) (ℝ × ℝ)) ⟶ ScalarRestriction.swappedRealPair :=
  CategoryTheory.ConcreteCategory.ofHom
    (C := TopModuleCat (ℝ × ℝ))
    (X := TopModuleCat.tensorLeftObj (ℝ × ℝ)
      (ModuleCat.of (ℝ × ℝ) (ℝ × ℝ)) ScalarRestriction.swappedRealPair)
    (Y := ScalarRestriction.swappedRealPair)
    (TopModuleCat.tensorLiftCLM (ℝ × ℝ)
      (C := ModuleCat.of (ℝ × ℝ) (ℝ × ℝ))
      (M := ScalarRestriction.swappedRealPair) (N := ScalarRestriction.swappedRealPair)
      (TensorHomExamples.rankOnePairing (ℝ × ℝ)
        (M := ScalarRestriction.swappedRealPair) (N := ScalarRestriction.swappedRealPair)
        (TopModuleCat.Hom.hom (R := ℝ × ℝ)
          (X := ScalarRestriction.swappedRealPair) (Y := ScalarRestriction.swappedRealPair)
          (𝟙 ScalarRestriction.swappedRealPair))))

/-- Doubling within the swapped real product target action. -/
noncomputable def swappedTargetDoubling :
    ScalarRestriction.swappedRealPair ⟶ ScalarRestriction.swappedRealPair :=
  (2 : ℝ × ℝ) • (𝟙 ScalarRestriction.swappedRealPair)

/-- The swapped-action outgoing map followed by target doubling. -/
noncomputable def swappedTargetComposite :
    (TopModuleCat.coefficientTensor (ℝ × ℝ) ScalarRestriction.swappedRealPair).obj
      (ModuleCat.of (ℝ × ℝ) (ℝ × ℝ)) ⟶ ScalarRestriction.swappedRealPair :=
  swappedOutgoing ≫ swappedTargetDoubling

/-- The categorical family associated to the swapped-action rank-one map. -/
noncomputable def swappedCurried :
    (ModuleCat.of (ℝ × ℝ) (ℝ × ℝ)) ⟶
      ((CategoryTheory.linearCoyoneda (ℝ × ℝ) (TopModuleCat.{0} (ℝ × ℝ))).obj
        (Opposite.op ScalarRestriction.swappedRealPair)).obj ScalarRestriction.swappedRealPair :=
  TopModuleCat.coefficientTensorHomEquiv (ℝ × ℝ) ScalarRestriction.swappedRealPair
    (ModuleCat.of (ℝ × ℝ) (ℝ × ℝ)) ScalarRestriction.swappedRealPair swappedOutgoing

/-- The swapped-action outgoing map recovered within its own stored action. -/
noncomputable def swappedRecovered :
    (TopModuleCat.coefficientTensor (ℝ × ℝ) ScalarRestriction.swappedRealPair).obj
      (ModuleCat.of (ℝ × ℝ) (ℝ × ℝ)) ⟶ ScalarRestriction.swappedRealPair :=
  (TopModuleCat.coefficientTensorHomEquiv (ℝ × ℝ) ScalarRestriction.swappedRealPair
    (ModuleCat.of (ℝ × ℝ) (ℝ × ℝ)) ScalarRestriction.swappedRealPair).symm swappedCurried

end CoefficientTensorExamples
