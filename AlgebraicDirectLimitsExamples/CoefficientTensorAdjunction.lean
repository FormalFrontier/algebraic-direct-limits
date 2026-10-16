/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicDirectLimitsExamples.CoefficientTensor
public import Mathlib.Algebra.Category.ModuleCat.Biproducts

/-!
# Coefficient-tensor adjunction on integer endomorphisms

The coefficient module is the existing categorical continuous endomorphism module
of the integers. The counit evaluates the tensor of the identity endomorphism and
`1` to `1`. The coefficient tensor sends the canonical binary coproduct cocone on
two copies of this coefficient module to a colimit cocone.

The integer model is supplied by `AlgebraicDirectLimitsExamples.CoefficientTensor`;
the binary biproduct and colimit-preservation interfaces are those of Mathlib.
-/

@[expose] public section

open CategoryTheory

namespace CoefficientTensorHomInteger

/-- The counit has value `1` on the tensor of the identity endomorphism and `1`. -/
example :
    ((TopModuleCat.coefficientTensorAdjunction ℤ M).counit.app M).hom t =
      (1 : ℤ) := by
  have hc : (TopModuleCat.coefficientTensorAdjunction ℤ M).counit.app M = f := by
    rw [← Adjunction.homEquiv_symm_id,
      TopModuleCat.coefficientTensorAdjunction_homEquiv]
    rfl
  rw [hc]
  exact data_values.2.2.1

noncomputable section

/-- The canonical binary coproduct of two endomorphism coefficient modules is preserved. -/
example :
    CategoryTheory.Limits.IsColimit
      (F.mapCocone
        ((CategoryTheory.Limits.BinaryBiproduct.bicone C C).toCocone)) := by
  exact CategoryTheory.Limits.isColimitOfPreserves F
    (CategoryTheory.Limits.BinaryBiproduct.isColimit C C)

end

end CoefficientTensorHomInteger
