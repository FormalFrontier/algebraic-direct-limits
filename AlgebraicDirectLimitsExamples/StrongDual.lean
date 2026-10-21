/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicDirectLimits
public import Mathlib.Analysis.Normed.Field.Lemmas

/-!
# Strong duals over incomplete fields

Every linear form on the strong dual of the rational plane is continuous for the
existing bounded-convergence topology. The rational plane has its usual product
topology; neither it nor its dual is given a replacement topology.

The empty rational product supplies the dimension-zero boundary. Over complete
nontrivially normed fields, the new theorem and Mathlib's general finite-dimensional
result prove the same proposition for the same strong-dual topology, so their
proofs agree by proof irrelevance.
-/

@[expose] public section

namespace AlgebraicDirectLimitsExamples.StrongDual

/-- Linear forms on the strong dual of the usual rational plane are continuous,
even though the scalar field is incomplete. -/
theorem rationalPlane_linear_continuous
    (l : StrongDual ℚ (Fin 2 → ℚ) →ₗ[ℚ] ℚ) : Continuous l := by
  let := IsModuleTopology.strongDual ℚ (Fin 2 → ℚ)
  exact IsModuleTopology.continuous_of_linearMap l

/-- The theorem includes the dual of the zero-dimensional rational space. -/
theorem rationalZero : IsModuleTopology ℚ (StrongDual ℚ (Fin 0 → ℚ)) :=
  IsModuleTopology.strongDual ℚ (Fin 0 → ℚ)

/-- Under the common complete-field hypotheses, both results certify the same
module topology on the same continuous dual, with no dictionary conversion. -/
theorem completeField_agreement
    (𝕜 : Type*) [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    (E : Type*) [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
    [FiniteDimensional 𝕜 E] [IsModuleTopology 𝕜 E] :
    IsModuleTopology.strongDual 𝕜 E =
      (isModuleTopologyOfFiniteDimensional (𝕜 := 𝕜) (E := StrongDual 𝕜 E)) :=
  Subsingleton.elim _ _

end AlgebraicDirectLimitsExamples.StrongDual
