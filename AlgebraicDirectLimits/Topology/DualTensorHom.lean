/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicDirectLimits.Topology.TensorHom
public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

/-!
# Continuous dual tensor contraction

`TopModuleCat.dualTensorHom` sends `φ ⊗ₜ v` to the rank-one operator
`w ↦ φ w • v`. The source has the existing one-sided tensor topology, with
`StrongDual 𝕜 E` as its algebraic coefficient module. The target `E →L[𝕜] G`
has Mathlib's topology of uniform convergence on bounded sets. Forgetting
continuity agrees with Mathlib's algebraic `dualTensorHom` after forgetting
continuity of the functionals.

The scalar field is nontrivially normed. The original space `E` only needs an
additive group, a module structure and a topology; continuity of its addition
or scalar action is not required. The right module `G` has continuous addition
and jointly continuous scalar multiplication. The scalar and carrier universes
are independent. No finiteness, norm on either module, completeness or separation
hypothesis is needed. This module constructs only the forward map, not an inverse.

## Implementation notes

For a fixed functional `φ`, Mathlib's `ContinuousLinearMap.precomp` composed with
`ContinuousLinearMap.toSpanSingletonCLE` gives the continuous family
`v ↦ (w ↦ φ w • v)`. The existing `TopModuleCat.tensorLiftCLM` extends this
family. Precomposition preserves bounded convergence because continuous linear
maps send bounded sets to bounded sets; no continuity of evaluation on `E` is used.

## References

The algebraic contraction is Mathlib's construction by Oliver Nash and Antoine
Labelle in `Mathlib.LinearAlgebra.Contraction`. The bounded-convergence topology,
precomposition and scalar-line maps are Mathlib's development by Anatole Dedecker
and Yury Kudryashov in
`Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap`.
The continuous forward construction follows Formal Frontier Agents' dual-tensor
formalization, using their one-sided tensor topology and universal property in
`AlgebraicDirectLimits.Topology.TensorProduct` and `TensorHom`.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

universe uK uE₁ uE₂

namespace TopModuleCat

variable (𝕜 : Type uK) [NontriviallyNormedField 𝕜]
variable (E : Type uE₁) [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
variable (G : Type uE₂) [AddCommGroup G] [Module 𝕜 G] [TopologicalSpace G]
variable [IsTopologicalAddGroup G] [ContinuousSMul 𝕜 G]

/-- The continuous forward dual–tensor Hom map, for the one-sided tensor topology
and the bounded-convergence Hom topology. It lifts Mathlib's `ContinuousLinearMap.precomp`
and `ContinuousLinearMap.toSpanSingletonCLE` using `TopModuleCat.tensorLiftCLM`.
No finiteness is needed. -/
def dualTensorHom :
    TopModuleCat.tensorLeftObj 𝕜 (ModuleCat.of 𝕜 (StrongDual 𝕜 E))
      (TopModuleCat.of 𝕜 G) →L[𝕜] (E →L[𝕜] G) :=
  TopModuleCat.tensorLiftCLM 𝕜
    (C := ModuleCat.of 𝕜 (StrongDual 𝕜 E)) (M := TopModuleCat.of 𝕜 G)
    (N := TopModuleCat.of 𝕜 (E →L[𝕜] G))
    { toFun := fun φ ↦
        (φ.precomp G).comp ContinuousLinearMap.toSpanSingletonCLE.toContinuousLinearMap
      map_add' := by intro φ ψ; ext v w; simp
      map_smul' := by intro a φ; ext v w; simp [smul_smul] }

/-- The forward map has the canonical rank-one operator formula. -/
@[simp]
theorem dualTensorHom_tmul (φ : StrongDual 𝕜 E) (v : G) (w : E) :
    dualTensorHom 𝕜 E G (φ ⊗ₜ[𝕜] v) w = φ w • v := by
  rw [dualTensorHom, TopModuleCat.tensorLiftCLM_tmul]
  rfl

/-- Forgetting continuity commutes with Mathlib's algebraic `dualTensorHom`. -/
theorem dualTensorHom_toLinearMap :
    (ContinuousLinearMap.coeLM 𝕜).comp (dualTensorHom 𝕜 E G).toLinearMap =
      (_root_.dualTensorHom 𝕜 E G).comp
        (TensorProduct.map (ContinuousLinearMap.coeLM 𝕜) (LinearMap.id : G →ₗ[𝕜] G)) := by
  apply TensorProduct.ext'
  intro φ v
  apply LinearMap.ext
  intro w
  change (dualTensorHom 𝕜 E G (φ ⊗ₜ[𝕜] v)) w = φ w • v
  exact dualTensorHom_tmul 𝕜 E G φ v w

end TopModuleCat
