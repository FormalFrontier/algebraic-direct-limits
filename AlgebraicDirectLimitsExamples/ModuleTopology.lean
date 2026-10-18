/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicDirectLimits.Topology.ModuleTopology
public import Mathlib.Topology.Algebra.Ring.Real

/-!
# The real coordinate axis and the zero-dimensional boundary

The usual inclusion of the real line into the first coordinate of the real plane
is continuous and injective, with proper image witnessed by `(0, 1)`. The module-
topology and embedding theorems apply to this map with the usual real and product
topologies. The same target also receives the unique map from `Fin 0 → ℝ`.

The continuity, injectivity and target module-topology witnesses are proved from
Mathlib independently of the target-semisimple injection theorems and their
semisimple-ring corollaries. Both forms are used explicitly on the same two maps,
rather than using an instance for source module topology. No carrier, topology or
module structure is replaced.

## References

These examples use Mathlib's product linear maps and real topological-ring
instances, together with its module-topology instances for scalars and products.
-/

@[expose] public section

namespace AlgebraicDirectLimitsExamples.ModuleTopology

/-- The ordinary first-axis map is continuous and injective into a module-topology
real plane, and `(0, 1)` does not lie in its image. -/
theorem realAxis_properties :
    Continuous (LinearMap.inl ℝ ℝ ℝ) ∧
      Function.Injective (LinearMap.inl ℝ ℝ ℝ) ∧
      IsModuleTopology ℝ (ℝ × ℝ) ∧
      (0, 1) ∉ (LinearMap.inl ℝ ℝ ℝ).range := by
  refine ⟨?_, LinearMap.inl_injective, inferInstance, ?_⟩
  · change Continuous (fun x : ℝ ↦ (x, (0 : ℝ)))
    exact continuous_id.prodMk continuous_const
  · rintro ⟨x, hx⟩
    exact zero_ne_one (congrArg Prod.snd hx)

/-- The zero-dimensional source maps continuously and injectively into the same
real plane, whose given product topology is the module topology. -/
theorem realZero_properties :
    Continuous (0 : (Fin 0 → ℝ) →ₗ[ℝ] ℝ × ℝ) ∧
      Function.Injective (0 : (Fin 0 → ℝ) →ₗ[ℝ] ℝ × ℝ) ∧
      IsModuleTopology ℝ (ℝ × ℝ) := by
  refine ⟨?_, ?_, inferInstance⟩
  · change Continuous (fun _ : Fin 0 → ℝ ↦ (0 : ℝ × ℝ))
    exact continuous_const
  · intro x y _
    exact Subsingleton.elim x y

/-- The first-axis injection gives the usual real line its module topology. -/
theorem realAxis_isModuleTopology : IsModuleTopology ℝ ℝ :=
  IsModuleTopology.of_continuous_injective (LinearMap.inl ℝ ℝ ℝ)
    realAxis_properties.1 realAxis_properties.2.1

/-- The first-axis injection is an embedding by the general linear injection API. -/
theorem realAxis_isEmbedding : Topology.IsEmbedding (LinearMap.inl ℝ ℝ ℝ) :=
  LinearMap.isEmbedding_of_isModuleTopology (LinearMap.inl ℝ ℝ ℝ)
    realAxis_properties.1 realAxis_properties.2.1

/-- The same module-topology theorem includes the zero-dimensional real source. -/
theorem realZero_isModuleTopology : IsModuleTopology ℝ (Fin 0 → ℝ) :=
  IsModuleTopology.of_continuous_injective (0 : (Fin 0 → ℝ) →ₗ[ℝ] ℝ × ℝ)
    realZero_properties.1 realZero_properties.2.1

/-- The unique map from the zero-dimensional source embeds into the real plane. -/
theorem realZero_isEmbedding :
    Topology.IsEmbedding (0 : (Fin 0 → ℝ) →ₗ[ℝ] ℝ × ℝ) :=
  LinearMap.isEmbedding_of_isModuleTopology (0 : (Fin 0 → ℝ) →ₗ[ℝ] ℝ × ℝ)
    realZero_properties.1 realZero_properties.2.1

/-- The semisimple-ring corollary gives the usual real line its module topology
from the first-axis injection as well. -/
theorem realAxis_isModuleTopology_of_isSemisimpleRing : IsModuleTopology ℝ ℝ :=
  IsModuleTopology.of_continuous_injective_of_isSemisimpleRing (LinearMap.inl ℝ ℝ ℝ)
    realAxis_properties.1 realAxis_properties.2.1

/-- The semisimple-ring embedding corollary applies to the same first-axis map. -/
theorem realAxis_isEmbedding_of_isSemisimpleRing :
    Topology.IsEmbedding (LinearMap.inl ℝ ℝ ℝ) :=
  LinearMap.isEmbedding_of_isModuleTopology_of_isSemisimpleRing (LinearMap.inl ℝ ℝ ℝ)
    realAxis_properties.1 realAxis_properties.2.1

/-- The semisimple-ring module-topology corollary includes the same zero-dimensional
real source. -/
theorem realZero_isModuleTopology_of_isSemisimpleRing :
    IsModuleTopology ℝ (Fin 0 → ℝ) :=
  IsModuleTopology.of_continuous_injective_of_isSemisimpleRing
    (0 : (Fin 0 → ℝ) →ₗ[ℝ] ℝ × ℝ) realZero_properties.1 realZero_properties.2.1

/-- The semisimple-ring embedding corollary includes the unique map from the
zero-dimensional source into the same real plane. -/
theorem realZero_isEmbedding_of_isSemisimpleRing :
    Topology.IsEmbedding (0 : (Fin 0 → ℝ) →ₗ[ℝ] ℝ × ℝ) :=
  LinearMap.isEmbedding_of_isModuleTopology_of_isSemisimpleRing
    (0 : (Fin 0 → ℝ) →ₗ[ℝ] ℝ × ℝ) realZero_properties.1 realZero_properties.2.1

end AlgebraicDirectLimitsExamples.ModuleTopology
