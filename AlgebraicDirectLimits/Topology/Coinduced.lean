/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Topology.Basic

/-!
# Linear maps out of coinduced topological modules

A linear map from `TopModuleCat.coinduced j` is continuous exactly when its
composite with every generating map is continuous. The target may have a
carrier universe different from that of the generating modules.

This is a property of linear maps, not a final-topology property for arbitrary
functions: `TopModuleCat.coinduced` is the finest *topological-module* topology
making the generators continuous.

## References

The proof follows the induced-topology argument for `TopModuleCat.isColimit`
in Mathlib's `Algebra.Category.ModuleCat.Topology.Basic`, by Richard Hill and
Andrew Yang. It uses their existing coinduced construction and its generating
maps, rather than constructing another topology.
-/

@[expose] public section

universe uR uC uI uY

open CategoryTheory

namespace TopModuleCat

variable {R : Type uR} [Ring R] [TopologicalSpace R]
variable {A : ModuleCat.{uC} R} {I : Type uI} {X : I → TopModuleCat.{uC} R}
variable (j : ∀ i, (X i).toModuleCat ⟶ A)

/-- A generating morphism into the coinduced module retains the given linear map. -/
@[simp]
theorem toCoinduced_apply (i : I) (x : X i) : toCoinduced j i x = j i x := rfl

/-- A linear map out of the coinduced topological module is continuous if and only
if its composites with all generating linear maps are continuous. The index type
may be empty, and the target has an independent carrier universe. -/
theorem continuous_coinduced_iff {Y : TopModuleCat.{uY} R}
    (f : coinduced j →ₗ[R] Y) :
    Continuous f ↔ ∀ i, Continuous (fun x : X i ↦ f (j i x)) := by
  constructor
  · intro hf i
    simpa only [Function.comp_def, toCoinduced_apply] using
      hf.comp (toCoinduced j i).hom.continuous
  · intro h
    -- The induced topology is on the unchanged underlying module A.
    let f' : A →ₗ[R] Y := f
    rw [continuous_iff_le_induced]
    change sInf _ ≤ TopologicalSpace.induced (f' : A → Y) _
    refine sInf_le ⟨continuousSMul_induced (M₂ := Y) f',
      continuousAdd_induced (N := Y) f', fun i ↦ ?_⟩
    apply Continuous.coinduced_le
    exact continuous_induced_rng.mpr (h i)

end TopModuleCat
