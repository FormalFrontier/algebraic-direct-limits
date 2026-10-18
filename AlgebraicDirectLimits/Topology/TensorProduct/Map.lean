/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicDirectLimits.Topology.TensorProduct

/-!
# Joint continuity of varying tensor maps

For independently based finite algebraic coefficient modules, continuity of each
matrix coefficient of a varying left map and joint continuity of right evaluation
imply joint continuity of `TopModuleCat.tensorMapCLM` on the parameter and the
whole tensor input. The right modules retain their given topologies and need not
be finite-dimensional or normed. No topology on a morphism space is used.

`TopModuleCat.tensorCoordinateContinuousLinearEquiv_tensorMapCLM_apply` expresses
the tensor map in the existing finite-product coordinates. Source and target
bases can have different index types and different ranks. The finite sum needs
`Fintype` only for its source index; the continuity statement uses `Finite` for
both indices.

## References

The finite-coordinate argument follows Formal Frontier Agents' tensor-coordinate
and joint tensor-transition developments. The one-sided tensor topology and
continuous tensor maps are reused from `AlgebraicDirectLimits.Topology.TensorProduct`.
Mathlib's tensor-basis equivalences are due to Jakob von Raumer, its tensor-map
API to Kenny Lau and Mario Carneiro, and its Finsupp API to Johannes Hölzl.
The topological-module category is due to Richard Hill and Andrew Yang. This
module is an original Formal Frontier contribution developed with AI assistance.
-/

@[expose] public section

open scoped TensorProduct

universe uR uX uC uD uM uN uI uJ

namespace TopModuleCat

variable (R : Type uR) [CommRing R] [TopologicalSpace R]
variable {C : ModuleCat.{uC} R} {D : ModuleCat.{uD} R}
variable {M : TopModuleCat.{uM} R} {N : TopModuleCat.{uN} R}
variable {I : Type uI} {J : Type uJ}

/-- In finite-basis coordinates, the tensor map is the sum of the images of the
source coordinates weighted by the matrix coefficients of its left map. The
coordinate equivalences are the existing one-sided tensor coordinates. -/
theorem tensorCoordinateContinuousLinearEquiv_tensorMapCLM_apply
    [Fintype I] [Finite J] (bC : Module.Basis I R C) (bD : Module.Basis J R D)
    (f : C →ₗ[R] D) (g : M →L[R] N) (z : tensorLeftObj R C M) (j : J) :
    tensorCoordinateContinuousLinearEquiv R D N bD (tensorMapCLM R f g z) j =
      ∑ i, bD.repr (f (bC i)) j •
        g (tensorCoordinateContinuousLinearEquiv R C M bC z i) := by
  classical
  have hz : z = ∑ i, tensorGenerator R C M (bC i)
      (tensorCoordinateContinuousLinearEquiv R C M bC z i) := by
    calc
      z = (tensorCoordinateContinuousLinearEquiv R C M bC).symm
          (tensorCoordinateContinuousLinearEquiv R C M bC z) :=
        ((tensorCoordinateContinuousLinearEquiv R C M bC).symm_apply_apply z).symm
      _ = _ := tensorCoordinateContinuousLinearEquiv_symm_apply R C M bC _
  calc
    _ = tensorCoordinateContinuousLinearEquiv R D N bD
        (tensorMapCLM R f g (∑ i, tensorGenerator R C M (bC i)
          (tensorCoordinateContinuousLinearEquiv R C M bC z i))) j :=
      congrArg (fun w : tensorLeftObj R C M ↦
        tensorCoordinateContinuousLinearEquiv R D N bD (tensorMapCLM R f g w) j) hz
    _ = _ := by
      simp only [map_sum, Finset.sum_apply, tensorMapCLM_tensorGenerator_apply,
        tensorCoordinateContinuousLinearEquiv_tensorGenerator_apply]

/-- Joint continuity of tensor-map evaluation follows from coefficientwise
continuity on the finite left factors and joint evaluation continuity on the
right factors. It holds on every tensor, not only on pure tensors, and makes no
operator-space continuity assumption. The algebraic left factors carry no topology. -/
theorem continuous_tensorMapCLM_apply
    {X : Type uX} [TopologicalSpace X] [Finite I] [Finite J]
    (bC : Module.Basis I R C) (bD : Module.Basis J R D)
    (f : X → C →ₗ[R] D) (g : X → M →L[R] N)
    (hF : ∀ i j, Continuous (fun x : X ↦ bD.repr (f x (bC i)) j))
    (hG : Continuous (fun p : X × M ↦ g p.1 p.2)) :
    Continuous (fun p : X × tensorLeftObj R C M ↦
      tensorMapCLM R (f p.1) (g p.1) p.2) := by
  classical
  let : Fintype I := Fintype.ofFinite I
  apply (tensorCoordinateContinuousLinearEquiv R D N bD).comp_continuous_iff.mp
  apply continuous_pi
  intro j
  have hsum : Continuous (fun p : X × tensorLeftObj R C M ↦
      ∑ i, bD.repr (f p.1 (bC i)) j •
        g p.1 (tensorCoordinateContinuousLinearEquiv R C M bC p.2 i)) := by
    apply continuous_finsetSum
    intro i _
    exact ((hF i j).comp continuous_fst).smul
      (hG.comp (continuous_fst.prodMk
        (((continuous_apply i).comp
          (tensorCoordinateContinuousLinearEquiv R C M bC).continuous).comp continuous_snd)))
  exact hsum.congr (fun p ↦
    (tensorCoordinateContinuousLinearEquiv_tensorMapCLM_apply R bC bD
      (f p.1) (g p.1) p.2 j).symm)

end TopModuleCat
