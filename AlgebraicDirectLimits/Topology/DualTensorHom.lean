/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicDirectLimits.Topology.TensorHom
public import AlgebraicDirectLimits.Topology.StrongDual
public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

/-!
# Continuous dual tensors and linear maps

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
hypothesis is needed for the forward map.

When `E` is finite-dimensional and has its module topology,
`TopModuleCat.dualTensorHomEquiv` is a continuous linear equivalence with this
same forward map. Its inverse in any finite basis is the sum of the continuous
coordinate forms tensored with the operator values. The original topologies
are retained; no norm on `E` or `G`, completeness or separation is required.

## Implementation notes

For a fixed functional `φ`, Mathlib's `ContinuousLinearMap.precomp` composed with
`ContinuousLinearMap.toSpanSingletonCLE` gives the continuous family
`v ↦ (w ↦ φ w • v)`. The existing `TopModuleCat.tensorLiftCLM` extends this
family. Precomposition preserves bounded convergence because continuous linear
maps send bounded sets to bounded sets; no continuity of evaluation on `E` is used.

For the finite-left equivalence, the module topology on `E` identifies its
continuous dual with its algebraic dual. Mathlib's algebraic contraction supplies
bijectivity. Each summand of the inverse is an existing continuous fixed-left
tensor generator after evaluation at a basis vector, so the inverse is continuous
for bounded convergence even when the right module is not normed. Empty bases
are allowed.

## References

The algebraic contraction is Mathlib's construction by Oliver Nash and Antoine
Labelle in `Mathlib.LinearAlgebra.Contraction`. The bounded-convergence topology,
precomposition and scalar-line maps are Mathlib's development by Anatole Dedecker
and Yury Kudryashov in
`Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap`.
The continuous constructions follow Formal Frontier Agents' dual-tensor
formalization, including the finite-evaluation inverse-continuity argument,
using their one-sided tensor topology and universal property in
`AlgebraicDirectLimits.Topology.TensorProduct` and `TensorHom`. The coordinate
forms use Kevin Buzzard and Will Sawin's module-topology automatic-continuity API.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

universe uK uE₁ uE₂

namespace TopModuleCat

section Forward

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

end Forward

section FiniteLeft

variable (𝕜 : Type uK) [NontriviallyNormedField 𝕜]
variable (E : Type uE₁) [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
variable [IsModuleTopology 𝕜 E]
variable (G : Type uE₂) [AddCommGroup G] [Module 𝕜 G] [TopologicalSpace G]
variable [IsTopologicalAddGroup G] [ContinuousSMul 𝕜 G]

/-- For a finite-dimensional left space with its module topology, the continuous
forward map is bijective. This follows from algebraic dual–tensor contraction by
identifying continuous and algebraic duals. -/
theorem dualTensorHom_bijective [FiniteDimensional 𝕜 E] :
    Function.Bijective (dualTensorHom 𝕜 E G) := by
  let c : StrongDual 𝕜 E ≃ₗ[𝕜] Module.Dual 𝕜 E :=
    LinearEquiv.ofBijective (ContinuousLinearMap.coeLM 𝕜)
      ⟨ContinuousLinearMap.coe_injective,
        fun f ↦ ⟨⟨f, IsModuleTopology.continuous_of_linearMap f⟩, rfl⟩⟩
  have h : Function.Bijective
      ((ContinuousLinearMap.coeLM 𝕜).comp (dualTensorHom 𝕜 E G).toLinearMap) := by
    rw [dualTensorHom_toLinearMap]
    exact (_root_.dualTensorHomEquiv 𝕜 E G).bijective.comp
      (TensorProduct.congr c (LinearEquiv.refl 𝕜 G)).bijective
  exact Function.Bijective.of_comp_left
    (f := ContinuousLinearMap.coeLM 𝕜) (g := dualTensorHom 𝕜 E G) h
    ContinuousLinearMap.coe_injective

variable {ι : Type*} [Fintype ι]

-- Each summand is a continuous fixed-left tensor generator after evaluation.
private def dualTensorHomInverseOfBasis (e : Module.Basis ι 𝕜 E) :
    (E →L[𝕜] G) →L[𝕜]
      TopModuleCat.tensorLeftObj 𝕜 (ModuleCat.of 𝕜 (StrongDual 𝕜 E))
        (TopModuleCat.of 𝕜 G) :=
  ∑ i, (TopModuleCat.tensorGenerator 𝕜 (ModuleCat.of 𝕜 (StrongDual 𝕜 E))
    (TopModuleCat.of 𝕜 G)
    ⟨e.coord i, IsModuleTopology.continuous_of_linearMap (e.coord i)⟩).comp
      { toLinearMap := (LinearMap.applyₗ (e i)).comp (ContinuousLinearMap.coeLM 𝕜)
        cont := continuous_eval_const (e i) }

private theorem dualTensorHomInverseOfBasis_apply (e : Module.Basis ι 𝕜 E)
    (A : E →L[𝕜] G) :
    dualTensorHomInverseOfBasis 𝕜 E G e A =
      ∑ i, (show TopModuleCat.tensorLeftObj 𝕜 (ModuleCat.of 𝕜 (StrongDual 𝕜 E))
        (TopModuleCat.of 𝕜 G) from
        (⟨e.coord i, IsModuleTopology.continuous_of_linearMap (e.coord i)⟩ :
          StrongDual 𝕜 E) ⊗ₜ[𝕜] A (e i)) := by
  simp only [dualTensorHomInverseOfBasis, sum_apply, ContinuousLinearMap.comp_apply]
  apply Finset.sum_congr rfl
  intro i _
  rfl

private theorem dualTensorHom_inverseOfBasis (e : Module.Basis ι 𝕜 E)
    (A : E →L[𝕜] G) :
    dualTensorHom 𝕜 E G (dualTensorHomInverseOfBasis 𝕜 E G e A) = A := by
  classical
  apply ContinuousLinearMap.ext
  intro w
  rw [dualTensorHomInverseOfBasis_apply, map_sum]
  calc
    _ = ∑ i, e.coord i w • A (e i) := by
      rw [sum_apply]
      apply Finset.sum_congr rfl
      intro i _
      exact dualTensorHom_tmul 𝕜 E G
        ⟨e.coord i, IsModuleTopology.continuous_of_linearMap (e.coord i)⟩ (A (e i)) w
    _ = A (∑ i, e.repr w i • e i) := by
      simp only [map_sum, map_smul, Module.Basis.coord_apply]
    _ = A w := congrArg A (e.sum_repr w)

variable [FiniteDimensional 𝕜 E]

/-- The finite-left continuous dual–tensor Hom equivalence for the one-sided tensor
and bounded-convergence topologies. Its forward map is `dualTensorHom`; its inverse
is the finite sum of coordinate forms tensored with operator values. The bijectivity
uses Mathlib's algebraic `dualTensorHomEquiv`, and inverse continuity follows from
continuous evaluation and the fixed-left tensor generators. No norm on either
module or completeness of the scalar field is required. -/
@[no_expose]
def dualTensorHomEquiv :
    TopModuleCat.tensorLeftObj 𝕜 (ModuleCat.of 𝕜 (StrongDual 𝕜 E))
      (TopModuleCat.of 𝕜 G) ≃L[𝕜] (E →L[𝕜] G) := by
  let f := dualTensorHom 𝕜 E G
  have hf := dualTensorHom_bijective 𝕜 E G
  refine { LinearEquiv.ofBijective f.toLinearMap hf with
    continuous_toFun := f.continuous
    continuous_invFun := ?_ }
  let e := Module.finBasis 𝕜 E
  have h (A : E →L[𝕜] G) : (LinearEquiv.ofBijective f.toLinearMap hf).symm A =
      dualTensorHomInverseOfBasis 𝕜 E G e A := by
    apply hf.injective
    exact (LinearEquiv.apply_symm_apply (LinearEquiv.ofBijective f.toLinearMap hf) A).trans
      (dualTensorHom_inverseOfBasis 𝕜 E G e A).symm
  exact (dualTensorHomInverseOfBasis 𝕜 E G e).continuous.congr (fun A ↦ (h A).symm)

/-- The equivalence has exactly the existing continuous forward contraction. -/
@[simp]
theorem dualTensorHomEquiv_toContinuousLinearMap :
    (dualTensorHomEquiv 𝕜 E G).toContinuousLinearMap =
      dualTensorHom 𝕜 E G := (rfl)

/-- Applying the equivalence agrees with the continuous forward contraction. -/
@[simp]
theorem dualTensorHomEquiv_apply
    (z : TopModuleCat.tensorLeftObj 𝕜 (ModuleCat.of 𝕜 (StrongDual 𝕜 E))
      (TopModuleCat.of 𝕜 G)) :
    dualTensorHomEquiv 𝕜 E G z = dualTensorHom 𝕜 E G z := by
  exact congrArg (fun f ↦ f z) (dualTensorHomEquiv_toContinuousLinearMap 𝕜 E G)

/-- Pure tensors correspond to rank-one operators. -/
@[simp]
theorem dualTensorHomEquiv_tmul (φ : StrongDual 𝕜 E) (v : G) (w : E) :
    dualTensorHomEquiv 𝕜 E G (φ ⊗ₜ[𝕜] v) w = φ w • v := by
  exact (congrArg (fun A : E →L[𝕜] G ↦ A w)
    (dualTensorHomEquiv_apply 𝕜 E G (φ ⊗ₜ[𝕜] v))).trans
      (dualTensorHom_tmul 𝕜 E G φ v w)

/-- The inverse recovers a tensor from its continuous contraction. -/
@[simp]
theorem dualTensorHomEquiv_symm_dualTensorHom
    (z : TopModuleCat.tensorLeftObj 𝕜 (ModuleCat.of 𝕜 (StrongDual 𝕜 E))
      (TopModuleCat.of 𝕜 G)) :
    (dualTensorHomEquiv 𝕜 E G).symm (dualTensorHom 𝕜 E G z) = z := by
  rw [← dualTensorHomEquiv_apply, ContinuousLinearEquiv.symm_apply_apply]

/-- Contracting the inverse tensor recovers the operator. -/
@[simp]
theorem dualTensorHom_dualTensorHomEquiv_symm (A : E →L[𝕜] G) :
    dualTensorHom 𝕜 E G ((dualTensorHomEquiv 𝕜 E G).symm A) = A := by
  rw [← dualTensorHomEquiv_apply, ContinuousLinearEquiv.apply_symm_apply]

/-- In any finite basis, the inverse is the finite tensor sum of continuous
coordinate forms and operator values. Empty bases are allowed. -/
theorem dualTensorHomEquiv_symm_apply (e : Module.Basis ι 𝕜 E) (A : E →L[𝕜] G) :
    (dualTensorHomEquiv 𝕜 E G).symm A =
      ∑ i, (show TopModuleCat.tensorLeftObj 𝕜 (ModuleCat.of 𝕜 (StrongDual 𝕜 E))
        (TopModuleCat.of 𝕜 G) from
        (⟨e.coord i, IsModuleTopology.continuous_of_linearMap (e.coord i)⟩ :
          StrongDual 𝕜 E) ⊗ₜ[𝕜] A (e i)) := by
  apply (dualTensorHomEquiv 𝕜 E G).injective
  calc
    dualTensorHomEquiv 𝕜 E G ((dualTensorHomEquiv 𝕜 E G).symm A) = A :=
      (dualTensorHomEquiv 𝕜 E G).apply_symm_apply A
    _ = dualTensorHom 𝕜 E G (dualTensorHomInverseOfBasis 𝕜 E G e A) :=
      (dualTensorHom_inverseOfBasis 𝕜 E G e A).symm
    _ = dualTensorHomEquiv 𝕜 E G
        (∑ i, (show TopModuleCat.tensorLeftObj 𝕜 (ModuleCat.of 𝕜 (StrongDual 𝕜 E))
          (TopModuleCat.of 𝕜 G) from
          (⟨e.coord i, IsModuleTopology.continuous_of_linearMap (e.coord i)⟩ :
            StrongDual 𝕜 E) ⊗ₜ[𝕜] A (e i))) := by
      rw [dualTensorHomInverseOfBasis_apply, dualTensorHomEquiv_apply]

/-- The inverse of the algebraic equivalence underlying continuous dual–tensor
contraction is continuous for the one-sided tensor topology and bounded convergence. -/
theorem continuous_dualTensorHom_inverse :
    Continuous (LinearEquiv.ofBijective (dualTensorHom 𝕜 E G).toLinearMap
      (dualTensorHom_bijective 𝕜 E G)).symm := by
  let e := dualTensorHomEquiv 𝕜 E G
  have he : e.toLinearEquiv = LinearEquiv.ofBijective (dualTensorHom 𝕜 E G).toLinearMap
      (dualTensorHom_bijective 𝕜 E G) := by
    apply LinearEquiv.toLinearMap_injective
    exact congrArg ContinuousLinearMap.toLinearMap
      (dualTensorHomEquiv_toContinuousLinearMap 𝕜 E G)
  exact e.symm.continuous.congr (fun A ↦
    congrArg (fun g : StrongDual 𝕜 E ⊗[𝕜] G ≃ₗ[𝕜] (E →L[𝕜] G) ↦ g.symm A) he)

end FiniteLeft

end TopModuleCat
