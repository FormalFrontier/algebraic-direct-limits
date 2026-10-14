/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicDirectLimits.Topology.TensorSeparation
public import AlgebraicDirectLimitsExamples.TensorProduct
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Topology.Algebra.Group.ZPow
public import Mathlib.Topology.Instances.ZMod

/-!
# Finite-basis tensor separation examples

The coefficient module is the existing integer-pair model, with its
`Module.Basis.finTwoProd ℤ` basis and proper diagonal integer algebra map.
The right factor `ZMod 3` has its usual discrete topology and canonical joint
integer action. It is not free as an integer module. Continuous coordinates
detect a nonzero pure tensor and a mixed sum with coordinates `![1, 2]`.
Right doubling moves the pure tensor. The two Hausdorff preservation statements
supply disjoint open neighborhoods of distinct tensors.

The existing integer right factor supplies a noncompact Hausdorff example.
An explicit `Fin 0` basis gives a Hausdorff tensor for every right factor,
including the existing indiscrete integer module, which is not Hausdorff.
Trivial scalar rings also give singleton tensors; a supplied basis may still
have a nonempty index. A polymorphic separation consumer keeps the scalar,
coefficient, right-factor and basis-index universes independent.

## Limitations

The preservation consumers use supplied-basis and projective statements in
`AlgebraicDirectLimits.Topology.TensorSeparation`, specializing them to the
finite models above. Coordinate calculations,
nonfreeness and the singleton boundaries do not assume tensor Hausdorffness.
No compactness preservation or general Hausdorffness reflection is asserted.

## References

The integer-pair models and their characteristic coordinate and generator API
are from `AlgebraicDirectLimitsExamples.TensorProduct`, by Formal Frontier
Agents. Mathlib's `ZMod` topology is due to David Loeffler; its algebraic API is
due to Chris Hughes. Its integer-module API is due to Nathaniel Thomas,
Jeremy Avigad, Johannes Hölzl and Mario Carneiro. Integer-action continuity is
due to Johannes Hölzl, Mario Carneiro and Patrick Massot. The free-module API
is due to Riccardo Brasca, and the torsion-free API to Yaël Dillies. The
finite-basis API is due to Johannes Hölzl, Mario Carneiro, Alexander Bentkamp
and Kevin H. Wilson. The separation and subsingleton-topology APIs are due to
Johannes Hölzl and Mario Carneiro.
-/

@[expose] public section

open scoped TensorProduct

universe uR uC uM uι

namespace TensorSeparationExamples

open TensorProductExamples (integerPairCoefficients integerModule)

/-- The discrete residue module with its canonical integer action. -/
abbrev residueModule : TopModuleCat ℤ := TopModuleCat.of ℤ (ZMod 3)

local notation "residueTensor" =>
  TopModuleCat.tensorLeftObj ℤ integerPairCoefficients residueModule
local notation "residueCoordinates" =>
  TopModuleCat.tensorCoordinateContinuousLinearEquiv ℤ
    integerPairCoefficients residueModule (Module.Basis.finTwoProd ℤ)
local notation "residueDoubling" =>
  TopModuleCat.tensorMapCLM ℤ
    (LinearMap.id : integerPairCoefficients →ₗ[ℤ] integerPairCoefficients)
    ((2 : ℤ) • ContinuousLinearMap.id ℤ residueModule)

/-- The residue right factor is Hausdorff with its supplied topology. -/
theorem residueModule_t2 : T2Space residueModule := by
  infer_instance

/-- Multiplication by the nonzero integer `3` kills `1` in the right factor. -/
theorem residueModule_three_smul_one : (3 : ℤ) • (1 : residueModule) = 0 := by
  change (3 : ℤ) • (1 : ZMod 3) = 0
  rw [Int.smul_one_eq_cast]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd (3 : ℤ) 3).mpr (dvd_refl (3 : ℤ))

/-- The residue right factor is not a free integer module. -/
theorem residueModule_not_free : ¬ Module.Free ℤ residueModule := by
  intro h
  let : Module.Free ℤ residueModule := h
  have hone : (1 : residueModule) = 0 :=
    (smul_eq_zero_iff_right (by norm_num : (3 : ℤ) ≠ 0)).mp
      residueModule_three_smul_one
  norm_num at hone

/-- The first coefficient generator applied to the nonzero residue `1`. -/
noncomputable def residueFirstTensor : residueTensor :=
  TopModuleCat.tensorGenerator ℤ integerPairCoefficients residueModule (1, 0) 1

/-- The first generator is the corresponding algebraic pure tensor. -/
theorem residueFirstTensor_eq_tmul :
    residueFirstTensor = ((1, 0) : integerPairCoefficients) ⊗ₜ[ℤ] (1 : residueModule) :=
  TopModuleCat.tensorGenerator_apply ℤ integerPairCoefficients residueModule (1, 0) 1

/-- Continuous coordinates detect the first tensor as `![1, 0]`. -/
theorem residueFirstTensor_coordinates :
    residueCoordinates residueFirstTensor = ![1, 0] := by
  ext i
  calc
    residueCoordinates residueFirstTensor i =
        (Module.Basis.finTwoProd ℤ).repr (1, 0) i • (1 : residueModule) :=
      TopModuleCat.tensorCoordinateContinuousLinearEquiv_tensorGenerator_apply ℤ
        integerPairCoefficients residueModule (Module.Basis.finTwoProd ℤ) (1, 0) 1 i
    _ = ![1, 0] i := by
      rw [congrFun (Module.Basis.coe_finTwoProd_repr ((1, 0) : ℤ × ℤ)) i]
      fin_cases i <;> norm_num

/-- The inverse continuous coordinates reconstruct the pure tensor. -/
theorem residueCoordinates_inverse_first :
    (residueCoordinates).symm ![1, 0] = residueFirstTensor := by
  apply (residueCoordinates).injective
  exact ((residueCoordinates).apply_symm_apply ![1, 0]).trans
    residueFirstTensor_coordinates.symm

/-- The pure tensor is nonzero, as detected by its first coordinate. -/
theorem residueFirstTensor_ne_zero : residueFirstTensor ≠ 0 := by
  intro h
  have hv := congrFun residueFirstTensor_coordinates (0 : Fin 2)
  rw [h, map_zero] at hv
  norm_num at hv

/-- A sum using both coefficient basis generators and nonzero right values. -/
noncomputable def residueMixedTensor : residueTensor :=
  residueFirstTensor +
    TopModuleCat.tensorGenerator ℤ integerPairCoefficients residueModule (0, 1) 2

/-- The mixed tensor has nonzero values in both coordinate positions. -/
theorem residueMixedTensor_coordinates :
    residueCoordinates residueMixedTensor = ![1, 2] := by
  ext i
  calc
    residueCoordinates residueMixedTensor i =
        residueCoordinates residueFirstTensor i +
          residueCoordinates
            (TopModuleCat.tensorGenerator ℤ integerPairCoefficients residueModule (0, 1) 2) i :=
      congrFun (map_add residueCoordinates residueFirstTensor
        (TopModuleCat.tensorGenerator ℤ integerPairCoefficients residueModule (0, 1) 2)) i
    _ = ![1, 0] i + (Module.Basis.finTwoProd ℤ).repr (0, 1) i • (2 : residueModule) := by
      rw [residueFirstTensor_coordinates,
        TopModuleCat.tensorCoordinateContinuousLinearEquiv_tensorGenerator_apply]
    _ = ![1, 2] i := by
      rw [congrFun (Module.Basis.coe_finTwoProd_repr ((0, 1) : ℤ × ℤ)) i]
      fin_cases i <;> norm_num

/-- The inverse coordinates reconstruct the mixed tensor. -/
theorem residueCoordinates_inverse_mixed :
    (residueCoordinates).symm ![1, 2] = residueMixedTensor := by
  apply (residueCoordinates).injective
  exact ((residueCoordinates).apply_symm_apply ![1, 2]).trans
    residueMixedTensor_coordinates.symm

/-- The mixed tensor is nonzero, as detected by its first coordinate. -/
theorem residueMixedTensor_ne_zero : residueMixedTensor ≠ 0 := by
  intro h
  have hv := congrFun residueMixedTensor_coordinates (0 : Fin 2)
  rw [h, map_zero] at hv
  norm_num at hv

/-- The pure and mixed tensors differ in their second coordinate. -/
theorem residueFirstTensor_ne_mixed : residueFirstTensor ≠ residueMixedTensor := by
  intro h
  have hv := congrFun residueMixedTensor_coordinates (1 : Fin 2)
  rw [← h, residueFirstTensor_coordinates] at hv
  exact (by decide : (0 : ZMod 3) ≠ 2) hv

/-- The canonical continuous tensor map doubles the right value of the pure tensor. -/
theorem residueDoubling_first :
    residueDoubling residueFirstTensor =
      TopModuleCat.tensorGenerator ℤ integerPairCoefficients residueModule (1, 0) 2 := by
  have hdouble : ((2 : ℤ) • ContinuousLinearMap.id ℤ residueModule)
      (1 : residueModule) = 2 := by
    norm_num [smul_apply, ContinuousLinearMap.id_apply, Int.smul_one_eq_cast]
  simpa only [residueFirstTensor, LinearMap.id_apply, hdouble] using
    TopModuleCat.tensorMapCLM_tensorGenerator_apply ℤ
      (LinearMap.id : integerPairCoefficients →ₗ[ℤ] integerPairCoefficients)
      ((2 : ℤ) • ContinuousLinearMap.id ℤ residueModule)
      ((1, 0) : integerPairCoefficients) (1 : residueModule)

/-- Doubling changes the coordinate vector from `![1, 0]` to `![2, 0]`. -/
theorem residueDoubling_first_coordinates :
    residueCoordinates (residueDoubling residueFirstTensor) = ![2, 0] := by
  rw [residueDoubling_first]
  ext i
  rw [TopModuleCat.tensorCoordinateContinuousLinearEquiv_tensorGenerator_apply,
    congrFun (Module.Basis.coe_finTwoProd_repr ((1, 0) : ℤ × ℤ)) i]
  fin_cases i <;> norm_num

/-- The canonical tensor doubling map moves a nonzero tensor. -/
theorem residueDoubling_first_ne :
    residueDoubling residueFirstTensor ≠ residueFirstTensor := by
  intro h
  have hv := congrFun residueDoubling_first_coordinates (0 : Fin 2)
  rw [h, residueFirstTensor_coordinates] at hv
  exact (by decide : (1 : ZMod 3) ≠ 2) hv

/-- The explicit finite basis supplies Hausdorffness of the residue tensor. -/
theorem residueTensor_t2_of_basis : T2Space residueTensor := by
  exact TopModuleCat.t2Space_tensorLeftObj_of_basis ℤ
    integerPairCoefficients residueModule (Module.Basis.finTwoProd ℤ)

/-- The projective statement applies to these finite-free coefficients through
Mathlib's free-to-projective instance. -/
theorem residueTensor_t2 : T2Space residueTensor := by
  let : Module.Free ℤ integerPairCoefficients :=
    Module.Free.of_basis (Module.Basis.finTwoProd ℤ)
  exact TopModuleCat.t2Space_tensorLeftObj ℤ integerPairCoefficients residueModule

/-- The basis theorem supplies disjoint open neighborhoods of the pure tensor and zero. -/
theorem residueFirstTensor_separated_zero :
    ∃ U V : Set residueTensor, IsOpen U ∧ IsOpen V ∧
      residueFirstTensor ∈ U ∧ 0 ∈ V ∧ Disjoint U V := by
  let : T2Space residueTensor := residueTensor_t2_of_basis
  exact t2_separation residueFirstTensor_ne_zero

/-- The canonical theorem separates the distinct pure and mixed tensors. -/
theorem residueFirstTensor_separated_mixed :
    ∃ U V : Set residueTensor, IsOpen U ∧ IsOpen V ∧
      residueFirstTensor ∈ U ∧ residueMixedTensor ∈ V ∧ Disjoint U V := by
  let : T2Space residueTensor := residueTensor_t2
  exact t2_separation residueFirstTensor_ne_mixed

/-- The existing discrete integer right factor is noncompact. -/
theorem integerModule_noncompact : NoncompactSpace integerModule := by
  infer_instance

/-- The finite-basis theorem also applies to the noncompact Hausdorff integer right factor. -/
theorem integerTensor_t2 :
    T2Space (TopModuleCat.tensorLeftObj ℤ integerPairCoefficients integerModule) := by
  exact TopModuleCat.t2Space_tensorLeftObj_of_basis ℤ
    integerPairCoefficients integerModule (Module.Basis.finTwoProd ℤ)

/-- Hausdorffness separates the existing nonzero integer tensor from zero. -/
theorem integerFirstTensor_separated_zero :
    ∃ U V : Set (TopModuleCat.tensorLeftObj ℤ integerPairCoefficients integerModule),
      IsOpen U ∧ IsOpen V ∧ TensorProductExamples.firstGeneratorTensor ∈ U ∧
        0 ∈ V ∧ Disjoint U V := by
  let := integerTensor_t2
  exact t2_separation TensorProductExamples.firstGeneratorTensor_ne_zero

section Boundaries

variable (R : Type uR) [CommRing R] [TopologicalSpace R]

/-- The explicit empty `Fin 0` coefficient basis gives a Hausdorff tensor for every right factor. -/
theorem emptyCoefficient_t2 (M : TopModuleCat.{uM} R) :
    T2Space (TopModuleCat.tensorLeftObj R (ModuleCat.of R (Fin 0 → R)) M) := by
  let : Subsingleton (TopModuleCat.tensorLeftObj R (ModuleCat.of R (Fin 0 → R)) M) :=
    ⟨fun x y ↦ (TensorProductExamples.emptyCoefficient_tensor_eq_zero R M x).trans
      (TensorProductExamples.emptyCoefficient_tensor_eq_zero R M y).symm⟩
  infer_instance

/-- Trivial scalar rings give Hausdorff tensors without finite-free or right separation premises. -/
theorem trivialRing_t2 [Subsingleton R] (C : ModuleCat.{uC} R) (M : TopModuleCat.{uM} R) :
    T2Space (TopModuleCat.tensorLeftObj R C M) := by
  let : Subsingleton (TopModuleCat.tensorLeftObj R C M) :=
    Module.subsingleton R (TopModuleCat.tensorLeftObj R C M)
  infer_instance

/-- The explicit-basis theorem is usable over a trivial ring without an empty-index premise. -/
theorem trivialRing_t2_of_basis [Subsingleton R]
    (C : ModuleCat.{uC} R) (M : TopModuleCat.{uM} R) {ι : Type uι}
    (b : Module.Basis ι R C) : T2Space (TopModuleCat.tensorLeftObj R C M) := by
  let : Subsingleton M := Module.subsingleton R M
  let : T2Space M := inferInstance
  exact TopModuleCat.t2Space_tensorLeftObj_of_basis R C M b

/-- Free coefficients over a trivial ring satisfy the projective statement;
in particular this includes the finite-free specialization. -/
theorem trivialRing_freeFinite_t2 [Subsingleton R]
    (C : ModuleCat.{uC} R) (M : TopModuleCat.{uM} R)
    [Module.Free R C] : T2Space (TopModuleCat.tensorLeftObj R C M) := by
  let : Subsingleton M := Module.subsingleton R M
  let : T2Space M := inferInstance
  exact TopModuleCat.t2Space_tensorLeftObj R C M

end Boundaries

/-- The zero ring permits a supplied basis indexed by the nonempty type `Fin 2`. -/
theorem zeroRing_nonemptyBasis_t2 :
    T2Space (TopModuleCat.tensorLeftObj (ZMod 1)
      (ModuleCat.of (ZMod 1) (ZMod 1 × ZMod 1)) (TopModuleCat.of (ZMod 1) (ZMod 1))) := by
  exact trivialRing_t2_of_basis (ZMod 1)
    (ModuleCat.of (ZMod 1) (ZMod 1 × ZMod 1)) (TopModuleCat.of (ZMod 1) (ZMod 1))
    (Module.Basis.finTwoProd (ZMod 1))

/-- The existing indiscrete-module functor applied to the integer module. -/
abbrev indiscreteIntegerModule : TopModuleCat ℤ :=
  (TopModuleCat.indiscrete ℤ).obj (ModuleCat.of ℤ ℤ)

/-- The nontrivial indiscrete integer module is not Hausdorff. -/
theorem indiscreteIntegerModule_not_t2 : ¬ T2Space indiscreteIntegerModule := by
  intro h
  let : T2Space indiscreteIntegerModule := h
  let : IndiscreteTopology indiscreteIntegerModule := ⟨rfl⟩
  let : Subsingleton indiscreteIntegerModule :=
    subsingleton_iff_indiscreteTopology.mpr inferInstance
  have h01 := Subsingleton.elim
    (show indiscreteIntegerModule from (0 : ℤ))
    (show indiscreteIntegerModule from (1 : ℤ))
  exact (zero_ne_one : (0 : ℤ) ≠ 1) h01

/-- Zero coefficients prevent Hausdorffness of the tensor from reflecting to the right factor. -/
theorem emptyIndiscrete_tensor_boundary :
    T2Space (TopModuleCat.tensorLeftObj ℤ (ModuleCat.of ℤ (Fin 0 → ℤ))
      indiscreteIntegerModule) ∧ ¬ T2Space indiscreteIntegerModule := by
  exact ⟨emptyCoefficient_t2 ℤ indiscreteIntegerModule, indiscreteIntegerModule_not_t2⟩

/-- The supplied-basis statement gives open separation with arbitrary independently
leveled input and index types, including the finite-basis specialization. -/
theorem finiteBasis_separates_tensor
    (R : Type uR) [CommRing R] [TopologicalSpace R]
    (C : ModuleCat.{uC} R) (M : TopModuleCat.{uM} R)
    {ι : Type uι} (b : Module.Basis ι R C) [T2Space M]
    (x y : TopModuleCat.tensorLeftObj R C M) (hne : x ≠ y) :
    ∃ U V : Set (TopModuleCat.tensorLeftObj R C M),
      IsOpen U ∧ IsOpen V ∧ x ∈ U ∧ y ∈ V ∧ Disjoint U V := by
  let := TopModuleCat.t2Space_tensorLeftObj_of_basis R C M b
  exact t2_separation hne

section ZeroRight

variable (R : Type uR) [CommRing R] [TopologicalSpace R]

/-- The canonical zero right module, as in the zero-right tensor-Hom client. -/
abbrev zeroRightModule : TopModuleCat R :=
  (TopModuleCat.indiscrete R).obj (ModuleCat.of R (Fin 0 → R))

/-- The supplied-basis statement applies to the zero right module. -/
theorem zeroRight_t2_of_basis (C : ModuleCat.{uC} R) {ι : Type uι}
    (b : Module.Basis ι R C) :
    T2Space (TopModuleCat.tensorLeftObj R C (zeroRightModule R)) := by
  let : Subsingleton (zeroRightModule R) := by
    change Subsingleton (Fin 0 → R)
    exact ⟨fun f g ↦ funext (fun i ↦ Fin.elim0 i)⟩
  let : T2Space (zeroRightModule R) := inferInstance
  exact TopModuleCat.t2Space_tensorLeftObj_of_basis R C (zeroRightModule R) b

/-- The projective statement also applies to the canonical zero right module. -/
theorem zeroRight_projective_t2 (C : ModuleCat.{uC} R) [Module.Projective R C] :
    T2Space (TopModuleCat.tensorLeftObj R C (zeroRightModule R)) := by
  let : Subsingleton (zeroRightModule R) := by
    change Subsingleton (Fin 0 → R)
    exact ⟨fun f g ↦ funext (fun i ↦ Fin.elim0 i)⟩
  let : T2Space (zeroRightModule R) := inferInstance
  exact TopModuleCat.t2Space_tensorLeftObj R C (zeroRightModule R)

end ZeroRight

/-- The arbitrary product-coordinate map agrees with the old finite residue coordinates
on every tensor, not just on the generators. -/
theorem residueProductCoordinates_eq (x : residueTensor) :
    TopModuleCat.tensorCoordinatesCLM ℤ integerPairCoefficients residueModule
      (Module.Basis.finTwoProd ℤ) x = residueCoordinates x := by
  exact DFunLike.congr_fun
    (TopModuleCat.tensorCoordinatesCLM_eq_finiteCoordinates ℤ
      integerPairCoefficients residueModule (Module.Basis.finTwoProd ℤ)) x

end TensorSeparationExamples
