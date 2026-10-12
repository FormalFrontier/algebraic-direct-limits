/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicDirectLimits.Topology.Restriction
import Mathlib.Algebra.Module.ULift
public import Mathlib.Algebra.Ring.Prod
public import Mathlib.Topology.Algebra.Algebra
public import Mathlib.Topology.Algebra.Module.Equiv
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.NormNum

/-!
# Scalar restriction on products, matrices, semirings and algebras

Swapping the factors of `ℝ × ℝ` gives a continuous nonidentity endomorphism
of a nondiscrete ring. The regular module and its restricted view coexist:
the scalar `(1, 0)` acts on `1` as `(0, 1)` only in the restricted view.
Doubling stays a nonzero continuous linear map, and a second client raises
only its target carrier universe.

The matrix clients use the noncommutative ring of two-by-two real matrices.
The real algebra-map client applies the multiplication-versus-scalar-action
agreement with the usual nondiscrete topology and acts nontrivially on a matrix
unit. The discrete-algebra clients recover the scalar and map formulas of
same-topology restriction for field extensions; target discreteness and
finite dimensionality are not needed for restriction itself. The natural-number
client uses the semiring continuity criterion without a continuity premise.

These clients use the characteristic scalar and map formulas and evaluate
the natural identity and composition comparisons on nonzero vectors.

## References

The algebraic swap, matrix topology and universe lift use Mathlib's existing
ring equivalence, topological-ring and continuous-linear-equivalence APIs.
The discrete-algebra specialization follows the scalar-restriction
formalization of Continuous Group Cohomology by Formal Frontier Agents,
including Beacon's original development.
-/

@[expose] public section

open CategoryTheory

namespace ScalarRestriction

/-- The regular topological module of the product of two real rings. -/
noncomputable abbrev realPairModule : TopModuleCat (ℝ × ℝ) :=
  TopModuleCat.of (ℝ × ℝ) (ℝ × ℝ)

/-- The ring endomorphism swapping the two real coordinates. -/
def swapHom : (ℝ × ℝ) →+* (ℝ × ℝ) :=
  (RingEquiv.prodComm : (ℝ × ℝ) ≃+* (ℝ × ℝ)).toRingHom

/-- Swapping the coordinates is continuous for their usual product topology. -/
theorem continuous_swapHom : Continuous swapHom :=
  continuous_snd.prodMk continuous_fst

/-- The scalar map used for restriction is not the identity. -/
theorem swapHom_ne_id : swapHom ≠ RingHom.id (ℝ × ℝ) := by
  intro h
  have hsecond : (1 : ℝ) = 0 := congrArg Prod.snd (RingHom.congr_fun h (1, 0))
  exact one_ne_zero hsecond

/-- The same carrier with the action restricted along coordinate swapping. -/
noncomputable abbrev swappedRealPair : TopModuleCat (ℝ × ℝ) :=
  TopModuleCat.restrictScalarsObj swapHom continuous_swapHom realPairModule

/-- In the restricted view, the first scalar coordinate acts as the second.
The action is taken from the stored restriction object, not the regular carrier. -/
theorem swapped_smul_one :
    @SMul.smul (ℝ × ℝ) swappedRealPair swappedRealPair.isModule.toSMul
      (1, 0) 1 = ((0, 1) : ℝ × ℝ) := by
  calc
    _ = @SMul.smul (ℝ × ℝ) realPairModule realPairModule.isModule.toSMul
        (swapHom (1, 0)) (1 : realPairModule) :=
      TopModuleCat.restrictScalarsObj_smul swapHom continuous_swapHom realPairModule
        (1, 0) (1 : realPairModule)
    _ = ((0, 1) : ℝ × ℝ) := by
      change swapHom (1, 0) * (1 : ℝ × ℝ) = (0, 1)
      rw [mul_one]
      rfl

/-- Original and restricted scalar views differ on a nonzero vector, even
though their scalar-ring type and carrier type are the same. Both actions are
selected from the corresponding bundled module fields. -/
theorem swapped_action_differs :
    @SMul.smul (ℝ × ℝ) swappedRealPair swappedRealPair.isModule.toSMul (1, 0) 1 ≠
      @SMul.smul (ℝ × ℝ) realPairModule realPairModule.isModule.toSMul (1, 0) 1 := by
  rw [swapped_smul_one]
  intro h
  have hregular :
      @SMul.smul (ℝ × ℝ) realPairModule realPairModule.isModule.toSMul (1, 0) 1 =
        ((1, 0) : ℝ × ℝ) := by
    change ((1, 0) : ℝ × ℝ) * 1 = (1, 0)
    exact mul_one _
  have hsecond : (1 : ℝ) = 0 := congrArg Prod.snd (h.trans hregular)
  exact one_ne_zero hsecond

/-- The first coordinate stays continuous under same-topology restriction. -/
theorem continuous_restricted_first_coordinate :
    Continuous (fun x : swappedRealPair ↦ x.1) :=
  (TopModuleCat.continuous_restrictScalarsObj_iff swapHom continuous_swapHom
    realPairModule Prod.fst).mpr continuous_fst

/-- A nonzero continuous linear endomorphism of the regular product module. -/
noncomputable def pairDoubling : realPairModule →L[ℝ × ℝ] realPairModule :=
  ContinuousLinearMap.id (ℝ × ℝ) realPairModule +
    ContinuousLinearMap.id (ℝ × ℝ) realPairModule

/-- Doubling adds the vector to itself. -/
@[simp]
theorem pairDoubling_apply (x : realPairModule) : pairDoubling x = x + x := rfl

/-- Doubling restricted to the swapped scalar view.
Both module structures are the stored fields of the restriction object. -/
noncomputable def swappedDoubling :
    @ContinuousLinearMap (ℝ × ℝ) (ℝ × ℝ) _ _ (RingHom.id (ℝ × ℝ))
      swappedRealPair swappedRealPair.topologicalSpace
      swappedRealPair.isAddCommGroup.toAddCommMonoid
      swappedRealPair swappedRealPair.topologicalSpace
      swappedRealPair.isAddCommGroup.toAddCommMonoid
      swappedRealPair.isModule swappedRealPair.isModule :=
  TopModuleCat.restrictScalarsCLM swapHom continuous_swapHom
    (M := realPairModule) (N := realPairModule) pairDoubling

/-- Restriction retains the nonzero value of doubling. -/
theorem swappedDoubling_first_axis : swappedDoubling (1, 0) = ((2, 0) : ℝ × ℝ) := by
  rw [swappedDoubling, TopModuleCat.restrictScalarsCLM_apply, pairDoubling_apply]
  change ((1 : ℝ) + 1, (0 : ℝ) + 0) = (2, 0)
  norm_num

/-- The restricted linear map is not zero. -/
theorem swappedDoubling_ne_zero : swappedDoubling ≠ 0 := by
  intro h
  have hx := DFunLike.congr_fun h (1, 0)
  rw [swappedDoubling_first_axis] at hx
  have hfirst : (2 : ℝ) = 0 := congrArg Prod.fst hx
  norm_num at hfirst

/-- The categorical restriction map preserves a genuine composite, whose
value on the first axis is four times the input. -/
theorem restricted_composite_first_axis :
    (TopModuleCat.restrictScalars swapHom continuous_swapHom).map
        (TopModuleCat.ofHom pairDoubling ≫ TopModuleCat.ofHom pairDoubling) (1, 0) =
      ((4, 0) : ℝ × ℝ) := by
  rw [TopModuleCat.restrictScalars_map_apply]
  change (((1 : ℝ) + 1) + (1 + 1), ((0 : ℝ) + 0) + (0 + 0)) = (4, 0)
  norm_num

/-- Restriction twice along swapping recovers the original action. -/
theorem twice_swapped_smul_one :
    @SMul.smul (ℝ × ℝ) _
      (TopModuleCat.restrictScalarsObj (swapHom.comp swapHom)
        (continuous_swapHom.comp continuous_swapHom) realPairModule).isModule.toSMul
      (1, 0) 1 = ((1, 0) : ℝ × ℝ) := by
  calc
    _ = @SMul.smul (ℝ × ℝ) realPairModule realPairModule.isModule.toSMul
        ((swapHom.comp swapHom) (1, 0)) (1 : realPairModule) :=
      TopModuleCat.restrictScalarsObj_smul (swapHom.comp swapHom)
        (continuous_swapHom.comp continuous_swapHom) realPairModule (1, 0) (1 : realPairModule)
    _ = ((1, 0) : ℝ × ℝ) := by
      change (swapHom.comp swapHom) (1, 0) * (1 : ℝ × ℝ) = (1, 0)
      rw [mul_one]
      rfl

/-- The identity natural comparison retains a nonzero vector. -/
theorem identity_comparison_first_axis :
    (TopModuleCat.restrictScalarsId (R := ℝ × ℝ)).hom.app realPairModule (1, 0) =
      ((1, 0) : ℝ × ℝ) :=
  TopModuleCat.restrictScalarsId_hom_app_apply realPairModule (1, 0)

/-- The composition comparison transports the twice-swapped action to
successive restriction without changing its value on a nonzero vector. -/
theorem swapping_comparison_first_axis :
    (TopModuleCat.restrictScalarsComp swapHom swapHom
        continuous_swapHom continuous_swapHom).hom.app realPairModule
        (@SMul.smul (ℝ × ℝ) _
          (TopModuleCat.restrictScalarsObj (swapHom.comp swapHom)
            (continuous_swapHom.comp continuous_swapHom) realPairModule).isModule.toSMul
          (1, 0)
          (show (TopModuleCat.restrictScalars (swapHom.comp swapHom)
              (continuous_swapHom.comp continuous_swapHom)).obj realPairModule from
            (1 : realPairModule))) =
      ((1, 0) : ℝ × ℝ) := by
  exact
    (TopModuleCat.restrictScalarsComp_hom_app_apply swapHom swapHom
      continuous_swapHom continuous_swapHom realPairModule
      (@SMul.smul (ℝ × ℝ)
        (TopModuleCat.restrictScalarsObj (swapHom.comp swapHom)
          (continuous_swapHom.comp continuous_swapHom) realPairModule)
        (TopModuleCat.restrictScalarsObj (swapHom.comp swapHom)
          (continuous_swapHom.comp continuous_swapHom) realPairModule).isModule.toSMul
        (1, 0)
        (show (TopModuleCat.restrictScalars (swapHom.comp swapHom)
            (continuous_swapHom.comp continuous_swapHom)).obj realPairModule from
          (1 : realPairModule)))).trans
      twice_swapped_smul_one

/-- A topological product module whose carrier alone has been universe-raised.
Joint continuity of its canonical action is transported along the linear down map. -/
noncomputable abbrev liftedRealPairModule : TopModuleCat.{1} (ℝ × ℝ) :=
  letI : ContinuousSMul (ℝ × ℝ) (ULift.{1} realPairModule) :=
    ContinuousSMul.induced
      (ULift.moduleEquiv (R := ℝ × ℝ) (M := realPairModule)).toLinearMap
  TopModuleCat.of (ℝ × ℝ) (ULift.{1} realPairModule)

/-- Doubling with a target in a different carrier universe. -/
noncomputable def liftedPairDoubling : realPairModule →L[ℝ × ℝ] liftedRealPairModule :=
  let e : ULift.{1} realPairModule ≃L[ℝ × ℝ] realPairModule := ContinuousLinearEquiv.ulift
  e.symm.toContinuousLinearMap.comp pairDoubling

/-- Continuous-linear restriction supports independent target universes and
still retains the same function. -/
theorem restricted_liftedPairDoubling_apply (x : realPairModule) :
    TopModuleCat.restrictScalarsCLM swapHom continuous_swapHom
        (M := realPairModule) (N := liftedRealPairModule) liftedPairDoubling x =
      (show TopModuleCat.restrictScalarsObj swapHom continuous_swapHom liftedRealPairModule from
        ULift.up (x + x)) := by
  rw [TopModuleCat.restrictScalarsCLM_apply]
  rfl

/-- The regular module of the noncommutative ring of two-by-two real matrices. -/
noncomputable abbrev realMatrixModule : TopModuleCat (Matrix (Fin 2) (Fin 2) ℝ) :=
  TopModuleCat.of (Matrix (Fin 2) (Fin 2) ℝ) (Matrix (Fin 2) (Fin 2) ℝ)

/-- The upper off-diagonal matrix unit. -/
def upperUnit : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j ↦ if i = 0 ∧ j = 1 then 1 else 0

/-- The lower off-diagonal matrix unit. -/
def lowerUnit : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j ↦ if i = 1 ∧ j = 0 then 1 else 0

/-- The matrix scalar ring in this client is genuinely noncommutative. -/
theorem matrix_units_do_not_commute : upperUnit * lowerUnit ≠ lowerUnit * upperUnit := by
  intro h
  have hentry := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ ↦ A 0 0) h
  norm_num [Matrix.mul_apply, Fin.sum_univ_two, upperUnit, lowerUnit] at hentry

/-- Restriction over a noncommutative scalar ring retains a nonzero endomorphism. -/
theorem restricted_matrix_doubling_entry :
    (TopModuleCat.restrictScalars (RingHom.id (Matrix (Fin 2) (Fin 2) ℝ)) continuous_id).map
        (TopModuleCat.ofHom
          (ContinuousLinearMap.id (Matrix (Fin 2) (Fin 2) ℝ) realMatrixModule +
            ContinuousLinearMap.id (Matrix (Fin 2) (Fin 2) ℝ) realMatrixModule))
        (1 : realMatrixModule) 0 0 = 2 := by
  rw [TopModuleCat.restrictScalars_map_apply]
  change ((1 : Matrix (Fin 2) (Fin 2) ℝ) + 1) 0 0 = 2
  norm_num [Matrix.one_apply]

section DiscreteAlgebra

universe uR uK uM uN

variable {R : Type uR} {K : Type uK} [Field R] [Field K] [Algebra R K]
variable [TopologicalSpace R] [DiscreteTopology R] [TopologicalSpace K]

/-- For field extensions with discrete source, the generic object recovers
the algebra-map scalar action without target discreteness or finite dimensionality. -/
theorem discrete_algebra_restriction_smul (M : TopModuleCat.{uM} K) (r : R) (x : M) :
    r • (show TopModuleCat.restrictScalarsObj (algebraMap R K)
        continuous_of_discreteTopology M from x) =
      (show TopModuleCat.restrictScalarsObj (algebraMap R K)
        continuous_of_discreteTopology M from algebraMap R K r • x) :=
  TopModuleCat.restrictScalarsObj_smul (algebraMap R K) continuous_of_discreteTopology M r x

/-- The discrete-field specialization agrees with Mathlib's algebraic restriction. -/
theorem discrete_algebra_restriction_toModuleCat (M : TopModuleCat.{uM} K) :
    (TopModuleCat.restrictScalarsObj (algebraMap R K)
        continuous_of_discreteTopology M).toModuleCat =
      (ModuleCat.restrictScalars (algebraMap R K)).obj M.toModuleCat :=
  TopModuleCat.restrictScalarsObj_toModuleCat (algebraMap R K) continuous_of_discreteTopology M

/-- The discrete-field continuous-map specialization retains the original function,
with independent source and target carrier universes. -/
theorem discrete_algebra_restriction_map_apply {M : TopModuleCat.{uM} K}
    {N : TopModuleCat.{uN} K} (f : M →L[K] N) (x : M) :
    TopModuleCat.restrictScalarsCLM (algebraMap R K) continuous_of_discreteTopology f x = f x :=
  TopModuleCat.restrictScalarsCLM_apply (algebraMap R K) continuous_of_discreteTopology f x

end DiscreteAlgebra

/-- Multiplication through the real algebra map into two-by-two real matrices
is jointly continuous for the usual, nondiscrete scalar topology. -/
theorem continuous_real_matrix_algebra_action :
    Continuous (fun p : ℝ × Matrix (Fin 2) (Fin 2) ℝ ↦
      algebraMap ℝ (Matrix (Fin 2) (Fin 2) ℝ) p.1 * p.2) := by
  rw [TopModuleCat.algebraMap_mulAction_eq_smul
    (R := ℝ) (S := Matrix (Fin 2) (Fin 2) ℝ)]
  exact (continuous_algebraMap_iff_smul ℝ (Matrix (Fin 2) (Fin 2) ℝ)).mp
    (continuous_algebraMap ℝ (Matrix (Fin 2) (Fin 2) ℝ))

/-- The real scalar `2` acts on the upper matrix unit with a nonzero entry. -/
theorem real_matrix_algebra_action_upper_entry :
    (algebraMap ℝ (Matrix (Fin 2) (Fin 2) ℝ) 2 * upperUnit) 0 1 = 2 := by
  have haction := congrFun
    (TopModuleCat.algebraMap_mulAction_eq_smul
      (R := ℝ) (S := Matrix (Fin 2) (Fin 2) ℝ)) (2, upperUnit)
  rw [haction]
  norm_num [upperUnit, Matrix.smul_apply]

/-- The real algebra-map action on the upper matrix unit is not zero. -/
theorem real_matrix_algebra_action_upper_ne_zero :
    algebraMap ℝ (Matrix (Fin 2) (Fin 2) ℝ) 2 * upperUnit ≠ 0 := by
  intro h
  have hentry := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ ↦ A 0 1) h
  rw [real_matrix_algebra_action_upper_entry] at hentry
  norm_num at hentry

/-- The natural-number cast acts jointly continuously on the regular semimodule
of `ℕ` with its usual topology; no ring structure or continuity premise is used. -/
theorem continuous_nat_regular_action :
    Continuous (fun p : ℕ × ℕ ↦ Nat.castRingHom ℕ p.1 * p.2) :=
  (TopModuleCat.continuous_ringHom_iff_continuous_mulAction (Nat.castRingHom ℕ)).mp
    continuous_of_discreteTopology

end ScalarRestriction
