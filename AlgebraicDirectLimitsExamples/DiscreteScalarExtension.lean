/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicDirectLimits.Topology.DiscreteScalarExtension
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Topology.Instances.Int
public import Mathlib.Tactic.NormNum

/-!
# Discrete scalar extension: matrices and a swapping algebra

The base is the nonfield `ℤ`; the coefficient algebra is the noncommutative ring
of two-by-two integer matrices, equipped with the discrete topology. The input
is the countable product of copies of `ℤ`, with the product topology, rather than
a finite-dimensional module. Left multiplication uses the base-linear coefficient
slot, so its continuity does not require a coefficient-linear multiplication map.

Evaluation at the zeroth coordinate, followed by the right tensor-unit map,
detects a nonzero tensor, a tensor moved by extended doubling, and the difference
between the two orders of coefficient multiplication.

A second example uses `A = ℤ × ℤ` for both scalar types and the swapping ring
homomorphism for `Algebra A A`. Its input is the regular rank-one module, bundled
before the swapping algebra is chosen. The coefficient base action is swapping,
while its coefficient action is regular multiplication. A coefficient-linear
rank-one comparison sends `c ⊗ m` to `φ(m) * c`. The unit is nonzero; the two
actions of `(1, 0)` on it have images `(0, 1)` and `(1, 0)`. Extending the regular
first-coordinate projection gives a nonzero map different from the identity.

## Limitations

The rank-one comparison is algebraic and reuses Mathlib's
`TensorProduct.AlgebraTensorModule.rid` and its pure-tensor laws. No continuous
rank-one equivalence or arbitrary coefficient topology is asserted.

## References

The matrix detector uses the tensor-map and right tensor-unit APIs developed
by Kenny Lau and Mario Carneiro. The rank-one comparison uses the coefficient-linear
tensor API developed in
Mathlib by Kim Morrison, Johan Commelin and Eric Wieser. The swapping automorphism
uses Mathlib's product-ring equivalence.
-/

@[expose] public section

open scoped TensorProduct

namespace DiscreteScalarExtensionExamples

/-- The coefficient ring of two-by-two integer matrices. -/
abbrev matrixRing := Matrix (Fin 2) (Fin 2) ℤ

/-- Every entry of the zero in the coefficient module is zero. -/
private theorem matrixCoefficient_zero_apply (i j : Fin 2) :
    (show matrixRing from
      (0 : TopModuleCat.DiscreteExtendScalars.coefficient ℤ matrixRing)) i j = 0 := by
  exact Matrix.zero_apply i j

/-- Addition in the coefficient module adds the corresponding matrix entries. -/
private theorem matrixCoefficient_add_apply
    (c d : TopModuleCat.DiscreteExtendScalars.coefficient ℤ matrixRing) (i j : Fin 2) :
    (show matrixRing from
      (c + d : TopModuleCat.DiscreteExtendScalars.coefficient ℤ matrixRing)) i j =
        (show matrixRing from c) i j + (show matrixRing from d) i j := by
  exact Matrix.add_apply (show matrixRing from c) (show matrixRing from d) i j

/-- Discrete topology on the coefficient ring. -/
@[instance_reducible]
def matrixTopology : TopologicalSpace matrixRing := ⊥

/-- The discrete topology on the ring of two-by-two integer matrices. -/
local instance : TopologicalSpace matrixRing := matrixTopology
local instance : DiscreteTopology matrixRing := discreteTopology_bot matrixRing

/-- A countable product of discrete integer modules, with its product topology. -/
abbrev integerSequences : TopModuleCat ℤ := TopModuleCat.of ℤ (ℕ → ℤ)

/-- The sequence which is constantly one. -/
def constantOne : integerSequences := fun _ ↦ 1

/-- The matrix unit in position `(0, 1)`. -/
def upperUnit : matrixRing := fun i j ↦ if i = 0 ∧ j = 1 then 1 else 0

/-- The matrix unit in position `(1, 0)`. -/
def lowerUnit : matrixRing := fun i j ↦ if i = 1 ∧ j = 0 then 1 else 0

/-- The coefficient algebra is genuinely noncommutative. -/
theorem matrixUnits_noncommute : upperUnit * lowerUnit ≠ lowerUnit * upperUnit := by
  intro h
  have h00 := congrFun (congrFun h (0 : Fin 2)) (0 : Fin 2)
  norm_num [upperUnit, lowerUnit, Matrix.mul_apply, Fin.sum_univ_two] at h00

/-- The coefficient-linear extension with nonfield base and infinite input. -/
noncomputable def matrixExtension : TopModuleCat matrixRing :=
  TopModuleCat.discreteExtendScalarsObj ℤ matrixRing integerSequences

/-- A tensor carrying the upper matrix unit and the constant-one sequence. -/
noncomputable def upperTensor : matrixExtension := upperUnit ⊗ₜ[ℤ] constantOne

private noncomputable def matrixTensorDetector :
    TopModuleCat.discreteExtendScalarsRObj ℤ matrixRing integerSequences →ₗ[ℤ]
      TopModuleCat.DiscreteExtendScalars.coefficient ℤ matrixRing :=
  (TensorProduct.rid ℤ
    (TopModuleCat.DiscreteExtendScalars.coefficient ℤ matrixRing)).toLinearMap.comp
      (TensorProduct.map
        (LinearMap.id : TopModuleCat.DiscreteExtendScalars.coefficient ℤ matrixRing →ₗ[ℤ]
          TopModuleCat.DiscreteExtendScalars.coefficient ℤ matrixRing)
        (LinearMap.proj 0 : integerSequences →ₗ[ℤ] ℤ))

private theorem matrixTensorDetector_tmul (c : matrixRing) (m : integerSequences) :
    matrixTensorDetector (c ⊗ₜ[ℤ] m) =
      (m 0) • (show TopModuleCat.DiscreteExtendScalars.coefficient ℤ matrixRing from c) := by
  exact TensorProduct.rid_tmul (R := ℤ)
    (M := TopModuleCat.DiscreteExtendScalars.coefficient ℤ matrixRing) c (m 0)

/-- The detector evaluates a tensor generator by the zeroth coordinate acting on its coefficient. -/
private theorem matrixTensorDetector_generator_apply
    (c : TopModuleCat.DiscreteExtendScalars.coefficient ℤ matrixRing) (m : integerSequences) :
    matrixTensorDetector
      (TopModuleCat.tensorGenerator ℤ
        (TopModuleCat.DiscreteExtendScalars.coefficient ℤ matrixRing) integerSequences c m) =
      (m 0) • c := by
  let C := TopModuleCat.DiscreteExtendScalars.coefficient ℤ matrixRing
  let f : C →ₗ[ℤ] C := LinearMap.id
  let p : integerSequences →ₗ[ℤ] ℤ := LinearMap.proj 0
  let q := (TensorProduct.rid ℤ C).toLinearMap
  have ht : TensorProduct.map f p (c ⊗ₜ[ℤ] m) = c ⊗ₜ[ℤ] m 0 :=
    (TensorProduct.map_tmul f p c m).trans
      (congrArg₂ (fun a : C ↦ fun b : ℤ ↦ a ⊗ₜ[ℤ] b)
        (LinearMap.id_apply c) (LinearMap.proj_apply 0 m))
  exact (congrArg matrixTensorDetector
    (TopModuleCat.tensorGenerator_apply ℤ C integerSequences c m)).trans
      ((LinearMap.comp_apply q (TensorProduct.map f p) (c ⊗ₜ[ℤ] m)).trans
        ((congrArg q ht).trans (TensorProduct.rid_tmul (R := ℤ) (M := C) c (m 0))))

/-- The chosen tensor is nonzero. -/
theorem upperTensor_ne_zero : upperTensor ≠ 0 := by
  intro h
  let C := TopModuleCat.DiscreteExtendScalars.coefficient ℤ matrixRing
  let c : C := upperUnit
  have ht : upperTensor = TopModuleCat.tensorGenerator ℤ C integerSequences c constantOne :=
    (TopModuleCat.tensorGenerator_apply ℤ C integerSequences c constantOne).symm
  have himage :
      matrixTensorDetector (TopModuleCat.tensorGenerator ℤ C integerSequences c constantOne) =
        (0 : C) :=
    (congrArg matrixTensorDetector (ht.symm.trans h)).trans (map_zero matrixTensorDetector)
  rw [matrixTensorDetector_generator_apply] at himage
  have hone : (constantOne 0) • c = c := by
    simpa only [constantOne] using (one_smul ℤ c)
  have hc : c = (0 : C) := hone.symm.trans himage
  have h01 := congrArg (fun z : C ↦ (show matrixRing from z) (0 : Fin 2) (1 : Fin 2)) hc
  rw [matrixCoefficient_zero_apply] at h01
  norm_num [c, upperUnit] at h01

/-- Doubling on the infinite product is a continuous base-linear map. -/
noncomputable def sequenceDoubling : integerSequences →L[ℤ] integerSequences :=
  2 • ContinuousLinearMap.id ℤ integerSequences

/-- Doubling evaluates coordinatewise as addition of a sequence to itself. -/
theorem sequenceDoubling_apply (m : integerSequences) (i : ℕ) :
    sequenceDoubling m i = m i + m i := by
  simp only [sequenceDoubling, two_smul]
  have hadd :
      (ContinuousLinearMap.id ℤ integerSequences +
        ContinuousLinearMap.id ℤ integerSequences) m = m + m :=
    (_root_.add_apply (ContinuousLinearMap.id ℤ integerSequences)
      (ContinuousLinearMap.id ℤ integerSequences) m).trans
        (congrArg₂ (fun x y : integerSequences ↦ x + y)
          (ContinuousLinearMap.id_apply m) (ContinuousLinearMap.id_apply m))
  exact (congrArg (fun n : integerSequences ↦ n i) hadd).trans (Pi.add_apply m m i)

/-- The extended doubling uses the canonical coefficient-linear map. -/
noncomputable def matrixTensorDoubling : matrixExtension →L[matrixRing] matrixExtension :=
  TopModuleCat.DiscreteExtendScalars.mapCLM ℤ matrixRing sequenceDoubling

/-- Extending doubling moves the selected nonzero tensor. -/
theorem matrixTensorDoubling_moves_upper : matrixTensorDoubling upperTensor ≠ upperTensor := by
  intro h
  let C := TopModuleCat.DiscreteExtendScalars.coefficient ℤ matrixRing
  let c : C := upperUnit
  let e := TopModuleCat.DiscreteExtendScalars.rViewHomeomorph ℤ matrixRing integerSequences
  have ht : upperTensor =
      e (TopModuleCat.tensorGenerator ℤ C integerSequences c constantOne) :=
    (TopModuleCat.DiscreteExtendScalars.rViewHomeomorph_apply ℤ matrixRing integerSequences
      (c ⊗ₜ[ℤ] constantOne)).symm.trans
        (congrArg e
          (TopModuleCat.tensorGenerator_apply ℤ C integerSequences c constantOne).symm)
  have hR :
      TopModuleCat.DiscreteExtendScalars.mapRCLM ℤ matrixRing sequenceDoubling
          (TopModuleCat.tensorGenerator ℤ C integerSequences c constantOne) =
        TopModuleCat.tensorGenerator ℤ C integerSequences c (sequenceDoubling constantOne) :=
    (congrArg (TopModuleCat.DiscreteExtendScalars.mapRCLM ℤ matrixRing sequenceDoubling)
      (TopModuleCat.tensorGenerator_apply ℤ C integerSequences c constantOne)).trans
        ((TopModuleCat.DiscreteExtendScalars.mapRCLM_tmul ℤ matrixRing
          sequenceDoubling c constantOne).trans
            (TopModuleCat.tensorGenerator_apply ℤ C integerSequences c
              (sequenceDoubling constantOne)).symm)
  have hmap : matrixTensorDoubling upperTensor =
      e (TopModuleCat.tensorGenerator ℤ C integerSequences c (sequenceDoubling constantOne)) :=
    (congrArg matrixTensorDoubling ht).trans
      ((TopModuleCat.DiscreteExtendScalars.mapCLM_rViewHomeomorph_apply ℤ matrixRing
        sequenceDoubling (TopModuleCat.tensorGenerator ℤ C integerSequences c constantOne)).trans
          (congrArg e hR))
  have hgenerators :
      TopModuleCat.tensorGenerator ℤ C integerSequences c (sequenceDoubling constantOne) =
        TopModuleCat.tensorGenerator ℤ C integerSequences c constantOne :=
    (e.symm_apply_apply _).symm.trans
      ((congrArg e.symm (hmap.symm.trans (h.trans ht))).trans (e.symm_apply_apply _))
  have himage := congrArg matrixTensorDetector hgenerators
  rw [matrixTensorDetector_generator_apply, matrixTensorDetector_generator_apply] at himage
  have hzero : sequenceDoubling constantOne 0 = (2 : ℤ) :=
    (sequenceDoubling_apply constantOne 0).trans (by norm_num [constantOne])
  rw [hzero] at himage
  have hone : (constantOne 0) • c = c := by
    simpa only [constantOne] using (one_smul ℤ c)
  have htwo : (2 : ℤ) • c = c + c := two_smul ℤ c
  have hc : c + c = c := htwo.symm.trans (himage.trans hone)
  have h01 := congrArg (fun z : C ↦ (show matrixRing from z) (0 : Fin 2) (1 : Fin 2)) hc
  rw [matrixCoefficient_add_apply] at h01
  norm_num [c, upperUnit] at h01

/-- The extended map's pure-tensor value is fixed by the public API. -/
theorem matrixTensorDoubling_upper :
    matrixTensorDoubling upperTensor = upperUnit ⊗ₜ[ℤ] sequenceDoubling constantOne := by
  exact TopModuleCat.DiscreteExtendScalars.mapCLM_tmul ℤ matrixRing
    sequenceDoubling upperUnit constantOne

/-- The unit of scalar extension lies in its base-linear view. -/
noncomputable def matrixUnitTensor :
    TopModuleCat.discreteExtendScalarsRObj ℤ matrixRing integerSequences :=
  TopModuleCat.DiscreteExtendScalars.unitContinuous ℤ matrixRing integerSequences constantOne

/-- Reversing coefficient multiplication changes its action on the unit tensor.
Both fixed multiplication maps are base-linear, not asserted to be matrix-linear. -/
theorem matrixScalar_order_sensitive :
    TopModuleCat.DiscreteExtendScalars.scalarRCLM ℤ matrixRing integerSequences upperUnit
        (TopModuleCat.DiscreteExtendScalars.scalarRCLM ℤ matrixRing integerSequences lowerUnit
          matrixUnitTensor) ≠
      TopModuleCat.DiscreteExtendScalars.scalarRCLM ℤ matrixRing integerSequences lowerUnit
        (TopModuleCat.DiscreteExtendScalars.scalarRCLM ℤ matrixRing integerSequences upperUnit
          matrixUnitTensor) := by
  intro h
  have hu : matrixUnitTensor = (1 : matrixRing) ⊗ₜ[ℤ] constantOne :=
    TopModuleCat.DiscreteExtendScalars.unitContinuous_apply ℤ matrixRing
      integerSequences constantOne
  have hlower :
      TopModuleCat.DiscreteExtendScalars.scalarRCLM ℤ matrixRing integerSequences lowerUnit
          matrixUnitTensor = lowerUnit ⊗ₜ[ℤ] constantOne := by
    rw [hu]
    simpa only [mul_one] using
      TopModuleCat.DiscreteExtendScalars.scalarRCLM_tmul ℤ matrixRing integerSequences
        lowerUnit (1 : matrixRing) constantOne
  have hupper :
      TopModuleCat.DiscreteExtendScalars.scalarRCLM ℤ matrixRing integerSequences upperUnit
          matrixUnitTensor = upperUnit ⊗ₜ[ℤ] constantOne := by
    rw [hu]
    simpa only [mul_one] using
      TopModuleCat.DiscreteExtendScalars.scalarRCLM_tmul ℤ matrixRing integerSequences
        upperUnit (1 : matrixRing) constantOne
  have hleft :
      TopModuleCat.DiscreteExtendScalars.scalarRCLM ℤ matrixRing integerSequences upperUnit
          (TopModuleCat.DiscreteExtendScalars.scalarRCLM ℤ matrixRing integerSequences lowerUnit
            matrixUnitTensor) = (upperUnit * lowerUnit) ⊗ₜ[ℤ] constantOne :=
    (congrArg
      (TopModuleCat.DiscreteExtendScalars.scalarRCLM ℤ matrixRing integerSequences upperUnit)
      hlower).trans
        (TopModuleCat.DiscreteExtendScalars.scalarRCLM_tmul ℤ matrixRing integerSequences
          upperUnit lowerUnit constantOne)
  have hright :
      TopModuleCat.DiscreteExtendScalars.scalarRCLM ℤ matrixRing integerSequences lowerUnit
          (TopModuleCat.DiscreteExtendScalars.scalarRCLM ℤ matrixRing integerSequences upperUnit
            matrixUnitTensor) = (lowerUnit * upperUnit) ⊗ₜ[ℤ] constantOne :=
    (congrArg
      (TopModuleCat.DiscreteExtendScalars.scalarRCLM ℤ matrixRing integerSequences lowerUnit)
      hupper).trans
        (TopModuleCat.DiscreteExtendScalars.scalarRCLM_tmul ℤ matrixRing integerSequences
          lowerUnit upperUnit constantOne)
  let C := TopModuleCat.DiscreteExtendScalars.coefficient ℤ matrixRing
  let cLeft : C := upperUnit * lowerUnit
  let cRight : C := lowerUnit * upperUnit
  have hgenerators :
      TopModuleCat.tensorGenerator ℤ C integerSequences cLeft constantOne =
        TopModuleCat.tensorGenerator ℤ C integerSequences cRight constantOne :=
    (TopModuleCat.tensorGenerator_apply ℤ C integerSequences cLeft constantOne).trans
      ((hleft.symm.trans (h.trans hright)).trans
        (TopModuleCat.tensorGenerator_apply ℤ C integerSequences cRight constantOne).symm)
  have himage := congrArg matrixTensorDetector hgenerators
  rw [matrixTensorDetector_generator_apply, matrixTensorDetector_generator_apply] at himage
  have honeLeft : (constantOne 0) • cLeft = cLeft := by
    simpa only [constantOne] using (one_smul ℤ cLeft)
  have honeRight : (constantOne 0) • cRight = cRight := by
    simpa only [constantOne] using (one_smul ℤ cRight)
  have hcoeff : cLeft = cRight := honeLeft.symm.trans (himage.trans honeRight)
  exact matrixUnits_noncommute (congrArg (fun c : C ↦ (show matrixRing from c)) hcoeff)

namespace RankOne

universe uR uK

/-- The regular left module, bundled without an algebra parameter. -/
abbrev regularModuleCat (K : Type uK) [Ring K] : ModuleCat K := ModuleCat.of K K

/-- The stored regular action is multiplication, independently of any algebra map. -/
theorem regularModuleCat_smul (K : Type uK) [Ring K]
    (k : K) (c : regularModuleCat K) : k • c = k * c := rfl

/-- The regular topological module, bundled without an algebra parameter. -/
abbrev regularTopModule (R : Type uR) [Ring R] [TopologicalSpace R]
    [IsTopologicalRing R] : TopModuleCat R := TopModuleCat.of R R

/-- The regular input action is multiplication, independently of any coefficient algebra. -/
theorem regularTopModule_smul (R : Type uR) [Ring R] [TopologicalSpace R]
    [IsTopologicalRing R] (r : R) (m : regularTopModule R) : r • m = r * m := rfl

section Comparison

variable (R : Type uR) (K : Type uK) [CommRing R] [Ring K] [Algebra R K]
variable [TopologicalSpace R] [IsTopologicalRing R]
variable [TopologicalSpace K] [DiscreteTopology K]

/-- Rank-one scalar extension is coefficient-linearly equivalent to the regular
coefficient module. The input's regular base action is bundled separately. -/
noncomputable def comparison :
    (TopModuleCat.discreteExtendScalarsObj R K (regularTopModule R)).toModuleCat ≃ₗ[K]
      regularModuleCat K := by
  letI : Module R (TopModuleCat.DiscreteExtendScalars.coefficient R K) :=
    (TopModuleCat.DiscreteExtendScalars.coefficient R K).isModule
  letI : Module K (TopModuleCat.DiscreteExtendScalars.coefficient R K) :=
    TopModuleCat.DiscreteExtendScalars.regularModule K
  letI : SMulCommClass R K (TopModuleCat.DiscreteExtendScalars.coefficient R K) :=
    TopModuleCat.DiscreteExtendScalars.coefficientSMulCommClass R K
  letI : IsScalarTower R K (TopModuleCat.DiscreteExtendScalars.coefficient R K) :=
    TopModuleCat.DiscreteExtendScalars.coefficientIsScalarTower R K
  exact TensorProduct.AlgebraTensorModule.rid R K
    (TopModuleCat.DiscreteExtendScalars.coefficient R K)

/-- The rank-one comparison evaluates a tensor using the specified algebra map. -/
@[simp]
theorem comparison_tmul (c : K) (m : regularTopModule R) :
    comparison R K (c ⊗ₜ[R] m) = algebraMap R K m * c := by
  let : Module R (TopModuleCat.DiscreteExtendScalars.coefficient R K) :=
    (TopModuleCat.DiscreteExtendScalars.coefficient R K).isModule
  let : Module K (TopModuleCat.DiscreteExtendScalars.coefficient R K) :=
    TopModuleCat.DiscreteExtendScalars.regularModule K
  let : SMulCommClass R K (TopModuleCat.DiscreteExtendScalars.coefficient R K) :=
    TopModuleCat.DiscreteExtendScalars.coefficientSMulCommClass R K
  let : IsScalarTower R K (TopModuleCat.DiscreteExtendScalars.coefficient R K) :=
    TopModuleCat.DiscreteExtendScalars.coefficientIsScalarTower R K
  exact (TensorProduct.AlgebraTensorModule.rid_tmul (R := R) (A := K)
    (M := TopModuleCat.DiscreteExtendScalars.coefficient R K) m c).trans
      (TopModuleCat.DiscreteExtendScalars.coefficient_smul R K m c)

/-- The inverse rank-one comparison puts a coefficient in the left tensor factor. -/
@[simp]
theorem comparison_symm_apply (c : regularModuleCat K) :
    (comparison R K).symm c = c ⊗ₜ[R] (1 : regularTopModule R) := by
  let : Module R (TopModuleCat.DiscreteExtendScalars.coefficient R K) :=
    (TopModuleCat.DiscreteExtendScalars.coefficient R K).isModule
  let : Module K (TopModuleCat.DiscreteExtendScalars.coefficient R K) :=
    TopModuleCat.DiscreteExtendScalars.regularModule K
  let : SMulCommClass R K (TopModuleCat.DiscreteExtendScalars.coefficient R K) :=
    TopModuleCat.DiscreteExtendScalars.coefficientSMulCommClass R K
  let : IsScalarTower R K (TopModuleCat.DiscreteExtendScalars.coefficient R K) :=
    TopModuleCat.DiscreteExtendScalars.coefficientIsScalarTower R K
  exact TensorProduct.AlgebraTensorModule.rid_symm_apply R K
    (M := TopModuleCat.DiscreteExtendScalars.coefficient R K) c

/-- The rank-one comparison sends the unit at `m` to its algebra-map image. -/
@[simp]
theorem comparison_unit (m : regularTopModule R) :
    comparison R K
      (TopModuleCat.DiscreteExtendScalars.rViewHomeomorph R K (regularTopModule R)
        (TopModuleCat.DiscreteExtendScalars.unitContinuous R K (regularTopModule R) m)) =
      algebraMap R K m := by
  rw [TopModuleCat.DiscreteExtendScalars.rViewHomeomorph_apply,
    TopModuleCat.DiscreteExtendScalars.unitContinuous_apply, comparison_tmul, mul_one]

/-- In the regular comparison target, coefficient scalars act by multiplication. -/
theorem comparison_smul (k : K)
    (x : TopModuleCat.discreteExtendScalarsObj R K (regularTopModule R)) :
    comparison R K (k • x) = k * comparison R K x := by
  rw [map_smul, regularModuleCat_smul]

/-- The base action on the unit is evaluated using the unit's base linearity
and the separately bundled regular input action. -/
theorem comparison_base_smul_unit (r : R) :
    comparison R K
      (TopModuleCat.DiscreteExtendScalars.rViewHomeomorph R K (regularTopModule R)
        (r • TopModuleCat.DiscreteExtendScalars.unitContinuous R K (regularTopModule R)
          (1 : regularTopModule R))) = algebraMap R K r := by
  rw [← (TopModuleCat.DiscreteExtendScalars.unitContinuous R K
    (regularTopModule R)).map_smul r (1 : regularTopModule R),
    regularTopModule_smul, mul_one, comparison_unit]

/-- On a unit tensor, an extended regular-input map evaluates at the algebra-map
image of the input map's value. -/
theorem comparison_map_unit (g : regularTopModule R →L[R] regularTopModule R)
    (m : regularTopModule R) :
    comparison R K
      (TopModuleCat.DiscreteExtendScalars.mapCLM R K g
        (TopModuleCat.DiscreteExtendScalars.rViewHomeomorph R K (regularTopModule R)
          (TopModuleCat.DiscreteExtendScalars.unitContinuous R K (regularTopModule R) m))) =
      algebraMap R K (g m) := by
  rw [TopModuleCat.DiscreteExtendScalars.rViewHomeomorph_apply,
    TopModuleCat.DiscreteExtendScalars.unitContinuous_apply,
    TopModuleCat.DiscreteExtendScalars.mapCLM_tmul, comparison_tmul, mul_one]

end Comparison

/-- The same commutative nonfield ring is used for both scalar types. -/
abbrev integerPairRing := ℤ × ℤ

/-- The first coordinate idempotent. -/
def firstIdempotent : integerPairRing := (1, 0)

/-- The second coordinate idempotent. -/
def secondIdempotent : integerPairRing := (0, 1)

/-- The product of discrete integer topologies is discrete. -/
theorem integerPairRing_discrete : DiscreteTopology integerPairRing := inferInstance

/-- The regular input, frozen before the swapping algebra structure is chosen. -/
abbrev regularInput : TopModuleCat integerPairRing := regularTopModule integerPairRing

/-- The regular coefficient target, frozen before the swapping algebra is chosen. -/
abbrev regularTarget : ModuleCat integerPairRing := regularModuleCat integerPairRing

/-- The input's first-coordinate projection is continuous and regular-base-linear. -/
noncomputable def regularProjection : regularInput →L[integerPairRing] regularInput :=
  firstIdempotent • ContinuousLinearMap.id integerPairRing regularInput

/-- The regular projection sends the input unit to the first idempotent. -/
theorem regularProjection_one : regularProjection (1 : regularInput) = firstIdempotent := by
  change firstIdempotent * 1 = firstIdempotent
  exact mul_one _

/-- The swapping ring homomorphism. -/
def swapHom : integerPairRing →+* integerPairRing :=
  (RingEquiv.prodComm : integerPairRing ≃+* integerPairRing).toRingHom

/-- Swapping sends the first idempotent to the second. -/
@[simp]
theorem swapHom_firstIdempotent : swapHom firstIdempotent = secondIdempotent := rfl

/-- The swapping ring homomorphism is not the identity. -/
theorem swapHom_ne_id : swapHom ≠ RingHom.id integerPairRing := by
  intro h
  have h01 : (0 : ℤ) = 1 :=
    congrArg (fun x : integerPairRing ↦ x.1) (DFunLike.congr_fun h firstIdempotent)
  norm_num at h01

/-- The same-type algebra structure induced by the swapping ring homomorphism.
It is stored as data so that scalar extension does not select the identity self-algebra. -/
@[instance_reducible]
def swappingAlgebra : Algebra integerPairRing integerPairRing := swapHom.toAlgebra

section SwappingAlgebra

/-- The chosen same-type algebra map is swapping, not the identity map. -/
theorem algebraMap_eq_swapHom :
    @algebraMap integerPairRing integerPairRing _ _ swappingAlgebra = swapHom := rfl

/-- The same-type algebra structure has a nonidentity algebra map. -/
theorem algebraMap_ne_id :
    @algebraMap integerPairRing integerPairRing _ _ swappingAlgebra ≠ RingHom.id integerPairRing :=
  swapHom_ne_id

/-- The bundled coefficient base action is multiplication by the swapped scalar. -/
theorem swappingCoefficient_smul (r : integerPairRing)
    (c : @TopModuleCat.DiscreteExtendScalars.coefficient
      integerPairRing integerPairRing _ _ swappingAlgebra) :
    @SMul.smul integerPairRing
      (@TopModuleCat.DiscreteExtendScalars.coefficient
        integerPairRing integerPairRing _ _ swappingAlgebra)
      (@TopModuleCat.DiscreteExtendScalars.coefficient
        integerPairRing integerPairRing _ _ swappingAlgebra).isModule.toSMul r c = swapHom r * c :=
  @TopModuleCat.DiscreteExtendScalars.coefficient_smul
    integerPairRing integerPairRing _ _ swappingAlgebra r c

/-- The base-linear view uses the swapping coefficient action and the regular input. -/
noncomputable def swappingRView : TopModuleCat integerPairRing :=
  @TopModuleCat.discreteExtendScalarsRObj
    integerPairRing integerPairRing _ _ swappingAlgebra _ regularInput

/-- The coefficient-linear view has regular coefficient multiplication. -/
noncomputable def swappingKView : TopModuleCat integerPairRing :=
  @TopModuleCat.discreteExtendScalarsObj
    integerPairRing integerPairRing _ _ swappingAlgebra _ _ _ regularInput

/-- The base view has exactly the primitive one-sided tensor topology. -/
theorem swappingRView_topology :
    swappingRView.topologicalSpace =
      (TopModuleCat.tensorLeftObj integerPairRing
        (@TopModuleCat.DiscreteExtendScalars.coefficient
          integerPairRing integerPairRing _ _ swappingAlgebra)
        regularInput).topologicalSpace := rfl

/-- The coefficient view retains exactly the topology of the base view. -/
theorem swappingKView_topology :
    @Eq (TopologicalSpace
      (@TensorProduct integerPairRing
        (@CommRing.toCommSemiring integerPairRing (inferInstance : CommRing integerPairRing))
        (@TopModuleCat.DiscreteExtendScalars.coefficient
          integerPairRing integerPairRing _ _ swappingAlgebra) regularInput
        (@TopModuleCat.DiscreteExtendScalars.coefficient
          integerPairRing integerPairRing _ _ swappingAlgebra).isAddCommGroup.toAddCommMonoid
        regularInput.toModuleCat.isAddCommGroup.toAddCommMonoid
        (@TopModuleCat.DiscreteExtendScalars.coefficient
          integerPairRing integerPairRing _ _ swappingAlgebra).isModule
        regularInput.toModuleCat.isModule))
      swappingKView.topologicalSpace swappingRView.topologicalSpace :=
  @TopModuleCat.discreteExtendScalarsObj_topologicalSpace
    integerPairRing integerPairRing _ _ swappingAlgebra _ _ _ regularInput

/-- The rank-one comparison targets the separately bundled regular coefficient module. -/
noncomputable def swappingComparison : swappingKView.toModuleCat ≃ₗ[integerPairRing]
    regularTarget :=
  @comparison integerPairRing integerPairRing _ _ swappingAlgebra _ _ _ _

/-- On every regular input vector, the rank-one comparison of the unit is swapping. -/
theorem swappingComparison_unit_apply (m : regularInput) :
    swappingComparison
      (@TopModuleCat.DiscreteExtendScalars.rViewHomeomorph
        integerPairRing integerPairRing _ _ swappingAlgebra _ _ _ regularInput
        (@TopModuleCat.DiscreteExtendScalars.unitContinuous
          integerPairRing integerPairRing _ _ swappingAlgebra _ regularInput m)) = swapHom m :=
  @comparison_unit integerPairRing integerPairRing _ _ swappingAlgebra _ _ _ _ m

/-- The unit at the regular input vector `1`, in the base-linear view. -/
noncomputable def unitR : swappingRView :=
  @TopModuleCat.DiscreteExtendScalars.unitContinuous
    integerPairRing integerPairRing _ _ swappingAlgebra _ regularInput (1 : regularInput)

/-- The corresponding unit vector in the coefficient-linear view. -/
noncomputable def unitK : swappingKView :=
  @TopModuleCat.DiscreteExtendScalars.rViewHomeomorph
    integerPairRing integerPairRing _ _ swappingAlgebra _ _ _ regularInput unitR

/-- The rank-one comparison sends the unit vector to the nonzero ring unit. -/
@[simp]
theorem swappingComparison_unit : swappingComparison unitK = (1 : integerPairRing) :=
  (swappingComparison_unit_apply (1 : regularInput)).trans swapHom.map_one

/-- The coefficient-linear unit vector is nonzero. -/
theorem unitK_ne_zero : unitK ≠ 0 := by
  intro h
  have himage := congrArg swappingComparison h
  rw [swappingComparison_unit, map_zero] at himage
  have h10 : (1 : ℤ) = 0 := congrArg (fun x : integerPairRing ↦ x.1) himage
  norm_num at h10

/-- The base-linear unit vector is nonzero as well. -/
theorem unitR_ne_zero : unitR ≠ 0 := by
  intro h
  apply unitK_ne_zero
  exact congrArg (@TopModuleCat.DiscreteExtendScalars.rViewHomeomorph
    integerPairRing integerPairRing _ _ swappingAlgebra _ _ _ regularInput) h

/-- Apply the base action of the first idempotent, then compare the two carriers. -/
noncomputable def baseAction : swappingRView → swappingKView := fun x ↦
  @TopModuleCat.DiscreteExtendScalars.rViewHomeomorph
    integerPairRing integerPairRing _ _ swappingAlgebra _ _ _ regularInput
    (@SMul.smul integerPairRing swappingRView swappingRView.toModuleCat.isModule.toSMul
      firstIdempotent x)

/-- Apply the coefficient action of the first idempotent on the corresponding carrier. -/
noncomputable def coefficientAction : swappingRView → swappingKView := fun x ↦
  @SMul.smul integerPairRing swappingKView swappingKView.toModuleCat.isModule.toSMul
    firstIdempotent (@TopModuleCat.DiscreteExtendScalars.rViewHomeomorph
      integerPairRing integerPairRing _ _ swappingAlgebra _ _ _ regularInput x)

/-- The base action on the unit has the swapped image `(0, 1)`. -/
theorem baseAction_unit_image :
    swappingComparison (baseAction unitR) = secondIdempotent := by
  calc
    swappingComparison (baseAction unitR) = swapHom firstIdempotent :=
      @comparison_base_smul_unit
        integerPairRing integerPairRing _ _ swappingAlgebra _ _ _ _ firstIdempotent
    _ = secondIdempotent := swapHom_firstIdempotent

/-- The coefficient action on the unit has the regular image `(1, 0)`. -/
theorem coefficientAction_unit_image :
    swappingComparison (coefficientAction unitR) = firstIdempotent := by
  calc
    swappingComparison (coefficientAction unitR) =
        firstIdempotent * swappingComparison unitK :=
      @comparison_smul
        integerPairRing integerPairRing _ _ swappingAlgebra _ _ _ _ firstIdempotent unitK
    _ = firstIdempotent := by rw [swappingComparison_unit, mul_one]

/-- The base and coefficient actions differ on the nonzero unit vector. -/
theorem baseAction_unit_ne_coefficientAction_unit :
    baseAction unitR ≠ coefficientAction unitR := by
  intro h
  have himage := congrArg swappingComparison h
  rw [baseAction_unit_image, coefficientAction_unit_image] at himage
  have h01 : (0 : ℤ) = 1 := congrArg (fun x : integerPairRing ↦ x.1) himage
  norm_num at h01

/-- Equal scalar types do not make the two action maps equal. -/
theorem baseAction_ne_coefficientAction : baseAction ≠ coefficientAction := by
  intro h
  exact baseAction_unit_ne_coefficientAction_unit (congrFun h unitR)

/-- Scalar extension of the frozen regular-input projection. -/
noncomputable def tensorProjection : swappingKView →L[integerPairRing] swappingKView :=
  @TopModuleCat.DiscreteExtendScalars.mapCLM
    integerPairRing integerPairRing _ _ swappingAlgebra _ _ _
    regularInput regularInput regularProjection

/-- The extended projection sends the unit to a vector with image `(0, 1)`. -/
theorem tensorProjection_unit_image :
    swappingComparison (tensorProjection unitK) = secondIdempotent := by
  calc
    swappingComparison (tensorProjection unitK) = swapHom (regularProjection 1) :=
      @comparison_map_unit integerPairRing integerPairRing _ _ swappingAlgebra _ _ _ _
        regularProjection (1 : regularInput)
    _ = secondIdempotent := by rw [regularProjection_one, swapHom_firstIdempotent]

/-- The extended projection has a nonzero value on the unit. -/
theorem tensorProjection_unit_ne_zero : tensorProjection unitK ≠ 0 := by
  intro h
  have himage := congrArg swappingComparison h
  rw [tensorProjection_unit_image, map_zero] at himage
  have h10 : (1 : ℤ) = 0 := congrArg (fun x : integerPairRing ↦ x.2) himage
  norm_num at h10

/-- The extended projection moves the unit vector. -/
theorem tensorProjection_unit_ne_unit : tensorProjection unitK ≠ unitK := by
  intro h
  have himage := congrArg swappingComparison h
  rw [tensorProjection_unit_image, swappingComparison_unit] at himage
  have h01 : (0 : ℤ) = 1 := congrArg (fun x : integerPairRing ↦ x.1) himage
  norm_num at h01

/-- The extended projection is not the zero map. -/
theorem tensorProjection_ne_zero : tensorProjection ≠ 0 := by
  intro h
  apply tensorProjection_unit_ne_zero
  rw [h]
  rfl

/-- The extended projection is not the identity map. -/
theorem tensorProjection_ne_id :
    tensorProjection ≠ ContinuousLinearMap.id integerPairRing swappingKView := by
  intro h
  apply tensorProjection_unit_ne_unit
  rw [h]
  rfl

end SwappingAlgebra

end RankOne

end DiscreteScalarExtensionExamples
