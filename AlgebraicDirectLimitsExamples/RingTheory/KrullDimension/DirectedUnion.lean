/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicDirectLimits.RingTheory.KrullDimension.DirectedUnion
public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Ring.Int.Field
public import Mathlib.Data.Rat.Lemmas
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.KrullDimension.PID

/-!
# Integer and rational subsemiring unions

The two-stage family consisting of the integer image in `ℚ` and the whole
rational semiring is directed and nonconstant. The first stage has dimension
one, the second and their union have dimension zero, and the supremum of the
stage dimensions is one. The rational number `1 / 2` witnesses that the first
stage inclusion into the union is not surjective.

The dimension inequality is derived directly from finite-subset capture, using
the terminal rational stage, independently of the general directed-union bound.
The same family also instantiates `Subsemiring.ringKrullDim_iSup_le`.
The empty-index example is vacuously directed but violates that bound: its
supremum still contains distinct zero and one, while its dimension supremum is
`⊥`.

## References

The numerical dimensions use Mathlib's field and principal-ideal-domain dimension
theorems. The integer image is identified with `ℤ` using
`RingEquiv.ofLeftInverseS` and the rational numerator. All subsemiring structures,
stage inclusions, and their canonical instances are Mathlib's.
-/

@[expose] public section

namespace DirectedUnionExamples

private def rationalStages : Bool → Subsemiring ℚ
  | false => (Int.castRingHom ℚ).rangeS
  | true => ⊤

private theorem rationalStages_directed : Directed (· ≤ ·) rationalStages := by
  intro i j
  exact ⟨true, le_top, le_top⟩

private theorem rationalStages_iSup : (⨆ i, rationalStages i : Subsemiring ℚ) = ⊤ :=
  top_unique (le_iSup rationalStages true)

private theorem half_not_mem_integerStage : (1 / 2 : ℚ) ∉ rationalStages false := by
  intro hx
  obtain ⟨z, hz⟩ := RingHom.mem_rangeS.mp hx
  have hden : (1 : ℕ) = 2 := by
    simpa only [Int.coe_castRingHom, Rat.den_intCast, one_div, Rat.inv_ofNat_den] using
      congrArg Rat.den hz
  exact (by decide : (1 : ℕ) ≠ 2) hden

private theorem rationalStages_strict : rationalStages false < rationalStages true := by
  exact SetLike.lt_iff_le_and_exists.mpr
    ⟨le_top, (1 / 2 : ℚ), Subsemiring.mem_top _, half_not_mem_integerStage⟩

private theorem integerStage_inclusion_not_surjective :
    ¬ Function.Surjective (Subsemiring.inclusion (le_iSup rationalStages false)) := by
  intro hsurj
  have hhalf : (1 / 2 : ℚ) ∈ (⨆ i, rationalStages i : Subsemiring ℚ) := by
    rw [rationalStages_iSup]
    exact Subsemiring.mem_top _
  obtain ⟨x, hx⟩ := hsurj ⟨(1 / 2 : ℚ), hhalf⟩
  have hx' : (x : ℚ) = (1 / 2 : ℚ) := congrArg Subtype.val hx
  exact half_not_mem_integerStage (hx' ▸ x.property)

private theorem integerStage_dimension : ringKrullDim (rationalStages false) = 1 := by
  have e : ℤ ≃+* (Int.castRingHom ℚ).rangeS :=
    RingEquiv.ofLeftInverseS (f := Int.castRingHom ℚ) (g := Rat.num) (by intro z; rfl)
  calc
    ringKrullDim (rationalStages false) = ringKrullDim ℤ := e.ringKrullDim.symm
    _ = 1 := IsPrincipalIdealRing.ringKrullDim_eq_one ℤ Int.not_isField

private theorem rationalStage_dimension : ringKrullDim (rationalStages true) = 0 := by
  exact (Subsemiring.topEquiv : (⊤ : Subsemiring ℚ) ≃+* ℚ).ringKrullDim.trans
    (ringKrullDim_eq_zero_of_field ℚ)

private theorem rationalUnion_dimension :
    ringKrullDim (⨆ i, rationalStages i : Subsemiring ℚ) = 0 := by
  rw [rationalStages_iSup]
  exact rationalStage_dimension

private theorem rationalStages_dimension_iSup : (⨆ i, ringKrullDim (rationalStages i)) = 1 := by
  rw [iSup_bool_eq, rationalStage_dimension, integerStage_dimension]
  exact sup_eq_right.mpr (by decide : (0 : WithBot ℕ∞) ≤ 1)

private theorem rationalStages_capture (E : Set (⨆ i, rationalStages i : Subsemiring ℚ)) :
    ∃ i, E ⊆ Set.range (Subsemiring.inclusion (le_iSup rationalStages i)) := by
  refine ⟨true, fun x _ => ?_⟩
  exact ⟨⟨x.val, Subsemiring.mem_top _⟩, rfl⟩

private theorem rationalUnion_dimension_bound :
    ringKrullDim (⨆ i, rationalStages i : Subsemiring ℚ) ≤
      ⨆ i, ringKrullDim (rationalStages i) := by
  exact ringKrullDim_le_iSup_of_finite_subset_range
    (fun i => Subsemiring.inclusion (le_iSup rationalStages i))
    (fun E _ => rationalStages_capture E)

private theorem rationalUnion_dimension_le_iSup :
    ringKrullDim (⨆ i, rationalStages i : Subsemiring ℚ) ≤
      ⨆ i, ringKrullDim (rationalStages i) :=
  Subsemiring.ringKrullDim_iSup_le rationalStages rationalStages_directed

/-- A nonconstant directed integer-to-rational family has a proper first stage,
non-surjective first-stage inclusion, dimension-zero union, and a finite, positive
stage-dimension supremum. Its dimension bound follows from finite-subset capture. -/
theorem exists_proper_integer_rational_union :
    ∃ s : Bool → Subsemiring ℚ,
      Directed (· ≤ ·) s ∧ s false < s true ∧
      ¬ Function.Surjective (Subsemiring.inclusion (le_iSup s false)) ∧
      ringKrullDim (s false) = 1 ∧ ringKrullDim (s true) = 0 ∧
      ringKrullDim (⨆ i, s i : Subsemiring ℚ) = 0 ∧ (⨆ i, ringKrullDim (s i)) = 1 ∧
      ringKrullDim (⨆ i, s i : Subsemiring ℚ) ≤ ⨆ i, ringKrullDim (s i) := by
  exact ⟨rationalStages, rationalStages_directed, rationalStages_strict,
    integerStage_inclusion_not_surjective, integerStage_dimension, rationalStage_dimension,
    rationalUnion_dimension, rationalStages_dimension_iSup, rationalUnion_dimension_bound⟩

/-- An empty family is directed but does not satisfy the directed-union dimension
inequality, even in the nontrivial ambient semiring `ℚ`. -/
theorem empty_family_dimension_bound_fails :
    Directed (· ≤ ·) (fun i : Empty => (Empty.elim i : Subsemiring ℚ)) ∧
      ¬ (ringKrullDim (⨆ i : Empty, (Empty.elim i : Subsemiring ℚ) : Subsemiring ℚ) ≤
        ⨆ i : Empty, ringKrullDim (Empty.elim i : Subsemiring ℚ)) := by
  constructor
  · intro i
    exact isEmptyElim i
  · intro h
    have hsup : (⨆ i : Empty, (Empty.elim i : Subsemiring ℚ) : Subsemiring ℚ) = ⊥ := by
      simp
    have hdim := congrArg (fun A : Subsemiring ℚ => ringKrullDim A) hsup
    have hbot : ringKrullDim (⊥ : Subsemiring ℚ) = ⊥ :=
      le_bot_iff.mp (by simpa only [hdim, iSup_of_empty] using h)
    have hsub := ringKrullDim_eq_bot_iff_subsingleton.mp hbot
    have hzero_one : (0 : ℚ) = 1 :=
      congrArg Subtype.val (@Subsingleton.elim (⊥ : Subsemiring ℚ) hsub 0 1)
    exact zero_ne_one hzero_one

end DirectedUnionExamples
