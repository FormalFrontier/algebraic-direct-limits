/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
module

public import AlgebraicDirectLimits
public import Mathlib.Algebra.Group.PUnit
public import Mathlib.Algebra.Group.Int.Defs

/-! Public-root client for native graded stabilization, including noncancellative boundaries. -/

set_option warningAsError true

public section

noncomputable section

namespace AlgebraicDirectLimits.Tests.GradedStabilization

open Algebra Algebra.GrothendieckAddGroup
open Algebra.GrothendieckAddGroup.GradedStabilization

universe v w

private theorem induced_degree_rw {M : Type v} [AddCommMonoid M]
    {A : Type w} [AddCommMonoid A] (d : M →+ A) (m : M) :
    inducedDegree d (of m) = of (d m) := by
  rw [inducedDegree_of]

private theorem induced_degree_simp {M : Type v} [AddCommMonoid M]
    {A : Type w} [AddCommMonoid A] (d : M →+ A) (m : M) :
    inducedDegree d (of m) = of (d m) := by
  simp

private theorem induced_degree_native_simp {M : Type v} [AddCommMonoid M]
    {A : Type w} [AddCommMonoid A] (d : M →+ A) (m : M) :
    inducedDegree d (AddLocalization.addMonoidOf ⊤ m) =
      AddLocalization.addMonoidOf ⊤ (d m) := by
  simp

private theorem normalization_representative_simp {M : Type v} [AddCommMonoid M]
    {A : Type w} [AddCommMonoid A] (d : M →+ A) (u : M) (n : ℕ)
    (m : degreeFiber d u n) :
    (normalization d u ⟦⟨n, m⟩⟧).1 = of m.1 - n • of u := by
  simp

private theorem normalization_equiv_representative_simp {M : Type v} [AddCommMonoid M]
    {A : Type w} [AddCommMonoid A] [IsCancelAdd A] (d : M →+ A) (u : M)
    (hu : (AddSubmonoid.multiples u).saturation = ⊤) (n : ℕ) (m : degreeFiber d u n) :
    (normalizationEquiv d u hu ⟦⟨n, m⟩⟧).1 = of m.1 - n • of u := by
  simp

private noncomputable def nativeKernelEquiv {M : Type v} [AddCommMonoid M]
    {A : Type w} [AddCommMonoid A]
    [IsCancelAdd A] (d : M →+ A) (u : M)
    (hu : (AddSubmonoid.multiples u).saturation = ⊤) :
    DirectLimit (degreeFiber d u) (transition d u) ≃ (inducedDegree d).ker :=
  normalizationEquiv d u hu

private theorem nativeKernelEquiv_symm_apply {M : Type v} [AddCommMonoid M]
    {A : Type w} [AddCommMonoid A]
    [IsCancelAdd A] (d : M →+ A) (u : M)
    (hu : (AddSubmonoid.multiples u).saturation = ⊤)
    (x : DirectLimit (degreeFiber d u) (transition d u)) :
    (normalizationEquiv d u hu).symm (normalizationEquiv d u hu x) = x :=
  (normalizationEquiv d u hu).symm_apply_apply x

private theorem nativeKernelEquiv_apply_symm {M : Type v} [AddCommMonoid M]
    {A : Type w} [AddCommMonoid A]
    [IsCancelAdd A] (d : M →+ A) (u : M)
    (hu : (AddSubmonoid.multiples u).saturation = ⊤) (z : (inducedDegree d).ker) :
    normalizationEquiv d u hu ((normalizationEquiv d u hu).symm z) = z :=
  (normalizationEquiv d u hu).apply_symm_apply z

theorem nat_one_cofinal : (AddSubmonoid.multiples (1 : ℕ)).saturation = ⊤ := by
  ext n
  constructor
  · intro _; trivial
  · intro _
    apply AddSubmonoid.mem_saturation_iff.mpr
    exact ⟨0, n, by simp⟩

/-- Zero degree is allowed, and its normalized kernel need not be trivial. -/
theorem zero_degree_distinguishes :
    normalization (0 : ℕ →+ ℕ) 1 ⟦⟨0, ⟨0, rfl⟩⟩⟧ ≠
      normalization (0 : ℕ →+ ℕ) 1 ⟦⟨0, ⟨1, rfl⟩⟩⟧ := by
  intro h
  have heq := congrArg Subtype.val h
  change of (0 : ℕ) - 0 • of 1 = of 1 - 0 • of 1 at heq
  have h01 : of (0 : ℕ) = of 1 := by simpa using heq
  exact Nat.zero_ne_one (of_injective h01)

/-- Zero-degree stabilization of the additive natural numbers. -/
noncomputable def zeroDegreeEquiv :=
  normalizationEquiv (0 : ℕ →+ ℕ) 1 nat_one_cofinal

/-- Multiplicative naturals, viewed additively, have an absorbing element.
This is an existing type, not a new completion or quotient. -/
theorem absorbing_cofinal :
    (AddSubmonoid.multiples (Additive.ofMul (0 : ℕ))).saturation = ⊤ := by
  ext n
  constructor
  · intro _; trivial
  · intro _
    apply AddSubmonoid.mem_saturation_iff.mpr
    refine ⟨Additive.ofMul 0, 1, ?_⟩
    change (0 : ℕ) ^ 1 = n.toMul * 0
    simp

/-- The absorbing element in the stage-zero fiber for multiplicative naturals. -/
def absorbingZero : degreeFiber (0 : Additive ℕ →+ ℕ) (Additive.ofMul 0) 0 :=
  ⟨Additive.ofMul 0, rfl⟩

/-- The unit in the same stage-zero fiber, distinct before stabilization. -/
def absorbingOne : degreeFiber (0 : Additive ℕ →+ ℕ) (Additive.ofMul 0) 0 :=
  ⟨Additive.ofMul 1, rfl⟩

theorem absorbing_representatives_distinct : absorbingZero ≠ absorbingOne := by
  intro h
  exact Nat.zero_ne_one (congrArg (fun x => x.1.toMul) h)

/-- The transition itself is not injective; no hidden cancellation of M. -/
theorem absorbing_transition_not_injective :
    ¬ Function.Injective (transition (0 : Additive ℕ →+ ℕ) (Additive.ofMul 0)
      0 1 (by decide)) := by
  intro h
  apply absorbing_representatives_distinct
  apply h
  apply Subtype.ext
  rfl

theorem absorbing_limit_equal :
    (⟦⟨0, absorbingZero⟩⟧ : DirectLimit (degreeFiber (0 : Additive ℕ →+ ℕ)
      (Additive.ofMul 0)) (transition (0 : Additive ℕ →+ ℕ) (Additive.ofMul 0))) =
      ⟦⟨0, absorbingOne⟩⟧ := by
  apply (mk_same_stage_eq_iff _ _ absorbing_cofinal _ _ _).mpr
  exact ⟨1, rfl⟩

/-- Normalization with a noncancellative source and absorbing stabilizer. -/
noncomputable def absorbingEquiv :=
  normalizationEquiv (0 : Additive ℕ →+ ℕ) (Additive.ofMul 0) absorbing_cofinal

/-- Zero is cofinal in an additive group; a positive-degree premise is absent. -/
theorem group_zero_cofinal {G : Type v} [AddCommGroup G] :
    (AddSubmonoid.multiples (0 : G)).saturation = ⊤ := by
  ext g
  constructor
  · intro _; trivial
  · intro _
    apply AddSubmonoid.mem_saturation_iff.mpr
    exact ⟨-g, 0, by simp⟩

/-- Normalization for the zero degree and zero stabilizer on the integers. -/
noncomputable def groupZeroEquiv :=
  normalizationEquiv (0 : ℤ →+ ℕ) 0 group_zero_cofinal

private noncomputable def punitKernelEquiv : DirectLimit (degreeFiber (0 : PUnit →+ ℕ) 0)
    (transition (0 : PUnit →+ ℕ) 0) ≃ (inducedDegree (0 : PUnit →+ ℕ)).ker :=
  normalizationEquiv _ _ group_zero_cofinal

/-- The degree codomain can be genuinely componentwise. -/
theorem product_diagonal_cofinal :
    (AddSubmonoid.multiples ((1, 1) : ℕ × ℕ)).saturation = ⊤ := by
  ext p
  constructor
  · intro _; trivial
  · intro _
    apply AddSubmonoid.mem_saturation_iff.mpr
    refine ⟨(p.2, p.1), p.1 + p.2, ?_⟩
    apply Prod.ext <;> simp [add_comm]

/-- Normalization for the componentwise degree on pairs of natural numbers. -/
noncomputable def componentwiseEquiv :=
  normalizationEquiv (AddMonoidHom.id (ℕ × ℕ)) (1, 1) product_diagonal_cofinal

/-- Native cross-stage equality does not require cancellation of the degree target. -/
theorem arbitrary_target_cross_stage {A : Type w} [AddCommMonoid A] :
    (⟦⟨0, ⟨Additive.ofMul 1, by simp⟩⟩⟧ :
      DirectLimit (degreeFiber (0 : Additive ℕ →+ A) (Additive.ofMul 0))
        (transition (0 : Additive ℕ →+ A) (Additive.ofMul 0))) =
      ⟦⟨1, ⟨Additive.ofMul 0, by simp⟩⟩⟧ := by
  apply Quotient.sound
  refine ⟨1, by change 0 ≤ 1; decide, by change 1 ≤ 1; decide, ?_⟩
  apply Subtype.ext
  rfl

/-- The public injectivity theorem likewise needs no target cancellation. -/
private theorem normalization_injective_without_target_cancellation
    {M : Type v} [AddCommMonoid M] {A : Type w} [AddCommMonoid A]
    (d : M →+ A) (u : M) (hu : (AddSubmonoid.multiples u).saturation = ⊤) :
    Function.Injective (normalization d u) :=
  normalization_injective d u hu

#check @normalizationEquiv
#check @mk_eq_iff
#check @mk_same_stage_eq_iff
#check @normalizationEquiv_symm_eq_mk
#print axioms degreeFiber
#print axioms transition
#print axioms degreeDirectedSystem
#print axioms inducedDegree
#print axioms inducedDegree_of
#print axioms inducedDegree_addMonoidOf
#print axioms induced_degree_rw
#print axioms induced_degree_simp
#print axioms induced_degree_native_simp
#print axioms normalization_representative_simp
#print axioms normalization_equiv_representative_simp
#print axioms normalizedAt
#print axioms normalizedAt_transition
#print axioms normalization
#print axioms normalization_mk
#print axioms exists_normalized_representative
#print axioms of_eq_iff_cyclic_stabilizer
#print axioms normalized_eq_iff
#print axioms normalization_injective
#print axioms mk_eq_iff
#print axioms mk_same_stage_eq_iff
#print axioms normalization_surjective
#print axioms normalizationEquiv
#print axioms normalizationEquiv_mk
#print axioms normalizationEquiv_symm_eq_mk
#print axioms nativeKernelEquiv
#print axioms nativeKernelEquiv_symm_apply
#print axioms nativeKernelEquiv_apply_symm
#print axioms punitKernelEquiv
#print axioms normalization_injective_without_target_cancellation
#print axioms nat_one_cofinal
#print axioms zero_degree_distinguishes
#print axioms zeroDegreeEquiv
#print axioms absorbing_cofinal
#print axioms absorbingZero
#print axioms absorbingOne
#print axioms absorbing_representatives_distinct
#print axioms absorbing_transition_not_injective
#print axioms absorbing_limit_equal
#print axioms absorbingEquiv
#print axioms group_zero_cofinal
#print axioms groupZeroEquiv
#print axioms product_diagonal_cofinal
#print axioms componentwiseEquiv
#print axioms arbitrary_target_cross_stage

end AlgebraicDirectLimits.Tests.GradedStabilization
