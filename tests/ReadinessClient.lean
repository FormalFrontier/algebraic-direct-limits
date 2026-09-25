/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicDirectLimits

/-!
# Aggregate-import client

These private checks use the older five mathematical modules through the public
aggregate only, without assuming injective transitions or countable index types.
-/

public section

namespace AlgebraicDirectLimits.Tests.Readiness

universe uIndex uScalar uLeft uRight uInverse uCategory uRing

open DirectLimit

section VaryingScalar

open DirectLimit.VaryingScalar

variable {ι : Type uIndex} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
variable (A : ι → Type uScalar) [∀ i, CommSemiring (A i)]
variable (f : ∀ i j, i ≤ j → A i →+* A j) [DirectedSystem A (f · · ·)]
variable (M : ι → Type uLeft) [∀ i, AddCommMonoid (M i)] [∀ i, Module (A i) (M i)]
variable (g : ∀ i j (hij : i ≤ j), M i →ₛₗ[f i j hij] M j)
variable [DirectedSystem M (g · · ·)]
variable (N : ι → Type uRight) [∀ i, AddCommMonoid (N i)] [∀ i, Module (A i) (N i)]
variable (h : ∀ i j (hij : i ≤ j), N i →ₛₗ[f i j hij] N j)
variable [DirectedSystem N (h · · ·)]

private theorem scalar_action_on_representatives (i : ι) (a : A i) (m : M i) :
    (⟦⟨i, a⟩⟧ : ScalarLimit A f) •
        (⟦⟨i, m⟩⟧ : DirectLimit M (fun i j hij ↦ g i j hij)) =
      (⟦⟨i, a • m⟩⟧ : DirectLimit M (fun i j hij ↦ g i j hij)) :=
  smul_mk A f M g i a m

private theorem module_transition_on_representatives {i j : ι} (hij : i ≤ j) (m : M i) :
    of A f M g j (g i j hij m) = of A f M g i m :=
  of_map A f M g hij m

private theorem tensor_equiv_on_representatives (i : ι) (m : M i) (n : N i) :
    tensorProductEquiv A f M g N h
        (of A f M g i m ⊗ₜ[ScalarLimit A f] of A f N h i n) =
      tensorOf A f M g N h i (m ⊗ₜ[A i] n) :=
  tensorProductEquiv_tmul_mk A f M g N h i m n

private theorem tensor_map_stage_rw (i : ι) (m : M i) (n : N i) :
    toTensorLimit A f M g N h
        (of A f M g i m ⊗ₜ[ScalarLimit A f] of A f N h i n) =
      tensorOf A f M g N h i (m ⊗ₜ[A i] n) := by
  rw [toTensorLimit_tmul_mk]

private theorem tensor_map_stage_simp (i : ι) (m : M i) (n : N i) :
    toTensorLimit A f M g N h
        (of A f M g i m ⊗ₜ[ScalarLimit A f] of A f N h i n) =
      tensorOf A f M g N h i (m ⊗ₜ[A i] n) := by
  simp

private theorem tensor_map_quotient_simp (i : ι) (m : M i) (n : N i) :
    toTensorLimit A f M g N h (⟦⟨i, m⟩⟧ ⊗ₜ[ScalarLimit A f] ⟦⟨i, n⟩⟧) =
      ⟦⟨i, m ⊗ₜ[A i] n⟩⟧ := by
  simp

private theorem tensor_equiv_stage_rw (i : ι) (m : M i) (n : N i) :
    tensorProductEquiv A f M g N h
        (of A f M g i m ⊗ₜ[ScalarLimit A f] of A f N h i n) =
      tensorOf A f M g N h i (m ⊗ₜ[A i] n) := by
  rw [tensorProductEquiv_tmul_mk]

private theorem tensor_equiv_stage_simp (i : ι) (m : M i) (n : N i) :
    tensorProductEquiv A f M g N h
        (of A f M g i m ⊗ₜ[ScalarLimit A f] of A f N h i n) =
      tensorOf A f M g N h i (m ⊗ₜ[A i] n) := by
  simp

private theorem tensor_equiv_quotient_simp (i : ι) (m : M i) (n : N i) :
    tensorProductEquiv A f M g N h (⟦⟨i, m⟩⟧ ⊗ₜ[ScalarLimit A f] ⟦⟨i, n⟩⟧) =
      ⟦⟨i, m ⊗ₜ[A i] n⟩⟧ := by
  simp

private theorem tensor_inverse_on_representatives (i : ι)
    (x : TensorProduct (A i) (M i) (N i)) :
    (tensorProductEquiv A f M g N h).symm ⟦⟨i, x⟩⟧ =
      tensorToLimits A f M g N h i x :=
  tensorProductEquiv_symm_mk A f M g N h i x

end VaryingScalar

section CofinalSequence

variable {J : Type uIndex} [Preorder J] [IsDirectedOrder J] [Nonempty J]

private theorem monotone_cofinal_sequence {s : Set J}
    (hs : IsCofinal s) (hsc : s.Countable) :
    ∃ f : ℕ → J, Monotone f ∧ IsCofinal (Set.range f) :=
  hs.exists_monotone_nat hsc

end CofinalSequence

section MittagLefflerRestriction

open CategoryTheory

variable {I : Type uIndex} {J : Type uCategory} [Preorder I] [Preorder J]
variable [IsDirectedOrder I] (F : Jᵒᵖ ⥤ Type uInverse)
variable {f : I → J} (hf : Monotone f)

private theorem cofinal_restriction_without_nonempty
    (hF : F.IsMittagLeffler) (hfc : IsCofinal (Set.range f)) :
    (hf.functor.op ⋙ F).IsMittagLeffler :=
  CategoryTheory.Functor.IsMittagLeffler.comp_monotone_cofinal F hF hf hfc

private theorem cofinal_restriction_old_assumptions [Nonempty I]
    (hF : F.IsMittagLeffler) (hfc : IsCofinal (Set.range f)) :
    (hf.functor.op ⋙ F).IsMittagLeffler := by
  obtain ⟨_⟩ := ‹Nonempty I›
  exact CategoryTheory.Functor.IsMittagLeffler.comp_monotone_cofinal F hF hf hfc

end MittagLefflerRestriction

section MittagLeffler

open CategoryTheory

variable {J : Type uIndex} [Preorder J] [IsDirectedOrder J] [Nonempty J]
variable (F : Jᵒᵖ ⥤ Type uInverse) (hF : F.IsMittagLeffler)
variable {s : Set J} (hs : IsCofinal s) (hsc : s.Countable)

private theorem sections_of_pointwise_nonempty
    (hF : F.IsMittagLeffler) [∀ j, Nonempty (F.obj j)]
    {s : Set J} (hs : IsCofinal s) (hsc : s.Countable) : F.sections.Nonempty :=
  CategoryTheory.Functor.IsMittagLeffler.nonempty_sections_of_countable_cofinal F hF hs hsc

private theorem evaluation_onto_eventual_range
    (hF : F.IsMittagLeffler) {s : Set J} (hs : IsCofinal s) (hsc : s.Countable)
    (i : Jᵒᵖ) :
    Function.Surjective (F.evalSectionToEventualRange i) :=
  CategoryTheory.Functor.IsMittagLeffler.surjective_evalSectionToEventualRange F hF hs hsc i

end MittagLeffler

section SimpleRing

open CategoryTheory CategoryTheory.Limits

variable {J : Type uCategory} [SmallCategory J] [IsFiltered J]
variable (F : J ⥤ RingCat.{max uCategory uRing})

private theorem simple_filtered_colimit (hF : ∀ j, IsSimpleRing (F.obj j)) :
    IsSimpleRing (RingCat.FilteredColimits.colimit F) :=
  RingCat.FilteredColimits.colimit_isSimpleRing F hF

end SimpleRing

section LocalizationPi

variable {R : Type uRing} [CommRing R]

private theorem comparison_on_original_product (r : R) (a : ℕ → R) :
    Localization.awayPiComparison r
        (algebraMap (ℕ → R) (Localization.Away (fun _ : ℕ ↦ r)) a) =
      fun i ↦ algebraMap R (Localization.Away r) (a i) :=
  Localization.awayPiComparison_algebraMap r a

private theorem comparison_not_surjective [IsDomain R] (r : R)
    (hr : r ≠ 0) (hr_unit : ¬ IsUnit r) :
    ¬ Function.Surjective (Localization.awayPiComparison r) :=
  Localization.awayPiComparison_not_surjective r hr hr_unit

end LocalizationPi

#print axioms scalar_action_on_representatives
#print axioms module_transition_on_representatives
#print axioms tensor_equiv_on_representatives
#print axioms tensor_map_stage_rw
#print axioms tensor_map_stage_simp
#print axioms tensor_map_quotient_simp
#print axioms tensor_equiv_stage_rw
#print axioms tensor_equiv_stage_simp
#print axioms tensor_equiv_quotient_simp
#print axioms DirectLimit.VaryingScalar.toTensorLimit_tmul_mk_mk
#print axioms DirectLimit.VaryingScalar.tensorProductEquiv_tmul_mk_mk
#print axioms cofinal_restriction_without_nonempty
#print axioms cofinal_restriction_old_assumptions
#print axioms tensor_inverse_on_representatives
#print axioms monotone_cofinal_sequence
#print axioms sections_of_pointwise_nonempty
#print axioms evaluation_onto_eventual_range
#print axioms simple_filtered_colimit
#print axioms comparison_on_original_product
#print axioms comparison_not_surjective

end AlgebraicDirectLimits.Tests.Readiness
