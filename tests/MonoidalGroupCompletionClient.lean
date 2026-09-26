/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicDirectLimits
public import Mathlib.Algebra.GroupWithZero.WithZero
public import Mathlib.Algebra.Group.PUnit

/-! Standalone clients of the public monoidal group-completion API. -/

public section
noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory Algebra
open Algebra.GrothendieckAddGroup
open CategoryTheory.MonoidalGroupCompletion

namespace MonoidalGroupCompletionClient

universe u₁ u₂ u₃ v₁ v₂ v₃

variable {C : Type u₁} [Category.{v₁} C]

private theorem classes_need_only_category (X Y : C) :
    objectClass X = objectClass Y ↔ Nonempty (X ≅ Y) :=
  objectClass_eq_iff X Y

variable [MonoidalCategory C]

private theorem tensor_needs_no_braiding (X Y : C) :
    objectClass (X ⊗ Y) = objectClass X + objectClass Y :=
  objectClass_tensor X Y

private theorem identity_cofinal (Y : C) :
    ∃ Z : C, ∃ X : C, Nonempty (Y ⊗ Z ≅ (𝟭 C).obj X) :=
  ⟨𝟙_ C, Y, ⟨ρ_ Y⟩⟩

variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
variable (F : C ⥤ D) [F.Monoidal]

private theorem skeleton_on_generator (X : C) :
    skeletonMap F (objectClass X) = objectClass (F.obj X) :=
  skeletonMap_objectClass F X

private theorem image_on_generator (X : C) : objectClass (F.obj X) ∈ imageSubmonoid F :=
  (mem_imageSubmonoid_iff F _).mpr ⟨X, rfl⟩

variable [BraidedCategory D]

private theorem weak_source_denominator
    (h : ∀ Y : D, ∃ Z : D, ∃ X : C, Nonempty (Y ⊗ Z ≅ F.obj X))
    (z : GrothendieckAddGroup (Additive (Skeleton D))) :
    ∃ Y : D, ∃ X : C, z = of (objectClass Y) - of (objectClass (F.obj X)) :=
  exists_object_denominator F h z

private theorem weak_source_stabilizer
    (h : ∀ Y : D, ∃ Z : D, ∃ X : C, Nonempty (Y ⊗ Z ≅ F.obj X)) (Y Y' : D) :
    of (objectClass Y) = of (objectClass Y') ↔
      ∃ X : C, Nonempty (Y ⊗ F.obj X ≅ Y' ⊗ F.obj X) :=
  object_eq_iff_stabilizer F h Y Y'

variable [BraidedCategory C]

private theorem identity_saturation : (imageSubmonoid (𝟭 C)).saturation = ⊤ :=
  (saturation_eq_top_iff (𝟭 C)).mpr identity_cofinal

private theorem identity_injective : Function.Injective (completionMap (𝟭 C)) :=
  completionMap_injective (𝟭 C) identity_cofinal

private theorem identity_is_identity : completionMap (𝟭 C) = AddMonoidHom.id _ :=
  completionMap_id

private theorem identity_denominator (z : GrothendieckAddGroup (Additive (Skeleton C))) :
    ∃ Y X : C, z = of (objectClass Y) - of (objectClass X) :=
  exists_object_denominator (𝟭 C) identity_cofinal z

private theorem identity_stabilizer (Y Y' : C) :
    of (objectClass Y) = of (objectClass Y') ↔
      ∃ X : C, Nonempty (Y ⊗ X ≅ Y' ⊗ X) :=
  object_eq_iff_stabilizer (𝟭 C) identity_cofinal Y Y'

private theorem generator (X : C) :
    completionMap F (of (objectClass X)) = of (objectClass (F.obj X)) :=
  completionMap_objectClass F X

private theorem composition {E : Type u₃} [Category.{v₃} E] [MonoidalCategory E]
    [BraidedCategory E] (G : D ⥤ E) [G.Monoidal] :
    completionMap (F ⋙ G) = (completionMap G).comp (completionMap F) :=
  completionMap_comp F G

private theorem natural_iso {F' : C ⥤ D} [F'.Monoidal] (e : F ≅ F') :
    completionMap F = completionMap F' :=
  completionMap_iso F e

variable [F.Full] [F.Faithful]

omit [BraidedCategory C] [BraidedCategory D] in
private theorem image_coercion (n : Additive (Skeleton C)) :
    (imageEquiv F n : Additive (Skeleton D)) = skeletonMap F n :=
  coe_imageEquiv F n

private theorem hom_factorization :
    (lift (of.comp (imageSubmonoid F).subtype)).comp
      (lift (of.comp (imageEquiv F).toAddMonoidHom)) = completionMap F :=
  completionMap_factorization F

private def range_equivalence
    (h : ∀ Y : D, ∃ Z : D, ∃ X : C, Nonempty (Y ⊗ Z ≅ F.obj X)) :
    GrothendieckAddGroup (Additive (Skeleton C)) ≃+ (completionMap F).range :=
  completionRangeEquiv F h

omit [BraidedCategory D] in
private theorem essentially_surjective_cofinal {A : Type u₃} [Category.{v₃} A]
    (G : A ⥤ D) [G.EssSurj] (Y : D) :
    ∃ Z : D, ∃ X : A, Nonempty (Y ⊗ Z ≅ G.obj X) := by
  obtain ⟨X, ⟨i⟩⟩ := Functor.EssSurj.mem_essImage G Y
  exact ⟨𝟙_ D, X, ⟨(ρ_ Y) ≪≫ i.symm⟩⟩

private theorem equivalence_injective (e : C ≌ D) [e.functor.Monoidal] :
    Function.Injective (completionMap e.functor) :=
  completionMap_injective e.functor (essentially_surjective_cofinal e.functor)

private theorem terminal_identity_injective :
    Function.Injective (completionMap (𝟭 (Discrete PUnit))) :=
  identity_injective

section Noncancellative

local instance noncancellativeMonoidal : MonoidalCategory (Discrete (WithZero PUnit.{1})) :=
  Discrete.monoidal _

private theorem zero_tensor_stabilizes (Y Y' : Discrete (WithZero PUnit.{1})) :
    Nonempty (Y ⊗ Discrete.mk 0 ≅ Y' ⊗ Discrete.mk 0) := by
  exact ⟨Discrete.eqToIso (by change Y.as * 0 = Y'.as * 0; simp)⟩

private theorem noncancellative_class_collapse (Y Y' : Discrete (WithZero PUnit.{1})) :
    of (objectClass Y) = of (objectClass Y') :=
  (identity_stabilizer Y Y').mpr ⟨Discrete.mk 0, zero_tensor_stabilizes Y Y'⟩

private theorem zero_one_object_classes_distinct :
    objectClass (Discrete.mk (0 : WithZero PUnit.{1})) ≠ objectClass (Discrete.mk 1) := by
  intro h
  obtain ⟨i⟩ := (objectClass_eq_iff _ _).mp h
  have hz : (0 : WithZero PUnit.{1}) = 1 := Discrete.eq_of_hom i.hom
  exact zero_ne_one hz

end Noncancellative

/-- The discrete strong monoidal functor corresponding to doubling on `ℕ`. -/
def doublingFunctor : Discrete (Multiplicative ℕ) ⥤ Discrete (Multiplicative ℕ) :=
  Discrete.monoidalFunctor ((AddMonoidHom.id ℕ + AddMonoidHom.id ℕ).toMultiplicative)

instance doublingMonoidal : doublingFunctor.Monoidal :=
  inferInstanceAs (Discrete.monoidalFunctor
    ((AddMonoidHom.id ℕ + AddMonoidHom.id ℕ).toMultiplicative)).Monoidal

instance doublingFaithful : doublingFunctor.Faithful where
  map_injective _ := Subsingleton.elim _ _

instance doublingFull : doublingFunctor.Full where
  map_surjective {X Y} f := by
    have h := Discrete.eq_of_hom f
    change X.as.toAdd + X.as.toAdd = Y.as.toAdd + Y.as.toAdd at h
    have hXY : X.as = Y.as := by change X.as.toAdd = Y.as.toAdd; omega
    exact ⟨Discrete.eqToHom hXY, Subsingleton.elim _ _⟩

private theorem doubling_cofinal (Y : Discrete (Multiplicative ℕ)) :
    ∃ Z : Discrete (Multiplicative ℕ), ∃ X : Discrete (Multiplicative ℕ),
      Nonempty (Y ⊗ Z ≅ doublingFunctor.obj X) :=
  ⟨Y, Y, ⟨Discrete.eqToIso rfl⟩⟩

private theorem doubling_completion_injective : Function.Injective (completionMap doublingFunctor) :=
  completionMap_injective doublingFunctor doubling_cofinal

private theorem doubling_not_essSurj : ¬ doublingFunctor.EssSurj := by
  intro h
  let _ := h
  obtain ⟨X, ⟨i⟩⟩ := Functor.EssSurj.mem_essImage doublingFunctor
    (Discrete.mk (Multiplicative.ofAdd 1))
  have hi := Discrete.eq_of_hom i.hom
  change X.as.toAdd + X.as.toAdd = 1 at hi
  omega

end MonoidalGroupCompletionClient
