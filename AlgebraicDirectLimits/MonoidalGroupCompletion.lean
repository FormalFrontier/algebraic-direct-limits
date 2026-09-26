/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.CategoryTheory.Monoidal.Skeleton
public import Mathlib.Algebra.Group.TypeTags.Hom
public import Mathlib.Algebra.Group.Subgroup.Ker
public import AlgebraicDirectLimits.CofinalGroupCompletion

/-!
# Monoidal functors and group completion of object classes

The additive skeleton of a braided monoidal category is an additive commutative
monoid. A strong monoidal functor induces a map on skeletons, and hence a map
on their Grothendieck groups. Object cofinality says that every target object
has a tensor complement making it isomorphic to an object in the functor's
image. It identifies the saturation of the *actual image submonoid* and gives
object denominators and a stabilization criterion. When the functor is fully
faithful, its induced completion map is injective, with no cancellation or
essential-surjectivity assumption. The range equivalence targets the actual
subgroup range, not the whole completion of the target.
-/

public section
noncomputable section

open CategoryTheory.MonoidalCategory Algebra
open Algebra.GrothendieckAddGroup

namespace CategoryTheory.MonoidalGroupCompletion

universe u₁ u₂ u₃ v₁ v₂ v₃

variable {C : Type u₁} [Category.{v₁} C]

/-- An object as an element of the native additive skeleton. -/
def objectClass (X : C) : Additive (Skeleton C) := Additive.ofMul (toSkeleton X)

theorem objectClass_surjective : Function.Surjective (objectClass (C := C)) := by
  intro x
  refine ⟨(fromSkeleton C).obj (Additive.toMul x), ?_⟩
  exact congrArg Additive.ofMul (toSkeleton_fromSkeleton_obj (Additive.toMul x))

theorem objectClass_eq_iff (X Y : C) :
    objectClass X = objectClass Y ↔ Nonempty (X ≅ Y) :=
  toSkeleton_eq_toSkeleton_iff

variable [MonoidalCategory C]

theorem objectClass_tensor (X Y : C) :
    objectClass (X ⊗ Y) = objectClass X + objectClass Y :=
  congrArg Additive.ofMul (Skeleton.toSkeleton_tensorObj X Y)

theorem objectClass_unit : objectClass (𝟙_ C) = 0 :=
  congrArg Additive.ofMul (Skeleton.one_eq (C := C)).symm

variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
variable (F : C ⥤ D) [F.Monoidal]

/-- The native skeleton monoid hom, transported to additive notation. -/
def skeletonMap : Additive (Skeleton C) →+ Additive (Skeleton D) :=
  (Skeleton.monoidHom F).toAdditive

theorem skeletonMap_objectClass (X : C) :
    skeletonMap F (objectClass X) = objectClass (F.obj X) :=
  congrArg Additive.ofMul (F.mapSkeleton_obj_toSkeleton X)

/-- The actual image of the skeleton map, before group completion. -/
def imageSubmonoid : AddSubmonoid (Additive (Skeleton D)) :=
  (⊤ : AddSubmonoid (Additive (Skeleton C))).map (skeletonMap F)

theorem mem_imageSubmonoid_iff (m : Additive (Skeleton D)) :
    m ∈ imageSubmonoid F ↔ ∃ X : C, objectClass (F.obj X) = m := by
  constructor
  · rintro ⟨n, _, hn⟩
    obtain ⟨X, rfl⟩ := objectClass_surjective n
    exact ⟨X, (skeletonMap_objectClass F X).symm.trans hn⟩
  · rintro ⟨X, rfl⟩
    exact ⟨objectClass X, trivial, skeletonMap_objectClass F X⟩

variable [BraidedCategory D]

/-- Top saturation of the actual image is equivalent to object cofinality,
with the complement taken in the ambient target category. -/
theorem saturation_eq_top_iff :
    (imageSubmonoid F).saturation = ⊤ ↔
      ∀ Y : D, ∃ Z : D, ∃ X : C, Nonempty (Y ⊗ Z ≅ F.obj X) := by
  constructor
  · intro h Y
    have hy : objectClass Y ∈ (imageSubmonoid F).saturation := by rw [h]; trivial
    obtain ⟨c, hc⟩ := AddSubmonoid.mem_saturation_iff.mp hy
    obtain ⟨Z, rfl⟩ := objectClass_surjective c
    obtain ⟨X, hX⟩ := (mem_imageSubmonoid_iff F _).mp hc
    refine ⟨Z, X, (objectClass_eq_iff _ _).mp ?_⟩
    rw [objectClass_tensor]
    exact hX.symm
  · intro h
    apply top_unique
    intro m _
    obtain ⟨Y, rfl⟩ := objectClass_surjective m
    obtain ⟨Z, X, hX⟩ := h Y
    apply AddSubmonoid.mem_saturation_iff.mpr
    refine ⟨objectClass Z, (mem_imageSubmonoid_iff F _).mpr ⟨X, ?_⟩⟩
    rw [← objectClass_tensor]
    exact ((objectClass_eq_iff _ _).mpr hX).symm

/-- Cofinality gives a denominator represented by an actual source object. -/
theorem exists_object_denominator
    (h : ∀ Y : D, ∃ Z : D, ∃ X : C, Nonempty (Y ⊗ Z ≅ F.obj X))
    (z : GrothendieckAddGroup (Additive (Skeleton D))) :
    ∃ Y : D, ∃ X : C, z = of (objectClass Y) - of (objectClass (F.obj X)) := by
  obtain ⟨m, l, hl⟩ := exists_cofinal_denominator (imageSubmonoid F)
    ((saturation_eq_top_iff F).mpr h) z
  obtain ⟨Y, rfl⟩ := objectClass_surjective m
  obtain ⟨X, hX⟩ := (mem_imageSubmonoid_iff F _).mp l.property
  exact ⟨Y, X, hX.symm ▸ hl⟩

/-- Equality after completion is witnessed by tensoring with one image object. -/
theorem object_eq_iff_stabilizer
    (h : ∀ Y : D, ∃ Z : D, ∃ X : C, Nonempty (Y ⊗ Z ≅ F.obj X)) (Y Y' : D) :
    of (objectClass Y) = of (objectClass Y') ↔
      ∃ X : C, Nonempty (Y ⊗ F.obj X ≅ Y' ⊗ F.obj X) := by
  rw [of_eq_iff_exists_cofinal_stabilizer (imageSubmonoid F)
    ((saturation_eq_top_iff F).mpr h)]
  constructor
  · rintro ⟨l, hl⟩
    obtain ⟨X, hX⟩ := (mem_imageSubmonoid_iff F _).mp l.property
    refine ⟨X, (objectClass_eq_iff _ _).mp ?_⟩
    simpa only [objectClass_tensor, hX] using hl
  · rintro ⟨X, hX⟩
    refine ⟨⟨objectClass (F.obj X), (mem_imageSubmonoid_iff F _).mpr ⟨X, rfl⟩⟩, ?_⟩
    simpa only [objectClass_tensor] using (objectClass_eq_iff _ _).mpr hX

private theorem lift_on_generator {A G : Type*} [AddCommMonoid A] [AddCommGroup G]
    (f : A →+ G) (a : A) : lift f (of a) = f a :=
  DFunLike.congr_fun ((lift (M := A) (G := G)).symm_apply_apply f) a

private theorem completion_hom_ext {A G : Type*} [AddCommMonoid A] [AddCommGroup G]
    {p q : GrothendieckAddGroup A →+ G}
    (h : ∀ a : A, p (of a) = q (of a)) : p = q :=
  (lift (M := A) (G := G)).symm.injective (AddMonoidHom.ext h)

variable [BraidedCategory C]

/-- The literal native Grothendieck lift of the given functor's skeleton map. -/
def completionMap : GrothendieckAddGroup (Additive (Skeleton C)) →+
    GrothendieckAddGroup (Additive (Skeleton D)) :=
  lift (of.comp (skeletonMap F))

theorem completionMap_objectClass (X : C) :
    completionMap F (of (objectClass X)) = of (objectClass (F.obj X)) := by
  rw [completionMap, lift_on_generator, AddMonoidHom.comp_apply, skeletonMap_objectClass]

theorem completionMap_id : completionMap (𝟭 C) = AddMonoidHom.id _ := by
  apply completion_hom_ext
  intro n
  obtain ⟨X, rfl⟩ := objectClass_surjective n
  exact completionMap_objectClass (𝟭 C) X

theorem completionMap_comp {E : Type u₃} [Category.{v₃} E] [MonoidalCategory E]
    [BraidedCategory E] (G : D ⥤ E) [G.Monoidal] :
    completionMap (F ⋙ G) = (completionMap G).comp (completionMap F) := by
  apply completion_hom_ext
  intro n
  obtain ⟨X, rfl⟩ := objectClass_surjective n
  simp only [AddMonoidHom.comp_apply, completionMap_objectClass, Functor.comp_obj]

/-- An ordinary natural isomorphism of strong monoidal functors induces the
same group-completion homomorphism; monoidal naturality is not required. -/
theorem completionMap_iso {F' : C ⥤ D} [F'.Monoidal] (e : F ≅ F') :
    completionMap F = completionMap F' := by
  apply completion_hom_ext
  intro n
  obtain ⟨X, rfl⟩ := objectClass_surjective n
  rw [completionMap_objectClass, completionMap_objectClass]
  exact congrArg of ((objectClass_eq_iff _ _).mpr ⟨e.app X⟩)

variable [F.Full] [F.Faithful]

omit [BraidedCategory C] [BraidedCategory D] in
theorem skeletonMap_injective : Function.Injective (skeletonMap F) :=
  F.mapSkeleton_injective

omit [BraidedCategory C] [BraidedCategory D] in
/-- Full faithfulness identifies the source skeleton with the actual image. -/
def imageEquiv : Additive (Skeleton C) ≃+ imageSubmonoid F := by
  let g : Additive (Skeleton C) →+ imageSubmonoid F :=
    (skeletonMap F).codRestrict _ (fun n => ⟨n, trivial, rfl⟩)
  apply AddEquiv.ofBijective g
  constructor
  · intro a b hab
    exact skeletonMap_injective F (congrArg Subtype.val hab)
  · rintro ⟨m, n, _, hn⟩
    exact ⟨n, Subtype.ext hn⟩

omit [BraidedCategory C] [BraidedCategory D] in
theorem coe_imageEquiv (n : Additive (Skeleton C)) :
    (imageEquiv F n : Additive (Skeleton D)) = skeletonMap F n := by
  change skeletonMap F n = skeletonMap F n
  rfl

theorem lift_imageEquiv_injective :
    Function.Injective (lift (of.comp (imageEquiv F).toAddMonoidHom)) := by
  let p := lift (of.comp (imageEquiv F).toAddMonoidHom)
  let q := lift (of.comp (imageEquiv F).symm.toAddMonoidHom)
  have hqp : q.comp p = AddMonoidHom.id _ := by
    apply completion_hom_ext
    intro n
    change q (p (of n)) = of n
    simp only [p, q, lift_on_generator, AddMonoidHom.comp_apply,
      AddEquiv.coe_toAddMonoidHom, AddEquiv.symm_apply_apply]
  have hleft : Function.LeftInverse q p := fun n => DFunLike.congr_fun hqp n
  exact hleft.injective

/-- Exact factorization of the given completion hom through its actual image. -/
theorem completionMap_factorization :
    (lift (of.comp (imageSubmonoid F).subtype)).comp
      (lift (of.comp (imageEquiv F).toAddMonoidHom)) = completionMap F := by
  apply completion_hom_ext
  intro n
  change lift (of.comp (imageSubmonoid F).subtype)
    (lift (of.comp (imageEquiv F).toAddMonoidHom) (of n)) = completionMap F (of n)
  simp only [completionMap, lift_on_generator, AddMonoidHom.comp_apply,
    AddEquiv.coe_toAddMonoidHom, AddSubmonoid.subtype_apply, coe_imageEquiv]

/-- Full faithfulness and object cofinality inject the completion of the source
into that of the target, without cancellation or essential surjectivity. -/
theorem completionMap_injective
    (h : ∀ Y : D, ∃ Z : D, ∃ X : C, Nonempty (Y ⊗ Z ≅ F.obj X)) :
    Function.Injective (completionMap F) := by
  rw [← completionMap_factorization F]
  exact (lift_subtype_injective (imageSubmonoid F)
    ((saturation_eq_top_iff F).mpr h)).comp (lift_imageEquiv_injective F)

/-- Additive equivalence with the native subgroup range of the induced map. -/
def completionRangeEquiv
    (h : ∀ Y : D, ∃ Z : D, ∃ X : C, Nonempty (Y ⊗ Z ≅ F.obj X)) :
    GrothendieckAddGroup (Additive (Skeleton C)) ≃+ (completionMap F).range :=
  AddMonoidHom.ofInjective (completionMap_injective F h)

end CategoryTheory.MonoidalGroupCompletion
