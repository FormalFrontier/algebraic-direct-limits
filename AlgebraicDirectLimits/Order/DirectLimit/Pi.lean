/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicDirectLimits.CategoryTheory.Types.DirectLimit
import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Products
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Limits.Types.Products

/-!
# Finite dependent products of directed limits

The canonical map sends the class of a tuple at one stage to the tuple of its coordinate
classes. It is defined for an arbitrary coordinate type and any directed index. For finite
coordinates and a nonempty directed index, it is bijective and defines an equivalence with
that same forward map. Its inverse synchronizes heterogeneous coordinate representatives.

The nonempty-index hypothesis is essential for the empty product: an empty directed limit
is empty, while the product over an empty coordinate type is a singleton. No coordinate
carrier is required to be inhabited, and transition maps need not be injective.

Product transitions are bundled as `TypeCat.Fun`s, including when a stage product is empty.
The coordinate direct limits retain the original selected transition data.

## References

The finite-product preservation theorem is Mathlib's
`CategoryTheory.Limits.filtered_colim_preservesFiniteLimits_of_types`, applied through
`CategoryTheory.Limits.PreservesProduct.iso`. The same-stage identifications are
`CategoryTheory.Limits.piObjIso` and `CategoryTheory.Limits.Types.productIso`.
The raw quotient is related to these categorical colimits by `DirectLimit.uliftCocone`.
-/

@[expose] public section

universe uι uκ uG uT

open CategoryTheory CategoryTheory.Limits

namespace DirectedSystem

variable {ι : Type uι} [Preorder ι] {κ : Type uκ}
variable {G : ι → κ → Type uG} {T : ∀ ⦃i j : ι⦄, i ≤ j → κ → Sort uT}
variable (f : ∀ i j (h : i ≤ j) a, T h a)
variable [∀ ⦃i j⦄ (h : i ≤ j) a, FunLike (T h a) (G i a) (G j a)]

/-- The coordinatewise transition on dependent products, bundled as a `TypeCat.Fun`. -/
def piTransition (i j : ι) (h : i ≤ j) :
    TypeCat.Fun (∀ a, G i a) (∀ a, G j a) :=
  TypeCat.Fun.mk fun x a ↦ f i j h a (x a)

/-- A product transition acts by the original selected map at each coordinate. -/
@[simp]
theorem piTransition_apply (i j : ι) (h : i ≤ j) (x : ∀ a, G i a) (a : κ) :
    piTransition f i j h x a = f i j h a (x a) := rfl

variable [∀ a, DirectedSystem (fun i ↦ G i a) (fun i j h ↦ f i j h a)]

/-- Coordinatewise transition maps give a directed system of dependent products. -/
instance pi :
    DirectedSystem (fun i ↦ ∀ a, G i a) (piTransition f · · ·) where
  map_self := by
    intro i x
    funext a
    exact DirectedSystem.map_self' (fun i j h ↦ f i j h a) (x a)
  map_map := by
    intro k j i hij hjk x
    funext a
    exact DirectedSystem.map_map' (fun i j h ↦ f i j h a) hij hjk (x a)

end DirectedSystem

namespace DirectLimit

variable {ι : Type uι} [Preorder ι] [IsDirectedOrder ι] {κ : Type uκ}
variable {G : ι → κ → Type uG} {T : ∀ ⦃i j : ι⦄, i ≤ j → κ → Sort uT}
variable (f : ∀ i j (h : i ≤ j) a, T h a)
variable [∀ ⦃i j⦄ (h : i ≤ j) a, FunLike (T h a) (G i a) (G j a)]
variable [∀ a, DirectedSystem (fun i ↦ G i a) (fun i j h ↦ f i j h a)]

/-- The canonical map from the direct limit of stage products to the product of the
coordinate direct limits. It sends each coefficient to its coordinate quotient classes. -/
def piMap :
    DirectLimit (fun i ↦ ∀ a, G i a) (DirectedSystem.piTransition f) →
      ∀ a, DirectLimit (fun i ↦ G i a) (fun i j h ↦ f i j h a) :=
  DirectLimit.lift (DirectedSystem.piTransition f)
    (fun i x a ↦ (⟦⟨i, x a⟩⟧ : DirectLimit (fun i ↦ G i a) (fun i j h ↦ f i j h a)))
    (by
      intro i j h x
      funext a
      exact DirectLimit.eq_of_le (F := fun i ↦ G i a)
        (f := fun i j h ↦ f i j h a) ⟨i, x a⟩ j h)

/-- The canonical comparison takes a common-stage tuple to its coordinate classes. -/
@[simp]
theorem piMap_mk (i : ι) (x : ∀ a, G i a) (a : κ) :
    piMap f ⟦⟨i, x⟩⟧ a = (⟦⟨i, x a⟩⟧ : DirectLimit (fun i ↦ G i a)
      (fun i j h ↦ f i j h a)) := rfl

/-- Lifting a stage product is naturally isomorphic to the categorical product of
its lifted coordinate functors. -/
private noncomputable def piTypesFunctorIso :
    (DirectedSystem.typesFunctor (DirectedSystem.piTransition f) ⋙
      uliftFunctor.{max uι uκ uG, max uκ uG}) ≅
        ∏ᶜ (fun a ↦ DirectedSystem.typesFunctor (fun i j h ↦ f i j h a) ⋙
          uliftFunctor.{max uι uκ uG, uG}) := by
  let L : κ → ι ⥤ Type (max uι uκ uG) := fun a ↦
    DirectedSystem.typesFunctor (fun i j h ↦ f i j h a) ⋙
      uliftFunctor.{max uι uκ uG, uG}
  let P : ι ⥤ Type (max uι uκ uG) :=
    DirectedSystem.typesFunctor (DirectedSystem.piTransition f) ⋙
      uliftFunctor.{max uι uκ uG, max uκ uG}
  let e (i : ι) : P.obj i ≅ (∀ a, (L a).obj i) :=
    { hom := TypeCat.ofHom fun x a ↦ ULift.up (x.down a)
      inv := TypeCat.ofHom fun x ↦ ULift.up (fun a ↦ (x a).down) }
  let E (i : ι) : P.obj i ≅ (∏ᶜ L).obj i :=
    e i ≪≫ (Types.productIso (fun a ↦ (L a).obj i)).symm ≪≫ (piObjIso L i).symm
  have hπ (i : ι) (a : κ) :
      (E i).hom ≫ (Pi.π L a).app i =
        TypeCat.ofHom (X := P.obj i) (Y := (L a).obj i)
          (fun x ↦ ULift.up (x.down a)) := by
    simp only [E, Iso.trans_hom, Iso.symm_hom, Category.assoc,
      piObjIso_inv_comp_π, Types.productIso_inv_comp_π]
    ext x
    rfl
  refine NatIso.ofComponents (F := P) (G := ∏ᶜ L) E ?_
  intro i j h
  apply (cancel_mono (piObjIso L j).hom).1
  apply Pi.hom_ext
  intro a
  simp only [Category.assoc, piObjIso_hom_comp_π]
  rw [(Pi.π L a).naturality h, hπ, ← Category.assoc, hπ]
  rfl

omit [IsDirectedOrder ι] in
/-- The stage isomorphism respects every coordinate projection. -/
@[reassoc]
private theorem piTypesFunctorIso_hom_π (i : ι) (a : κ) :
    (piTypesFunctorIso f).hom.app i ≫
      (Pi.π (fun a ↦ DirectedSystem.typesFunctor (fun i j h ↦ f i j h a) ⋙
        uliftFunctor.{max uι uκ uG, uG}) a).app i =
      TypeCat.ofHom
        (X := (DirectedSystem.typesFunctor (DirectedSystem.piTransition f) ⋙
          uliftFunctor.{max uι uκ uG, max uκ uG}).obj i)
        (Y := (DirectedSystem.typesFunctor (fun i j h ↦ f i j h a) ⋙
          uliftFunctor.{max uι uκ uG, uG}).obj i)
        (fun x ↦ ULift.up (x.down a)) := by
  dsimp only [piTypesFunctorIso, NatIso.ofComponents]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc,
    piObjIso_inv_comp_π, Types.productIso_inv_comp_π]
  ext x
  rfl

/-- Over a nonempty directed index, the canonical comparison for a finite dependent
product is bijective. This is the raw-direct-limit form of finite-product preservation
by filtered colimits of types. -/
theorem piMap_bijective [Finite κ] [Nonempty ι] : Function.Bijective (piMap f) := by
  let L : κ → ι ⥤ Type (max uι uκ uG) := fun a ↦
    DirectedSystem.typesFunctor (fun i j h ↦ f i j h a) ⋙
      uliftFunctor.{max uι uκ uG, uG}
  let P : ι ⥤ Type (max uι uκ uG) :=
    DirectedSystem.typesFunctor (DirectedSystem.piTransition f) ⋙
      uliftFunctor.{max uι uκ uG, max uκ uG}
  let cP : ColimitCocone P :=
    ⟨uliftCocone.{uι, max uκ uG, _, uκ} (DirectedSystem.piTransition f),
      uliftCoconeIsColimit.{uι, max uκ uG, _, uκ} (DirectedSystem.piTransition f)⟩
  let c (a : κ) : ColimitCocone (L a) :=
    ⟨uliftCocone.{uι, uG, uT, uκ} (fun i j h ↦ f i j h a),
      uliftCoconeIsColimit.{uι, uG, uT, uκ} (fun i j h ↦ f i j h a)⟩
  have : PreservesFiniteLimits (colim : (ι ⥤ Type (max uι uκ uG)) ⥤ _) :=
    filtered_colim_preservesFiniteLimits_of_types
  let e : cP.cocone.pt ≅ (∀ a, (c a).cocone.pt) :=
    (colimit.isoColimitCocone cP).symm ≪≫
      HasColimit.isoOfNatIso (piTypesFunctorIso f) ≪≫
      PreservesProduct.iso colim L ≪≫
      Pi.mapIso (fun a ↦ colimit.isoColimitCocone (c a)) ≪≫
      Types.productIso _
  have h (i : ι) (a : κ) :
      cP.cocone.ι.app i ≫ e.hom ≫
          TypeCat.ofHom (fun y : ∀ a, (c a).cocone.pt ↦ y a) =
        TypeCat.ofHom (X := P.obj i) (Y := (L a).obj i)
          (fun x ↦ ULift.up (x.down a)) ≫ (c a).cocone.ι.app i := by
    simp only [e, Iso.trans_hom, Iso.symm_hom, Category.assoc,
      Types.productIso_hom_comp_eval, Pi.mapIso_hom_π,
      PreservesProduct.iso_hom, piComparison_comp_π_assoc,
      colimit.isoColimitCocone_ι_inv_assoc, HasColimit.ι_isoOfNatIso_hom_assoc,
      colimit.ι_map_assoc, colimit.isoColimitCocone_ι_hom]
    simpa only [Category.assoc] using
      congrArg (fun q : P.obj i ⟶ (L a).obj i ↦ q ≫ (c a).cocone.ι.app i)
        (piTypesFunctorIso_hom_π f i a)
  have he (i : ι) (x : ∀ a, G i a) (a : κ) :
      e.hom (ULift.up (⟦⟨i, x⟩⟧ :
        DirectLimit (fun i ↦ ∀ a, G i a) (DirectedSystem.piTransition f)) :
          cP.cocone.pt) a =
        (ULift.up (⟦⟨i, x a⟩⟧ :
          DirectLimit (fun i ↦ G i a) (fun i j h ↦ f i j h a)) :
            (c a).cocone.pt) := by
    let ev : (∀ b, (c b).cocone.pt) ⟶ (c a).cocone.pt :=
      TypeCat.ofHom (fun y ↦ y a)
    let pr : P.obj i ⟶ (L a).obj i :=
      TypeCat.ofHom (fun y ↦ ULift.up (y.down a))
    -- Fix the concrete category and endpoints before evaluating the composites.
    have h' :
        TypeCat.Hom.hom (cP.cocone.ι.app i ≫ e.hom ≫ ev) (ULift.up x : P.obj i) =
          TypeCat.Hom.hom (pr ≫ (c a).cocone.ι.app i) (ULift.up x : P.obj i) :=
      ConcreteCategory.congr_hom (C := Type (max uι uκ uG))
        (FC := TypeCat.Fun) (CC := fun X ↦ X)
        (X := P.obj i) (Y := (c a).cocone.pt) (h i a) (ULift.up x : P.obj i)
    have h'' :
        TypeCat.Hom.hom ev (TypeCat.Hom.hom e.hom
          (TypeCat.Hom.hom (cP.cocone.ι.app i) (ULift.up x : P.obj i))) =
          TypeCat.Hom.hom ((c a).cocone.ι.app i)
            (TypeCat.Hom.hom pr (ULift.up x : P.obj i)) := by
      calc
        _ = TypeCat.Hom.hom (e.hom ≫ ev)
            (TypeCat.Hom.hom (cP.cocone.ι.app i) (ULift.up x : P.obj i)) :=
          (ConcreteCategory.comp_apply (C := Type (max uι uκ uG))
            (FC := TypeCat.Fun) (CC := fun X ↦ X)
            (X := cP.cocone.pt) (Y := ∀ b, (c b).cocone.pt)
            (Z := (c a).cocone.pt) e.hom ev
            (TypeCat.Hom.hom (cP.cocone.ι.app i) (ULift.up x : P.obj i))).symm
        _ = TypeCat.Hom.hom (cP.cocone.ι.app i ≫ e.hom ≫ ev)
            (ULift.up x : P.obj i) :=
          (ConcreteCategory.comp_apply (C := Type (max uι uκ uG))
            (FC := TypeCat.Fun) (CC := fun X ↦ X)
            (X := P.obj i) (Y := cP.cocone.pt) (Z := (c a).cocone.pt)
            (cP.cocone.ι.app i) (e.hom ≫ ev) (ULift.up x : P.obj i)).symm
        _ = TypeCat.Hom.hom (pr ≫ (c a).cocone.ι.app i)
            (ULift.up x : P.obj i) := h'
        _ = _ :=
          ConcreteCategory.comp_apply (C := Type (max uι uκ uG))
            (FC := TypeCat.Fun) (CC := fun X ↦ X)
            (X := P.obj i) (Y := (L a).obj i) (Z := (c a).cocone.pt)
            pr ((c a).cocone.ι.app i) (ULift.up x : P.obj i)
    have hP :
        TypeCat.Hom.hom (cP.cocone.ι.app i) (ULift.up x : P.obj i) =
          (ULift.up (⟦⟨i, x⟩⟧ :
            DirectLimit (fun j ↦ ∀ b, G j b) (DirectedSystem.piTransition f)) :
              cP.cocone.pt) :=
      uliftCocone_ι_app.{uι, max uκ uG, _, uκ}
        (G := fun j ↦ ∀ b, G j b)
        (T := fun ⦃j k⦄ _ ↦ TypeCat.Fun (∀ b, G j b) (∀ b, G k b))
        (DirectedSystem.piTransition f) i (ULift.up x)
    have hpr : TypeCat.Hom.hom pr (ULift.up x : P.obj i) =
        (ULift.up (x a) : (L a).obj i) := rfl
    have hC :
        TypeCat.Hom.hom ((c a).cocone.ι.app i) (ULift.up (x a) : (L a).obj i) =
          (ULift.up (⟦⟨i, x a⟩⟧ :
            DirectLimit (fun j ↦ G j a) (fun j k h ↦ f j k h a)) :
              (c a).cocone.pt) :=
      uliftCocone_ι_app.{uι, uG, uT, uκ}
        (G := fun j ↦ G j a) (T := fun ⦃j k⦄ h ↦ T h a)
        (fun j k h ↦ f j k h a) i (ULift.up (x a))
    rw [hP, hpr, hC] at h''
    exact h''
  let E : DirectLimit (fun i ↦ ∀ a, G i a) (DirectedSystem.piTransition f) ≃
      ∀ a, DirectLimit (fun i ↦ G i a) (fun i j h ↦ f i j h a) :=
    ((Equiv.ulift : cP.cocone.pt ≃
      DirectLimit (fun i ↦ ∀ a, G i a) (DirectedSystem.piTransition f)).symm.trans
        e.toEquiv).trans
      (Equiv.piCongrRight fun a ↦ (Equiv.ulift : (c a).cocone.pt ≃
        DirectLimit (fun i ↦ G i a) (fun i j h ↦ f i j h a)))
  have hE : (E : _ → _) = piMap f := by
    funext z
    obtain ⟨i, x, rfl⟩ := DirectLimit.exists_eq_mk (DirectedSystem.piTransition f) z
    funext a
    exact congrArg ULift.down (he i x a)
  rw [← hE]
  exact E.bijective

variable [Finite κ] [Nonempty ι]

/-- The equivalence between the direct limit of finite stage products and the product
of the coordinate direct limits, with forward function `DirectLimit.piMap`. -/
noncomputable def piEquiv :
    DirectLimit (fun i ↦ ∀ a, G i a) (DirectedSystem.piTransition f) ≃
      ∀ a, DirectLimit (fun i ↦ G i a) (fun i j h ↦ f i j h a) :=
  Equiv.ofBijective (piMap f) (piMap_bijective f)

/-- The forward function of the equivalence is the canonical comparison. -/
theorem piEquiv_apply
    (z : DirectLimit (fun i ↦ ∀ a, G i a) (DirectedSystem.piTransition f)) :
    piEquiv f z = piMap f z := rfl

/-- The equivalence takes a common-stage tuple to its coordinate classes. -/
@[simp]
theorem piEquiv_mk (i : ι) (x : ∀ a, G i a) (a : κ) :
    piEquiv f ⟦⟨i, x⟩⟧ a = (⟦⟨i, x a⟩⟧ : DirectLimit (fun i ↦ G i a)
      (fun i j h ↦ f i j h a)) := rfl

/-- The inverse equivalence assembles coordinate classes represented at one stage. -/
@[simp]
theorem piEquiv_symm_mk (i : ι) (x : ∀ a, G i a) :
    (piEquiv f).symm (fun a ↦ (⟦⟨i, x a⟩⟧ :
      DirectLimit (fun i ↦ G i a) (fun i j h ↦ f i j h a))) = ⟦⟨i, x⟩⟧ :=
  (piEquiv f).symm_apply_apply ⟦⟨i, x⟩⟧

/-- Given coordinate representatives and a common upper stage, the inverse comparison
uses precisely the selected transition maps to transport them to that stage. -/
theorem piEquiv_symm_mk_of_le (i : κ → ι) (x : ∀ a, G (i a) a)
    (k : ι) (h : ∀ a, i a ≤ k) :
    (piEquiv f).symm (fun a ↦ (⟦⟨i a, x a⟩⟧ :
      DirectLimit (fun i ↦ G i a) (fun i j h ↦ f i j h a))) =
        ⟦⟨k, fun a ↦ f (i a) k (h a) a (x a)⟩⟧ := by
  apply (piEquiv f).injective
  funext a
  rw [Equiv.apply_symm_apply, piEquiv_mk]
  exact DirectLimit.eq_of_le (F := fun i ↦ G i a)
    (f := fun i j h ↦ f i j h a) ⟨i a, x a⟩ k (h a)

/-- A finite heterogeneous family of classes has representatives at a common stage.
The stage carrier may vary with the coordinate. -/
theorem exists_eq_mk_pi
    (y : ∀ a, DirectLimit (fun i ↦ G i a) (fun i j h ↦ f i j h a)) :
    ∃ (i : ι) (x : ∀ a, G i a), ∀ a, y a = ⟦⟨i, x a⟩⟧ := by
  obtain ⟨i, x, hx⟩ := DirectLimit.exists_eq_mk
    (DirectedSystem.piTransition f) ((piEquiv f).symm y)
  refine ⟨i, x, fun a ↦ ?_⟩
  simpa only [Equiv.apply_symm_apply, piEquiv_mk] using
    congrArg (fun z ↦ piEquiv f z a) hx

end DirectLimit
