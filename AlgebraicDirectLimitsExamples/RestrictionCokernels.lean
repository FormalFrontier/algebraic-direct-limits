/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicDirectLimits.Topology.RestrictionCokernels
public import AlgebraicDirectLimitsExamples.RestrictionKernels
import Mathlib.Tactic.NormNum

/-!
# A nonzero cokernel after restriction from `ZMod 4` to the integers

Doubling on the discrete regular `ZMod 4` module of
`AlgebraicDirectLimitsExamples.RestrictionKernels` has a nonzero algebraic-range
quotient. The class of one is nonzero in both concrete quotient views. The
canonical categorical cokernel comparison retains that class and is an
isomorphism by scalar-restriction preservation.

The parity arrow takes values in the finite direct sum `ℤ ⊕ ZMod 2`, represented
by the binary product. It kills doubling and factors uniquely through the
restricted quotient. Its descendant takes the class of one to `(0, 1)`.
There is no `ZMod 4`-action on this target in the construction; indeed four
does not annihilate `(1, 0)`, whereas it annihilates every restricted object.

## References

The examples reuse the reduction, regular module and doubling morphism of
`AlgebraicDirectLimitsExamples.RestrictionKernels`. They use Mathlib's
`ZMod.castHom` and the algebraic-range topological cokernel of Richard Hill and
Andrew Yang. The restriction functor follows the Continuous Group Cohomology
formalization by Formal Frontier Agents, including Beacon's original development.
The parity map's construction with the stored module structures follows Kim
Morrison's `Algebra.Category.Grp.ZModuleEquivalence` in Mathlib. Its scalar law
uses the integer-action value identities in `Algebra.Module.NatInt`, by
Nathaniel Thomas, Jeremy Avigad, Johannes Hölzl and Mario Carneiro.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace ScalarRestriction.ModFour

/-- The discrete topology on `ZMod 4` in the doubling cokernel construction. -/
local instance instTopologicalSpaceZModFourCokernel : TopologicalSpace (ZMod 4) := topology
local instance : DiscreteTopology (ZMod 4) := discreteTopology_bot _
/-- The discrete topology on the `ZMod 2` factor of the parity arrow's target. -/
local instance instTopologicalSpaceZModTwoParity : TopologicalSpace (ZMod 2) := ⊥
local instance : DiscreteTopology (ZMod 2) := discreteTopology_bot _
local instance : ContinuousAdd (ℤ × ZMod 2) := ⟨continuous_of_discreteTopology⟩
local instance : ContinuousSMul ℤ (ℤ × ZMod 2) := ⟨continuous_of_discreteTopology⟩

private def parityHom : ZMod 4 →+* ZMod 2 :=
  ZMod.castHom (show 2 ∣ 4 by norm_num) (ZMod 2)

private theorem parityHom_double (x : ZMod 4) : parityHom (x + x) = 0 := by
  rw [map_add, ← two_mul]
  have htwo : (2 : ZMod 2) = 0 := ZMod.natCast_self 2
  rw [htwo, zero_mul]

private theorem one_not_mem_doubling_range :
    (1 : regularModule) ∉ doubling.hom.range := by
  rintro ⟨x, hx⟩
  have he := congrArg parityHom hx
  change parityHom (x + x) = parityHom 1 at he
  rw [parityHom_double, map_one] at he
  exact zero_ne_one he

/-- The class of one in the larger-ring algebraic-range quotient is nonzero. -/
theorem coker_one_ne_zero :
    TopModuleCat.cokerπ doubling (1 : regularModule) ≠ 0 := by
  intro h
  exact one_not_mem_doubling_range ((Submodule.Quotient.mk_eq_zero _).mp h)

/-- The class of one in the quotient of the restricted map is also nonzero.
The range is computed with the canonical restricted module structure. -/
theorem restricted_coker_one_ne_zero :
    TopModuleCat.cokerπ
        ((TopModuleCat.restrictScalars reduction continuous_reduction).map doubling)
        (show restrictedModule from 1) ≠ 0 := by
  intro h
  obtain ⟨x, hx⟩ := (Submodule.Quotient.mk_eq_zero _).mp h
  have hmap : @Eq (ZMod 4)
      (((TopModuleCat.restrictScalars reduction continuous_reduction).map doubling).hom x)
      (doubling.hom x) :=
    TopModuleCat.restrictScalars_map_apply reduction continuous_reduction doubling x
  have e : @Eq (ZMod 4) (doubling.hom x) 1 :=
    Eq.trans (α := ZMod 4) hmap.symm hx
  exact one_not_mem_doubling_range ⟨x, e⟩

/-- The chosen categorical projection also retains a nonzero class of one. -/
theorem cokernel_one_ne_zero :
    cokernel.π doubling (1 : regularModule) ≠ 0 := by
  intro h
  let d := cokernel.desc doubling (TopModuleCat.cokerπ doubling)
    (TopModuleCat.comp_cokerπ doubling)
  have hd : d.hom (cokernel.π doubling 1) = TopModuleCat.cokerπ doubling 1 :=
    ConcreteCategory.congr_hom
      (cokernel.π_desc doubling (TopModuleCat.cokerπ doubling)
        (TopModuleCat.comp_cokerπ doubling)) 1
  rw [h, map_zero] at hd
  exact coker_one_ne_zero hd.symm

/-- The canonical comparison acts on the nonzero projected representative as
prescribed by the stock projection law. -/
theorem cokernelComparison_class_one :
    cokernelComparison doubling
        (TopModuleCat.restrictScalars reduction continuous_reduction)
        (cokernel.π
          ((TopModuleCat.restrictScalars reduction continuous_reduction).map doubling)
          (1 : ZMod 4)) =
      (show (TopModuleCat.restrictScalars reduction continuous_reduction).obj
        (cokernel doubling) from cokernel.π doubling 1) := by
  let E := TopModuleCat.restrictScalars reduction continuous_reduction
  let u : E.obj regularModule := (1 : ZMod 4)
  have p1 : @Eq (cokernel (C := TopModuleCat.{0} (ZMod 4)) doubling : Type)
      (cokernelComparison doubling E (cokernel.π (E.map doubling) u))
      ((cokernel.π (E.map doubling) ≫ cokernelComparison doubling E) u) :=
    (ConcreteCategory.comp_apply (C := TopModuleCat.{0} ℤ)
      (X := E.obj regularModule) (Y := cokernel (C := TopModuleCat.{0} ℤ) (E.map doubling))
      (Z := E.obj (cokernel (C := TopModuleCat.{0} (ZMod 4)) doubling))
      (cokernel.π (E.map doubling)) (cokernelComparison doubling E) u).symm
  have p2 : @Eq (cokernel (C := TopModuleCat.{0} (ZMod 4)) doubling : Type)
      ((cokernel.π (E.map doubling) ≫ cokernelComparison doubling E) u)
      ((E.map (cokernel.π doubling)) u) :=
    ConcreteCategory.congr_hom (π_comp_cokernelComparison doubling E) u
  have p3 : @Eq (cokernel (C := TopModuleCat.{0} (ZMod 4)) doubling : Type)
      ((E.map (cokernel.π doubling)) u)
      (show E.obj (cokernel (C := TopModuleCat.{0} (ZMod 4)) doubling) from
        cokernel.π doubling (1 : ZMod 4)) :=
    TopModuleCat.restrictScalars_map_apply reduction continuous_reduction
      (M := regularModule) (N := cokernel (C := TopModuleCat.{0} (ZMod 4)) doubling)
      (cokernel.π doubling) (1 : ZMod 4)
  exact Eq.trans (α := (cokernel (C := TopModuleCat.{0} (ZMod 4)) doubling : Type)) p1
    (Eq.trans (α := (cokernel (C := TopModuleCat.{0} (ZMod 4)) doubling : Type)) p2 p3)

/-- In the reverse orientation, the stock preservation isomorphism returns
the class of one to the cokernel of the restricted map. -/
theorem preservesCokernel_iso_class_one :
    (PreservesCokernel.iso
        (TopModuleCat.restrictScalars reduction continuous_reduction) doubling).hom
        (show (TopModuleCat.restrictScalars reduction continuous_reduction).obj
          (cokernel doubling) from cokernel.π doubling 1) =
      cokernel.π
        ((TopModuleCat.restrictScalars reduction continuous_reduction).map doubling)
        (1 : ZMod 4) := by
  let E := TopModuleCat.restrictScalars reduction continuous_reduction
  let u : E.obj regularModule := (1 : ZMod 4)
  let j : E.obj (cokernel (C := TopModuleCat.{0} (ZMod 4)) doubling) ⟶
      cokernel (C := TopModuleCat.{0} ℤ) (E.map doubling) :=
    (PreservesCokernel.iso E doubling).hom
  have hmap : @Eq (cokernel (C := TopModuleCat.{0} (ZMod 4)) doubling : Type)
      ((E.map (cokernel.π doubling)) u)
      (show E.obj (cokernel (C := TopModuleCat.{0} (ZMod 4)) doubling) from
        cokernel.π doubling (1 : ZMod 4)) :=
    TopModuleCat.restrictScalars_map_apply reduction continuous_reduction
      (M := regularModule) (N := cokernel (C := TopModuleCat.{0} (ZMod 4)) doubling)
      (cokernel.π doubling) (1 : ZMod 4)
  have p1 : @Eq (cokernel (C := TopModuleCat.{0} ℤ) (E.map doubling) : Type)
      (j (show E.obj (cokernel (C := TopModuleCat.{0} (ZMod 4)) doubling) from
        cokernel.π doubling (1 : ZMod 4)))
      (j ((E.map (cokernel.π doubling)) u)) :=
    congrArg (fun z : E.obj (cokernel (C := TopModuleCat.{0} (ZMod 4)) doubling) ↦ j z) hmap.symm
  have p2 : @Eq (cokernel (C := TopModuleCat.{0} ℤ) (E.map doubling) : Type)
      (j ((E.map (cokernel.π doubling)) u))
      ((E.map (cokernel.π doubling) ≫ j) u) :=
    (ConcreteCategory.comp_apply (C := TopModuleCat.{0} ℤ)
      (X := E.obj regularModule) (Y := E.obj (cokernel (C := TopModuleCat.{0} (ZMod 4)) doubling))
      (Z := cokernel (C := TopModuleCat.{0} ℤ) (E.map doubling))
      (E.map (cokernel.π doubling)) j u).symm
  have p3 : @Eq (cokernel (C := TopModuleCat.{0} ℤ) (E.map doubling) : Type)
      ((E.map (cokernel.π doubling) ≫ j) u) (cokernel.π (E.map doubling) u) :=
    ConcreteCategory.congr_hom (PreservesCokernel.π_iso_hom E doubling) u
  exact Eq.trans (α := (cokernel (C := TopModuleCat.{0} ℤ) (E.map doubling) : Type)) p1
    (Eq.trans (α := (cokernel (C := TopModuleCat.{0} ℤ) (E.map doubling) : Type)) p2 p3)

/-- The comparison is an isomorphism, and its value on the class of one is
nonzero; neither concrete quotient is being replaced by a zero object. -/
theorem cokernelComparison_nonzero :
    IsIso (cokernelComparison doubling
        (TopModuleCat.restrictScalars reduction continuous_reduction)) ∧
      cokernelComparison doubling
        (TopModuleCat.restrictScalars reduction continuous_reduction)
        (cokernel.π
          ((TopModuleCat.restrictScalars reduction continuous_reduction).map doubling)
          (1 : ZMod 4)) ≠ 0 := by
  refine ⟨inferInstance, ?_⟩
  rw [cokernelComparison_class_one]
  exact cokernel_one_ne_zero

/-- A discrete integer module representing the finite direct sum `ℤ ⊕ ZMod 2`. -/
noncomputable abbrev parityTarget : TopModuleCat ℤ :=
  TopModuleCat.of ℤ (ℤ × ZMod 2)

/-- The continuous integer-linear parity arrow, with no larger-ring action
on its target. Its source uses the functor's restricted action. -/
noncomputable def parity : restrictedModule ⟶ parityTarget := by
  let q : ZMod 4 →+* ZMod 2 :=
    ZMod.castHom (show 2 ∣ 4 by norm_num) (ZMod 2)
  let p : restrictedModule →+ parityTarget :=
    { toFun := fun x ↦ ((0 : ℤ), q x)
      map_zero' := Prod.ext rfl (map_zero q)
      map_add' := fun x y ↦ Prod.ext (zero_add 0).symm (q.map_add x y) }
  let l := @LinearMap.mk ℤ ℤ inferInstance inferInstance (RingHom.id ℤ)
    restrictedModule parityTarget
    restrictedModule.toModuleCat.isAddCommGroup.toAddCommMonoid
    parityTarget.toModuleCat.isAddCommGroup.toAddCommMonoid
    restrictedModule.toModuleCat.isModule parityTarget.toModuleCat.isModule
    p.toAddHom (fun n x ↦ by
      have hsource := @int_smul_eq_zsmul restrictedModule
        restrictedModule.toModuleCat.isAddCommGroup
        restrictedModule.toModuleCat.isModule n x
      have htarget := @int_smul_eq_zsmul parityTarget
        parityTarget.toModuleCat.isAddCommGroup
        parityTarget.toModuleCat.isModule n (p x)
      exact Eq.trans (α := (parityTarget : Type)) (congrArg p hsource)
        (Eq.trans (α := (parityTarget : Type)) (p.map_zsmul n x) htarget.symm))
  let f := @ContinuousLinearMap.mk ℤ ℤ inferInstance inferInstance (RingHom.id ℤ)
    restrictedModule restrictedModule.topologicalSpace
    restrictedModule.toModuleCat.isAddCommGroup.toAddCommMonoid
    parityTarget parityTarget.topologicalSpace
    parityTarget.toModuleCat.isAddCommGroup.toAddCommMonoid
    restrictedModule.toModuleCat.isModule parityTarget.toModuleCat.isModule l
    ((TopModuleCat.continuous_restrictScalarsObj_iff reduction
      continuous_reduction regularModule (fun x ↦ ((0 : ℤ), q x))).2
        continuous_of_discreteTopology)
  exact ConcreteCategory.ofHom (C := TopModuleCat.{0} ℤ)
    (X := restrictedModule) (Y := parityTarget) f

/-- The parity arrow is evaluated by reduction modulo two in the second coordinate. -/
@[simp]
theorem parity_apply (x : regularModule) :
    parity x = (0, ZMod.castHom (show 2 ∣ 4 by norm_num) (ZMod 2) x) := by
  rfl

/-- The parity arrow kills doubling. -/
theorem doubling_comp_parity :
    (TopModuleCat.restrictScalars reduction continuous_reduction).map doubling ≫ parity = 0 := by
  refine ConcreteCategory.ext_apply (C := TopModuleCat.{0} ℤ)
    (X := restrictedModule) (Y := parityTarget) (fun x ↦ ?_)
  have hcomp : @Eq (ℤ × ZMod 2)
      (((TopModuleCat.restrictScalars reduction continuous_reduction).map doubling ≫ parity) x)
      (parity ((TopModuleCat.restrictScalars reduction continuous_reduction).map doubling x)) :=
    ConcreteCategory.comp_apply (C := TopModuleCat.{0} ℤ)
      ((TopModuleCat.restrictScalars reduction continuous_reduction).map doubling) parity x
  have hpoint : @Eq (ℤ × ZMod 2)
      (parity ((TopModuleCat.restrictScalars reduction continuous_reduction).map doubling x))
      ((0 : ℤ), 0) := by
    rw [TopModuleCat.restrictScalars_map_apply, doubling_apply, parity_apply]
    exact Prod.ext rfl (parityHom_double x)
  have hzero : @Eq (ℤ × ZMod 2) ((0 : restrictedModule ⟶ parityTarget) x) (0, 0) :=
    TopModuleCat.hom_zero_apply ℤ (M₁ := restrictedModule) (M₂ := parityTarget) x
  exact Eq.trans (α := ℤ × ZMod 2) hcomp
    (Eq.trans (α := ℤ × ZMod 2) hpoint hzero.symm)

/-- The parity arrow has a unique continuous integer-linear descendant on the
restricted quotient, whose value on the class of one is nonzero. -/
theorem parity_factors :
    ∃ d : (TopModuleCat.restrictScalars reduction continuous_reduction).obj
        (TopModuleCat.coker doubling) ⟶ parityTarget,
      ((TopModuleCat.restrictScalars reduction continuous_reduction).map
          (TopModuleCat.cokerπ doubling) ≫ d = parity) ∧
      d (TopModuleCat.cokerπ doubling 1) = (0, 1) ∧
      d ≠ 0 ∧
      ∀ d', (TopModuleCat.restrictScalars reduction continuous_reduction).map
          (TopModuleCat.cokerπ doubling) ≫ d' = parity → d' = d := by
  obtain ⟨d, hd, huniq⟩ := TopModuleCat.restrictScalars_coker_existsUnique
    reduction continuous_reduction doubling parity doubling_comp_parity
  let E := TopModuleCat.restrictScalars reduction continuous_reduction
  let u : E.obj regularModule := (1 : ZMod 4)
  have hmap : @Eq (TopModuleCat.coker doubling : Type)
      ((E.map (TopModuleCat.cokerπ doubling)) u)
      (show E.obj (TopModuleCat.coker doubling) from
        TopModuleCat.cokerπ doubling (1 : ZMod 4)) :=
    TopModuleCat.restrictScalars_map_apply reduction continuous_reduction
      (M := regularModule) (N := TopModuleCat.coker doubling)
      (TopModuleCat.cokerπ doubling) (1 : ZMod 4)
  have p1 : @Eq (ℤ × ZMod 2)
      (d (TopModuleCat.cokerπ doubling (1 : ZMod 4)))
      (d ((E.map (TopModuleCat.cokerπ doubling)) u)) :=
    congrArg (fun z : E.obj (TopModuleCat.coker doubling) ↦ d z) hmap.symm
  have p2 : @Eq (ℤ × ZMod 2)
      (d ((E.map (TopModuleCat.cokerπ doubling)) u))
      ((E.map (TopModuleCat.cokerπ doubling) ≫ d) u) :=
    (ConcreteCategory.comp_apply (C := TopModuleCat.{0} ℤ)
      (X := E.obj regularModule) (Y := E.obj (TopModuleCat.coker doubling))
      (Z := parityTarget) (E.map (TopModuleCat.cokerπ doubling)) d u).symm
  have p3 : @Eq (ℤ × ZMod 2)
      ((E.map (TopModuleCat.cokerπ doubling) ≫ d) u) (parity u) :=
    ConcreteCategory.congr_hom hd u
  have p4 : @Eq (ℤ × ZMod 2) (parity u) (0, 1) := by
    rw [parity_apply]
    exact congrArg (fun z : ZMod 2 ↦ ((0 : ℤ), z)) (map_one parityHom)
  have hvalue : d (TopModuleCat.cokerπ doubling 1) = (0, 1) :=
    Eq.trans (α := ℤ × ZMod 2) p1
      (Eq.trans (α := ℤ × ZMod 2) p2 (Eq.trans (α := ℤ × ZMod 2) p3 p4))
  refine ⟨d, hd, hvalue, ?_, fun d' hd' ↦ huniq d' hd'⟩
  intro hz
  have he : @Eq (ℤ × ZMod 2) (d (TopModuleCat.cokerπ doubling 1)) (0, 0) :=
    Eq.trans (α := ℤ × ZMod 2)
      (ConcreteCategory.congr_hom hz (TopModuleCat.cokerπ doubling 1))
      (TopModuleCat.hom_zero_apply ℤ (M₁ := E.obj (TopModuleCat.coker doubling))
        (M₂ := parityTarget) (TopModuleCat.cokerπ doubling 1))
  have hsecond : (1 : ZMod 2) = 0 :=
    congrArg Prod.snd (Eq.trans (α := ℤ × ZMod 2) hvalue.symm he)
  exact one_ne_zero hsecond

/-- Four annihilates every object obtained by restriction from `ZMod 4`. -/
theorem four_smul_restriction (X : TopModuleCat (ZMod 4)) (x : X) :
    @Eq (X : Type)
      (@SMul.smul ℤ (X : Type)
        (TopModuleCat.restrictScalarsObj reduction
          continuous_reduction X).toModuleCat.isModule.toSMul
        (4 : ℤ) x) (0 : X) := by
  have haction : @Eq (X : Type)
      (@SMul.smul ℤ (X : Type)
        (TopModuleCat.restrictScalarsObj reduction
          continuous_reduction X).toModuleCat.isModule.toSMul
        (4 : ℤ) x)
      (@SMul.smul (ZMod 4) (X : Type) X.toModuleCat.isModule.toSMul (reduction 4) x) :=
    TopModuleCat.restrictScalarsObj_smul reduction continuous_reduction X 4 x
  have hfour : reduction 4 = 0 :=
    Eq.trans (α := ZMod 4) (reduction_apply 4) (ZMod.natCast_self 4)
  have hzero : @Eq (X : Type)
      (@SMul.smul (ZMod 4) (X : Type) X.toModuleCat.isModule.toSMul (reduction 4) x)
      (0 : X) :=
    Eq.trans (α := (X : Type))
      (congrArg (fun s : ZMod 4 ↦ @SMul.smul (ZMod 4) (X : Type)
        X.toModuleCat.isModule.toSMul s x) hfour)
      (@Module.zero_smul (ZMod 4) (X : Type) inferInstance
        X.toModuleCat.isAddCommGroup.toAddCommMonoid X.toModuleCat.isModule x)
  exact Eq.trans (α := (X : Type)) haction hzero

/-- The target has an element not killed by four. Thus the arbitrary-target
universal property is not merely testing another restricted module. -/
theorem four_smul_parityTarget_ne_zero :
    (4 : ℤ) • ((1, 0) : parityTarget) ≠ 0 := by
  intro h
  have hfirst := congrArg Prod.fst h
  norm_num at hfirst

end ScalarRestriction.ModFour
