/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicDirectLimits.PrimeSpectrumFilteredColimits
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Filtered.Connected
public import Mathlib.CategoryTheory.Limits.Connected
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Ring.Int.Field

/-!
# Filtered-colimit spectrum examples

Constant diagrams, a quotient transition, the empty spectrum of a zero ring,
and a non-Hausdorff spectrum test the projection comparison.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicDirectLimitsExamples.PrimeSpectrumFilteredColimits

private instance : IsConnected ℕ := IsFiltered.isConnected ℕ
private instance : IsConnected (Discrete PUnit) := IsFiltered.isConnected _

example (p : PrimeSpectrum ℤ) (j : ℕ) :
    limit.π (((Functor.const ℕ).obj (CommRingCat.of ℤ)).op ⋙
      AlgebraicGeometry.Spec.toTop) (op j)
      (PrimeSpectrum.colimitHomeomorph
        ((Functor.const ℕ).obj (CommRingCat.of ℤ))
        (constCocone ℕ (CommRingCat.of ℤ))
        (isColimitConstCocone ℕ (CommRingCat.of ℤ)) p) = p := by
  calc
    _ = PrimeSpectrum.comap ((constCocone ℕ (CommRingCat.of ℤ)).ι.app j).hom p :=
      PrimeSpectrum.colimitHomeomorph_π_apply
        ((Functor.const ℕ).obj (CommRingCat.of ℤ))
        (constCocone ℕ (CommRingCat.of ℤ))
        (isColimitConstCocone ℕ (CommRingCat.of ℤ)) j p
    _ = p := by
      change PrimeSpectrum.comap (RingHom.id ℤ) p = p
      rfl

/-- The two-stage quotient sequence has one integer stage and residue-ring stages thereafter. -/
def quotientStage : ℕ → CommRingCat
  | 0 => CommRingCat.of ℤ
  | _ + 1 => CommRingCat.of (ZMod 2)

/-- The quotient map followed by identity transitions. -/
def quotientStep : ∀ n, quotientStage n ⟶ quotientStage (n + 1)
  | 0 => CommRingCat.ofHom (Int.castRingHom (ZMod 2))
  | _ + 1 => 𝟙 _

/-- The filtered diagram with a noninjective first transition. -/
def quotientDiagram : ℕ ⥤ CommRingCat := Functor.ofSequence quotientStep

example : ¬ Function.Injective (quotientStep 0).hom := by
  intro hinj
  have heq : (2 : ℤ) = 0 := hinj (by
    change (2 : ZMod 2) = 0
    decide)
  norm_num at heq

example (p : PrimeSpectrum (ZMod 2)) :
    (2 : ℤ) ∈ (PrimeSpectrum.comap (quotientStep 0).hom p).asIdeal := by
  change (2 : ZMod 2) ∈ p.asIdeal
  have hz : (2 : ZMod 2) = 0 := by decide
  rw [hz]
  exact p.asIdeal.zero_mem

example : Nonempty (PrimeSpectrum (ZMod 2)) :=
  PrimeSpectrum.nonempty_iff_nontrivial.mpr inferInstance

example (p : PrimeSpectrum (CommRingCat.FilteredColimits.colimit quotientDiagram)) :
    (2 : ℤ) ∈ (limit.π (quotientDiagram.op ⋙ AlgebraicGeometry.Spec.toTop) (op 0)
      (PrimeSpectrum.colimitHomeomorph quotientDiagram
        (CommRingCat.FilteredColimits.colimitCocone quotientDiagram)
        (CommRingCat.FilteredColimits.colimitCoconeIsColimit quotientDiagram) p)).asIdeal := by
  let cocone := CommRingCat.FilteredColimits.colimitCocone quotientDiagram
  have hnat :=
    (Cocone.w_apply cocone (homOfLE (Nat.le_add_right 0 1)) (2 : ℤ)).symm
  have hzero : (cocone.ι.app 0).hom (2 : ℤ) = 0 := by
    have hz : (ConcreteCategory.hom
        (quotientDiagram.map (homOfLE (Nat.le_add_right 0 1)))) (2 : ℤ) =
        (0 : quotientDiagram.obj 1) := by
      change (2 : ZMod 2) = 0
      decide
    calc
      (cocone.ι.app 0).hom (2 : ℤ) =
          (ConcreteCategory.hom (cocone.ι.app 1))
            ((ConcreteCategory.hom
              (quotientDiagram.map (homOfLE (Nat.le_add_right 0 1)))) (2 : ℤ)) := hnat
      _ = (cocone.ι.app 1).hom 0 := by rw [hz]
      _ = 0 := map_zero _
  have hmem : (2 : ℤ) ∈ (PrimeSpectrum.comap (cocone.ι.app 0).hom p).asIdeal := by
    change (cocone.ι.app 0).hom (2 : ℤ) ∈ p.asIdeal
    rw [hzero]
    exact p.asIdeal.zero_mem
  exact (PrimeSpectrum.colimitHomeomorph_π_apply quotientDiagram cocone
    (CommRingCat.FilteredColimits.colimitCoconeIsColimit quotientDiagram) 0 p).symm ▸ hmem

example : IsEmpty (PrimeSpectrum (ZMod 1)) := inferInstance

example : IsEmpty (↥(limit (((Functor.const (Discrete PUnit)).obj
    (CommRingCat.of (ZMod 1))).op ⋙
    AlgebraicGeometry.Spec.toTop) : TopCat)) := by
  refine ⟨fun p => ?_⟩
  let projection := limit.π (((Functor.const (Discrete PUnit)).obj
    (CommRingCat.of (ZMod 1))).op ⋙ AlgebraicGeometry.Spec.toTop)
      (op (Discrete.mk PUnit.unit))
  have point : PrimeSpectrum (ZMod 1) := projection.hom p
  exact isEmptyElim point

example : ¬ T1Space (PrimeSpectrum ℤ) := by
  intro h
  exact Int.not_isField (PrimeSpectrum.t1Space_iff_isField.mp h)

example : ¬ T2Space (PrimeSpectrum ℤ) := by
  intro h
  exact Int.not_isField (PrimeSpectrum.t1Space_iff_isField.mp
    (@T2Space.t1Space (PrimeSpectrum ℤ) _ h))

end AlgebraicDirectLimitsExamples.PrimeSpectrumFilteredColimits
