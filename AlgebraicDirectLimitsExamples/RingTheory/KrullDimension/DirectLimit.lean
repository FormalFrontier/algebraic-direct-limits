/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicDirectLimits.RingTheory.KrullDimension.DirectLimit
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Bool.Basic
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Tactic.NormNum

/-!
# Directed-colimit models

The constant integer system has injective characteristic maps. The two-stage
system `ℤ → ZMod 2`, indexed by `false ≤ true`, has a noninjective transition
homomorphism. Its integer-stage characteristic map identifies `2` and `0`, while
its terminal-stage characteristic map distinguishes `0` and `1`.

These facts use the characteristic maps and universal property of the colimit.
The directed-colimit dimension bound specializes to both systems: it bounds the
constant limit by the integer dimension and the quotient limit by the supremum
of the two stage dimensions.

`DirectLimitExamples.constant_dimension_bound` is a public example of the
bound for the constant integer system, expressed using Mathlib's `DirectLimit`
and identity transition maps. The projections and two-stage calculations remain
private supporting examples.
-/

@[expose] public section

namespace DirectLimitExamples

noncomputable section

private def constantProjection :
    DirectLimit (fun _ : ℕ => ℤ) (fun _ _ _ => RingHom.id ℤ) →+* ℤ :=
  DirectLimit.Ring.lift (fun _ : ℕ => ℤ) (fun _ _ _ => RingHom.id ℤ)
    ℤ (fun _ => RingHom.id ℤ) (by intros; rfl)

/-- The universal map of the constant integer system recovers each stage element. -/
private theorem constantProjection_of (i : ℕ) (x : ℤ) :
    constantProjection (DirectLimit.Ring.of (fun _ : ℕ => ℤ)
      (fun _ _ _ => RingHom.id ℤ) i x) = x :=
  DirectLimit.Ring.lift_of (G := fun _ : ℕ => ℤ)
    (f := fun _ _ _ => RingHom.id ℤ) ℤ (fun _ => RingHom.id ℤ) (by intros; rfl) i x

/-- Characteristic maps in the constant integer system are injective. -/
private theorem constant_of_injective (i : ℕ) :
    Function.Injective (DirectLimit.Ring.of (fun _ : ℕ => ℤ)
      (fun _ _ _ => RingHom.id ℤ) i) := by
  intro x y h
  have h' := congrArg constantProjection h
  simpa only [constantProjection_of] using h'

/-- The constant integer limit has dimension at most that of the integers.
This specializes `ringKrullDim_directLimit_le_iSup` to identity transition maps
over the nonempty directed index `ℕ`. -/
theorem constant_dimension_bound :
    ringKrullDim (DirectLimit (fun _ : ℕ => ℤ) (fun _ _ _ => RingHom.id ℤ)) ≤
      ringKrullDim ℤ := by
  simpa using ringKrullDim_directLimit_le_iSup
    (fun _ : ℕ => ℤ) (fun _ _ _ => RingHom.id ℤ)

private def quotientStage : Bool → Type
  | false => ℤ
  | true => ZMod 2

private instance (i : Bool) : CommRing (quotientStage i) := by
  cases i <;> dsimp [quotientStage] <;> infer_instance

private def quotientMap (i j : Bool) (h : i ≤ j) :
    quotientStage i →+* quotientStage j :=
  match i, j with
  | false, false => RingHom.id ℤ
  | false, true => Int.castRingHom (ZMod 2)
  | true, true => RingHom.id (ZMod 2)
  | true, false => False.elim ((by decide : ¬ (true : Bool) ≤ false) h)

private theorem quotientMap_false_true_apply (h : (false : Bool) ≤ true) (x : ℤ) :
    quotientMap false true h x = (x : ZMod 2) := rfl

private theorem quotientMap_true_true_apply (h : (true : Bool) ≤ true) (x : ZMod 2) :
    quotientMap true true h x = x := rfl

private theorem quotientMap_two_eq_zero (h : (false : Bool) ≤ true) :
    quotientMap false true h (2 : quotientStage false) =
      quotientMap false true h 0 := by
  exact (quotientMap_false_true_apply h 2).trans
    ((by decide : ((2 : ℤ) : ZMod 2) = ((0 : ℤ) : ZMod 2)).trans
      (quotientMap_false_true_apply h 0).symm)

private instance : DirectedSystem quotientStage (quotientMap · · ·) where
  map_self := by
    intro i x
    cases i <;> rfl
  map_map := by
    intro k j i hij hjk x
    cases i <;> cases j <;> cases k
      <;> first
      | exact False.elim ((by decide : ¬ (true : Bool) ≤ false) hij)
      | exact False.elim ((by decide : ¬ (true : Bool) ≤ false) hjk)
      | rfl

/-- The dimension bound also applies to a system with a noninjective transition. -/
private theorem quotient_dimension_bound :
    ringKrullDim (DirectLimit quotientStage quotientMap) ≤
      ringKrullDim ℤ ⊔ ringKrullDim (ZMod 2) := by
  calc
    _ ≤ ⨆ i, ringKrullDim (quotientStage i) :=
      ringKrullDim_directLimit_le_iSup quotientStage quotientMap
    _ = _ := by rw [iSup_bool_eq, sup_comm]; rfl

private def quotientProjection : DirectLimit quotientStage quotientMap →+* ZMod 2 :=
  DirectLimit.Ring.lift _ _ (ZMod 2)
    (fun i => quotientMap i true (Bool.le_true i))
    (by
      intro i j h x
      exact DirectedSystem.map_map (f := (quotientMap · · ·)) h (Bool.le_true j) x)

/-- The terminal-stage projection recovers the transition image of every stage element. -/
private theorem quotientProjection_of (i : Bool) (x : quotientStage i) :
    quotientProjection (DirectLimit.Ring.of quotientStage quotientMap i x) =
      quotientMap i true (Bool.le_true i) x :=
  DirectLimit.Ring.lift_of (G := quotientStage) (f := quotientMap) (ZMod 2)
    (fun i => quotientMap i true (Bool.le_true i))
    (by
      intro i j h x
      exact DirectedSystem.map_map (f := (quotientMap · · ·)) h (Bool.le_true j) x) i x

/-- Reduction modulo two is a noninjective transition in the two-stage system. -/
private theorem quotient_transition_not_injective :
    ¬ Function.Injective (quotientMap false true (by decide)) := by
  intro h
  have htwo : (2 : ℤ) = 0 := h (quotientMap_two_eq_zero (by decide))
  exact (by decide : (2 : ℤ) ≠ 0) htwo

/-- The integer-stage characteristic map identifies two distinct integers. -/
private theorem integer_stage_two_eq_zero :
    DirectLimit.Ring.of quotientStage quotientMap false 2 =
      DirectLimit.Ring.of quotientStage quotientMap false 0 := by
  rw [← DirectLimit.Ring.of_f (by decide : false ≤ true) (2 : quotientStage false),
    ← DirectLimit.Ring.of_f (by decide : false ≤ true) (0 : quotientStage false)]
  exact congrArg (DirectLimit.Ring.of quotientStage quotientMap true)
    (quotientMap_two_eq_zero (by decide))

/-- The terminal-stage characteristic map distinguishes zero and one. -/
private theorem terminal_stage_zero_ne_one :
    DirectLimit.Ring.of quotientStage quotientMap true 0 ≠
      DirectLimit.Ring.of quotientStage quotientMap true 1 := by
  intro h
  have h' := congrArg quotientProjection h
  have hzero_one : (0 : ZMod 2) = 1 :=
    ((quotientProjection_of true 0).trans
      (quotientMap_true_true_apply (Bool.le_true true) 0)).symm.trans
        (h'.trans ((quotientProjection_of true 1).trans
          (quotientMap_true_true_apply (Bool.le_true true) 1)))
  exact zero_ne_one hzero_one


end

end DirectLimitExamples
