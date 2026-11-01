/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Colimit.DirectLimit
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Data.Matrix.Basic
public import AlgebraicDirectLimits.Order.DirectedSystem
import AlgebraicDirectLimits.Matrix.ProductDescentSignature

/-!
# Matrix units over directed semiring limits

The coefficient ring homomorphisms act entrywise on square matrices and hence on
units. These maps form a directed system and a compatible family into matrices
over the coefficient limit.

The equivalence `matrixUnitsColimitEquiv` identifies the limit of finite
square-matrix unit groups with the matrix units over the coefficient limit.
A matrix and its inverse descend together, and equality of stage images is
witnessed at a common stage above both sources. Transition maps need not be
injective, and the matrix dimension may be empty.
-/

@[expose] public section

universe uι uR uκ

namespace DirectLimit

variable {ι : Type uι} [Preorder ι]
variable (κ : Type uκ) [Fintype κ] [DecidableEq κ]
variable (R : ι → Type uR) [∀ i, Semiring (R i)]
variable (f : ∀ i j, i ≤ j → R i →+* R j)

/-- The map of matrix-unit groups induced by a coefficient transition. -/
abbrev matrixUnitsMap (i j : ι) (h : i ≤ j) :
    (Matrix κ κ (R i))ˣ →* (Matrix κ κ (R j))ˣ :=
  Units.map (f i j h).mapMatrix.toMonoidHom

@[simp]
theorem matrixUnitsMap_val_apply (i j : ι) (h : i ≤ j)
    (u : (Matrix κ κ (R i))ˣ) (a b : κ) :
    (matrixUnitsMap κ R f i j h u : Matrix κ κ (R j)) a b =
      f i j h (u.val a b) := rfl

@[simp]
theorem matrixUnitsMap_inv_apply (i j : ι) (h : i ≤ j)
    (u : (Matrix κ κ (R i))ˣ) (a b : κ) :
    (matrixUnitsMap κ R f i j h u).inv a b =
      f i j h (u.inv a b) := rfl

variable [DirectedSystem R (fun i j h ↦ (f i j h : R i → R j))]

/-- Entrywise transition maps on units form a directed system. -/
instance matrixUnitsDirectedSystem :
    DirectedSystem (fun i ↦ (Matrix κ κ (R i))ˣ)
      (fun i j h ↦ matrixUnitsMap κ R f i j h) where
  map_self {i} u := by
    apply Units.ext
    funext a b
    exact DirectedSystem.map_self (f := fun i j h ↦ (f i j h : R i → R j)) _
  map_map {k j i} hij hjk u := by
    apply Units.ext
    funext a b
    exact DirectedSystem.map_map (f := fun i j h ↦ (f i j h : R i → R j)) hij hjk _

variable [IsDirectedOrder ι] [Nonempty ι]

/-- The stage map to matrix units over the coefficient direct limit. -/
noncomputable def matrixUnitsOf (i : ι) :
    (Matrix κ κ (R i))ˣ →* (Matrix κ κ (_root_.DirectLimit R f))ˣ :=
  Units.map (Ring.of R f i).mapMatrix.toMonoidHom

@[simp]
theorem matrixUnitsOf_val_apply (i : ι) (u : (Matrix κ κ (R i))ˣ) (a b : κ) :
    (matrixUnitsOf κ R f i u : Matrix κ κ (_root_.DirectLimit R f)) a b =
      Ring.of R f i (u.val a b) := rfl

@[simp]
theorem matrixUnitsOf_inv_apply (i : ι) (u : (Matrix κ κ (R i))ˣ) (a b : κ) :
    (matrixUnitsOf κ R f i u).inv a b =
      Ring.of R f i (u.inv a b) := rfl

/-- The stage maps on matrix units respect coefficient transitions. -/
@[simp]
theorem matrixUnitsOf_f (i j : ι) (h : i ≤ j) (u : (Matrix κ κ (R i))ˣ) :
    matrixUnitsOf κ R f j (matrixUnitsMap κ R f i j h u) =
      matrixUnitsOf κ R f i u := by
  apply Units.ext
  funext a b
  exact Ring.of_f (G := R) (f := f) h (u.val a b)

/-- The comparison from the direct limit of matrix-unit groups to matrix units
 over the coefficient direct limit. -/
noncomputable def matrixUnitsToLimit :
    _root_.DirectLimit (fun i ↦ (Matrix κ κ (R i))ˣ)
      (fun i j h ↦ matrixUnitsMap κ R f i j h) →*
        (Matrix κ κ (_root_.DirectLimit R f))ˣ where
  toFun := _root_.DirectLimit.lift
    (fun i j h ↦ matrixUnitsMap κ R f i j h)
    (fun i ↦ matrixUnitsOf κ R f i)
    (fun i j h u ↦ (matrixUnitsOf_f κ R f i j h u).symm)
  map_one' := lift_one (fun i ↦ matrixUnitsOf κ R f i) _
  map_mul' := lift_mul (fun i ↦ matrixUnitsOf κ R f i) _

/-- The comparison on a matrix unit represented at one stage. -/
@[simp]
theorem matrixUnitsToLimit_mk (i : ι) (u : (Matrix κ κ (R i))ˣ) :
    matrixUnitsToLimit κ R f ⟦⟨i, u⟩⟧ = matrixUnitsOf κ R f i u := rfl

/-- A unit matrix over the coefficient direct limit is the image of a unit
matrix over one stage. Both ordered inverse equations descend together. -/
theorem exists_matrix_unit_representation
    (u : (Matrix κ κ (_root_.DirectLimit R f))ˣ) :
    ∃ (i : ι) (v : (Matrix κ κ (R i))ˣ), matrixUnitsOf κ R f i v = u := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  have h1 : (1 : Matrix κ κ (R i)).map (Ring.of R f i) = 1 :=
    map_one (Ring.of R f i).mapMatrix
  obtain ⟨k, hik, hjk, A, B, hA, _, hAB, hBA⟩ :=
    exists_matrix_products R f
      i i (1 : Matrix κ κ (R i)) (1 : Matrix κ κ (R i))
      u.val u.inv (u.val_inv.trans h1.symm) (u.inv_val.trans h1.symm)
  refine ⟨k, ⟨A, B, ?_, ?_⟩, ?_⟩
  · exact hAB.trans (map_one (f i k hik).mapMatrix)
  · exact hBA.trans (map_one (f i k hjk).mapMatrix)
  · apply Units.ext
    exact hA

/-- Two stage matrix units have equal images if and only if their transitions
agree at a common stage above both source stages. -/
theorem matrixUnitsOf_eq_iff {i j : ι}
    (u : (Matrix κ κ (R i))ˣ) (v : (Matrix κ κ (R j))ˣ) :
    matrixUnitsOf κ R f i u = matrixUnitsOf κ R f j v ↔
      ∃ (k : ι) (hik : i ≤ k) (hjk : j ≤ k),
        matrixUnitsMap κ R f i k hik u = matrixUnitsMap κ R f j k hjk v := by
  constructor
  · intro h
    have hentries (p : κ × κ) :
        (⟦⟨i, u.val p.1 p.2⟩⟧ : _root_.DirectLimit R f) =
          ⟦⟨j, v.val p.1 p.2⟩⟧ :=
      congrArg (fun w : (Matrix κ κ (_root_.DirectLimit R f))ˣ ↦
        w.val p.1 p.2) h
    obtain ⟨k, hik, hjk, hk⟩ :=
      (forall_mk_eq_iff_exists_of_fixed f i j
        (fun p : κ × κ ↦ u.val p.1 p.2)
        (fun p : κ × κ ↦ v.val p.1 p.2)).mp hentries
    refine ⟨k, hik, hjk, ?_⟩
    apply Units.ext
    funext a b
    exact hk (a, b)
  · rintro ⟨k, hik, hjk, h⟩
    calc
      matrixUnitsOf κ R f i u =
          matrixUnitsOf κ R f k (matrixUnitsMap κ R f i k hik u) :=
        (matrixUnitsOf_f κ R f i k hik u).symm
      _ = matrixUnitsOf κ R f k (matrixUnitsMap κ R f j k hjk v) :=
        congrArg (matrixUnitsOf κ R f k) h
      _ = matrixUnitsOf κ R f j v := matrixUnitsOf_f κ R f j k hjk v

/-- The matrix-unit comparison reflects equality in the source direct limit. -/
theorem matrixUnitsToLimit_injective :
    Function.Injective (matrixUnitsToLimit κ R f) := by
  intro x y
  refine Quotient.inductionOn₂ x y ?_
  rintro ⟨i, u⟩ ⟨j, v⟩ h
  obtain ⟨k, hik, hjk, hk⟩ := (matrixUnitsOf_eq_iff κ R f u v).mp h
  exact ((forall_mk_eq_iff_exists_of_fixed
    (fun i j h ↦ matrixUnitsMap κ R f i j h) i j
    (fun _ : Unit ↦ u) (fun _ : Unit ↦ v)).mpr
      ⟨k, hik, hjk, fun _ ↦ hk⟩) ()

/-- Every matrix unit over the coefficient limit comes from the source limit. -/
theorem matrixUnitsToLimit_surjective :
    Function.Surjective (matrixUnitsToLimit κ R f) := by
  intro w
  obtain ⟨i, u, hu⟩ := exists_matrix_unit_representation κ R f w
  refine ⟨⟦⟨i, u⟩⟧, ?_⟩
  exact (matrixUnitsToLimit_mk κ R f i u).trans hu

/-- Finite square-matrix units commute with directed limits of semirings.
The forward map is induced entrywise by the coefficient stage maps. -/
noncomputable def matrixUnitsColimitEquiv :
    _root_.DirectLimit (fun i ↦ (Matrix κ κ (R i))ˣ)
      (fun i j h ↦ matrixUnitsMap κ R f i j h) ≃*
        (Matrix κ κ (_root_.DirectLimit R f))ˣ :=
  MulEquiv.ofBijective (matrixUnitsToLimit κ R f)
    ⟨matrixUnitsToLimit_injective κ R f, matrixUnitsToLimit_surjective κ R f⟩

/-- The equivalence sends a stage representative to its entrywise image. -/
@[simp]
theorem matrixUnitsColimitEquiv_mk (i : ι) (u : (Matrix κ κ (R i))ˣ) :
    matrixUnitsColimitEquiv κ R f ⟦⟨i, u⟩⟧ = matrixUnitsOf κ R f i u := rfl

/-- The inverse equivalence sends a stage image back to that representative. -/
@[simp]
theorem matrixUnitsColimitEquiv_symm_apply_stage
    (i : ι) (u : (Matrix κ κ (R i))ˣ) :
    (matrixUnitsColimitEquiv κ R f).symm (matrixUnitsOf κ R f i u) =
      ⟦⟨i, u⟩⟧ := by
  rw [← matrixUnitsColimitEquiv_mk κ R f i u]
  exact (matrixUnitsColimitEquiv κ R f).symm_apply_apply _

end DirectLimit
