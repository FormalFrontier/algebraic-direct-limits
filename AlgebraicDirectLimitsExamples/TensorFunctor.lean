/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicDirectLimits.Topology.TensorFunctor
public import AlgebraicDirectLimitsExamples.TensorProduct
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Associator

/-!
# Integer examples for tensoring the topological factor

Fix the rank-two coefficient module `integerPairCoefficients` and apply
`TopModuleCat.tensorLeftFunctor` to endomorphisms of `integerModule`. The first
example identifies functorial doubling with `doubledFirstTensor`; the second
evaluates preservation of addition on the same tensor.

The coordinate and nonvanishing facts `firstGeneratorTensor_coordinates`,
`firstGeneratorTensor_ne_zero`, `doubledFirstTensor_coordinate_zero`, and
`doubledFirstTensor_ne_first` from `AlgebraicDirectLimitsExamples.TensorProduct`
show that this is a nonzero integer tensor moved by doubling. No general
faithfulness claim is made: the functor also allows zero coefficient and right
modules.

The finite free coefficient module also exercises injectivity and monomorphism
preservation on the same doubling map. With `ZMod 2` coefficients the original
map is still mono, but its tensor map kills the nonzero tensor `1 ⊗ 1`.
Nonvanishing is detected by bilinear reduction to `ZMod 2`, using Mathlib's
algebraic tensor universal property; no topology on `ZMod 2` is needed.
These examples extend the
integer tensor model using the fixed-coefficient functor.
-/

@[expose] public section

open CategoryTheory
open scoped TensorProduct

namespace TensorProductExamples

/-- Functorial integer doubling agrees with the algebraic tensor-map value. -/
theorem tensorLeftFunctor_integerDoubling_first :
    ((TopModuleCat.tensorLeftFunctor ℤ integerPairCoefficients).map
      (CategoryTheory.ConcreteCategory.ofHom
        (C := TopModuleCat.{0} ℤ)
        (X := integerModule) (Y := integerModule)
        integerDoubling)).hom firstGeneratorTensor = doubledFirstTensor :=
  integerTensorDoubling_firstGenerator

/-- Preservation of addition evaluates doubling plus identity on the first generator. -/
theorem tensorLeftFunctor_integer_additive_use :
    ((TopModuleCat.tensorLeftFunctor ℤ integerPairCoefficients).map
      ((CategoryTheory.ConcreteCategory.ofHom
        (C := TopModuleCat.{0} ℤ)
        (X := integerModule) (Y := integerModule)
        integerDoubling) + 𝟙 integerModule)).hom firstGeneratorTensor =
      doubledFirstTensor + firstGeneratorTensor := by
  let F : TopModuleCat.{0} ℤ ⥤ TopModuleCat.{0} ℤ :=
    TopModuleCat.tensorLeftFunctor ℤ integerPairCoefficients
  let T : TopModuleCat.{0} ℤ :=
    TopModuleCat.tensorLeftObj ℤ integerPairCoefficients integerModule
  let d : integerModule ⟶ integerModule :=
    CategoryTheory.ConcreteCategory.ofHom
      (C := TopModuleCat.{0} ℤ) (X := integerModule) (Y := integerModule)
      integerDoubling
  have hid : @Eq (T : Type) ((F.map (𝟙 integerModule)).hom firstGeneratorTensor)
      firstGeneratorTensor :=
    Eq.trans (α := (T : Type))
      (congrArg
        (fun k : F.obj integerModule ⟶ F.obj integerModule =>
          k.hom firstGeneratorTensor)
        (CategoryTheory.Functor.map_id F integerModule))
      (CategoryTheory.id_apply (X := F.obj integerModule) firstGeneratorTensor)
  exact Eq.trans (α := (T : Type))
    (congrArg
      (fun k : F.obj integerModule ⟶ F.obj integerModule =>
        k.hom firstGeneratorTensor)
      (Functor.map_add F (f := d) (g := 𝟙 integerModule)))
    (Eq.trans (α := (T : Type))
      (congrArg
        (fun k : F.obj integerModule →L[ℤ] F.obj integerModule =>
          k firstGeneratorTensor)
        (TopModuleCat.hom_add ℤ (F.map d) (F.map (𝟙 integerModule))))
      (Eq.trans (α := (T : Type))
        (add_apply (F.map d).hom (F.map (𝟙 integerModule)).hom firstGeneratorTensor)
        (congrArg₂ (fun x y : T => x + y)
          tensorLeftFunctor_integerDoubling_first hid)))

/-- The free integer-pair coefficients preserve injectivity and monicity of doubling. -/
theorem tensorLeftFunctor_integerDoubling_monomorphisms :
    let d : integerModule ⟶ integerModule :=
      ConcreteCategory.ofHom (C := TopModuleCat.{0} ℤ)
        (X := integerModule) (Y := integerModule) integerDoubling
    Mono d ∧
      Function.Injective ((TopModuleCat.tensorLeftFunctor ℤ integerPairCoefficients).map d).hom ∧
      Mono ((TopModuleCat.tensorLeftFunctor ℤ integerPairCoefficients).map d) := by
  let d : integerModule ⟶ integerModule :=
    ConcreteCategory.ofHom (C := TopModuleCat.{0} ℤ)
      (X := integerModule) (Y := integerModule) integerDoubling
  letI : Module.Free ℤ integerPairCoefficients :=
    Module.Free.of_basis (Module.Basis.finTwoProd ℤ)
  have hi : Function.Injective integerDoubling := by
    intro x y h
    have h' : (2 : ℤ) * x = 2 * y := by
      simpa [integerDoubling, two_smul, two_mul] using h
    exact mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0) h'
  haveI hd : Mono d := ConcreteCategory.mono_of_injective d hi
  exact ⟨hd, TopModuleCat.tensorLeftFunctor_map_injective ℤ integerPairCoefficients d hi,
    Functor.map_mono (TopModuleCat.tensorLeftFunctor ℤ integerPairCoefficients) d⟩

/-- Bilinear reduction observes the original tensor using Mathlib's universal property.
The scalar laws compare each stored integer action pointwise with additive scaling. -/
private noncomputable def modTwoIntegerTensorObservation :
    TensorProduct ℤ (ModuleCat.of ℤ (ZMod 2)) integerModule →ₗ[ℤ] ZMod 2 :=
  TensorProduct.lift
    (LinearMap.mk₂ ℤ
      (fun (c : ModuleCat.of ℤ (ZMod 2)) (z : integerModule) =>
        (c : ZMod 2) * ((z : ℤ) : ZMod 2))
      (by
        intro c c' z
        exact add_mul (c : ZMod 2) (c' : ZMod 2) ((z : ℤ) : ZMod 2))
      (by
        intro r c z
        let g : ModuleCat.of ℤ (ZMod 2) →+ ZMod 2 :=
          AddMonoidHom.mulRight ((z : ℤ) : ZMod 2)
        have hcast : Int.instCommRing.intCast r = r := rfl
        have hsmul :
            g (Int.instCommRing.intCast r • c) =
              Int.instCommRing.intCast r • g c :=
          @map_intCast_smul
            (M := ModuleCat.of ℤ (ZMod 2)) (M₂ := ZMod 2)
            (ModuleCat.of ℤ (ZMod 2)).isAddCommGroup
            (inferInstance : AddCommGroup (ZMod 2))
            (F := ModuleCat.of ℤ (ZMod 2) →+ ZMod 2)
            (inferInstance : FunLike (ModuleCat.of ℤ (ZMod 2) →+ ZMod 2)
              (ModuleCat.of ℤ (ZMod 2)) (ZMod 2))
            (inferInstance : AddMonoidHomClass (ModuleCat.of ℤ (ZMod 2) →+ ZMod 2)
              (ModuleCat.of ℤ (ZMod 2)) (ZMod 2))
            (f := g) (R := ℤ) (S := ℤ)
            Int.instCommRing.toRing Int.instCommRing.toRing
            (ModuleCat.of ℤ (ZMod 2)).isModule
            (inferInstance : Module ℤ (ZMod 2))
            (x := r) (a := c)
        have hbeta :
            ((r • c : ModuleCat.of ℤ (ZMod 2)) : ZMod 2) *
                ((z : ℤ) : ZMod 2) =
              r • ((c : ZMod 2) * ((z : ℤ) : ZMod 2)) :=
          Eq.mp (congrArg (fun s : ℤ => g (s • c) = s • g c) hcast) hsmul
        exact hbeta)
      (by
        intro c z z'
        exact (congrArg (fun a : ZMod 2 => (c : ZMod 2) * a)
          (Int.cast_add (R := ZMod 2) (z : ℤ) (z' : ℤ))).trans
          (mul_add (c : ZMod 2) ((z : ℤ) : ZMod 2) ((z' : ℤ) : ZMod 2)))
      (by
        intro r c z
        let h : integerModule →+ ZMod 2 :=
          (AddMonoidHom.mulLeft (c : ZMod 2)).comp (Int.castAddHom (ZMod 2))
        have hcast : Int.instCommRing.intCast r = r := rfl
        have hsmul :
            h (Int.instCommRing.intCast r • z) =
              Int.instCommRing.intCast r • h z :=
          @map_intCast_smul
            (M := integerModule) (M₂ := ZMod 2)
            integerModule.toModuleCat.isAddCommGroup
            (inferInstance : AddCommGroup (ZMod 2))
            (F := integerModule →+ ZMod 2)
            (inferInstance : FunLike (integerModule →+ ZMod 2)
              integerModule (ZMod 2))
            (inferInstance : AddMonoidHomClass (integerModule →+ ZMod 2)
              integerModule (ZMod 2))
            (f := h) (R := ℤ) (S := ℤ)
            Int.instCommRing.toRing Int.instCommRing.toRing
            integerModule.toModuleCat.isModule
            (inferInstance : Module ℤ (ZMod 2))
            (x := r) (a := z)
        have hbeta :
            (c : ZMod 2) * (((r • z : integerModule) : ℤ) : ZMod 2) =
              r • ((c : ZMod 2) * ((z : ℤ) : ZMod 2)) :=
          Eq.mp (congrArg (fun s : ℤ => h (s • z) = s • h z) hcast) hsmul
        exact hbeta))

private theorem modTwoIntegerTensorObservation_tmul_one :
    modTwoIntegerTensorObservation
      ((1 : ModuleCat.of ℤ (ZMod 2)) ⊗ₜ[ℤ] (1 : integerModule)) = 1 := by
  unfold modTwoIntegerTensorObservation
  calc
    _ = _ :=
      TensorProduct.lift.tmul
        (1 : ModuleCat.of ℤ (ZMod 2)) (1 : integerModule)
    _ = (1 : ZMod 2) * (((1 : integerModule) : ℤ) : ZMod 2) :=
      LinearMap.mk₂_apply ℤ
        (fun (c : ModuleCat.of ℤ (ZMod 2)) (z : integerModule) =>
          (c : ZMod 2) * ((z : ℤ) : ZMod 2))
        (1 : ModuleCat.of ℤ (ZMod 2)) (1 : integerModule)
    _ = 1 :=
      (congrArg (fun a : ZMod 2 => (1 : ZMod 2) * a)
        (Int.cast_one (R := ZMod 2))).trans (mul_one (1 : ZMod 2))

/-- Without flat coefficients, integer doubling can cease to be injective or mono. -/
theorem tensorLeftFunctor_modTwo_doubling_boundary :
    let d : integerModule ⟶ integerModule :=
      ConcreteCategory.ofHom (C := TopModuleCat.{0} ℤ)
        (X := integerModule) (Y := integerModule) integerDoubling
    let F := TopModuleCat.tensorLeftFunctor ℤ (ModuleCat.of ℤ (ZMod 2))
    Mono d ∧ ¬ Function.Injective (F.map d).hom ∧ ¬ Mono (F.map d) := by
  let d : integerModule ⟶ integerModule :=
    ConcreteCategory.ofHom (C := TopModuleCat.{0} ℤ)
      (X := integerModule) (Y := integerModule) integerDoubling
  let F := TopModuleCat.tensorLeftFunctor ℤ (ModuleCat.of ℤ (ZMod 2))
  let A : Type := TensorProduct ℤ (ModuleCat.of ℤ (ZMod 2)) integerModule
  have hd : Mono d := tensorLeftFunctor_integerDoubling_monomorphisms.1
  let x : F.obj integerModule :=
    (1 : ModuleCat.of ℤ (ZMod 2)) ⊗ₜ[ℤ] (1 : integerModule)
  have hx : x ≠ 0 := by
    intro h
    have he : modTwoIntegerTensorObservation x = 0 :=
      (congrArg modTwoIntegerTensorObservation h).trans modTwoIntegerTensorObservation.map_zero
    have hone : modTwoIntegerTensorObservation x = (1 : ZMod 2) :=
      modTwoIntegerTensorObservation_tmul_one
    exact one_ne_zero (hone.symm.trans he)
  have hzero : @Eq A ((F.map d).hom x) 0 := by
    have hd_one : d.hom (1 : integerModule) = (1 : integerModule) + 1 := by
      simpa only [d, ConcreteCategory.hom_ofHom, one_add_one_eq_two] using
        integerDoubling_apply_one
    have hcoeff : (1 : ModuleCat.of ℤ (ZMod 2)) + 1 = 0 := by
      have hcast : ((2 : ℕ) : ZMod 2) = (1 : ZMod 2) + 1 :=
        (Nat.cast_add (R := ZMod 2) 1 1).trans
          (congrArg₂ (fun a b : ZMod 2 => a + b)
            (Nat.cast_one (R := ZMod 2)) (Nat.cast_one (R := ZMod 2)))
      exact hcast.symm.trans (ZMod.natCast_self 2)
    have hentry : @Eq A ((F.map d).hom x)
        ((1 : ModuleCat.of ℤ (ZMod 2)) ⊗ₜ[ℤ] d.hom (1 : integerModule)) :=
      TopModuleCat.tensorLeftFunctor_map_tmul ℤ (ModuleCat.of ℤ (ZMod 2)) d
        (1 : ModuleCat.of ℤ (ZMod 2)) (1 : integerModule)
    have hdouble : @Eq A
        ((1 : ModuleCat.of ℤ (ZMod 2)) ⊗ₜ[ℤ] d.hom (1 : integerModule))
        ((1 : ModuleCat.of ℤ (ZMod 2)) ⊗ₜ[ℤ] ((1 : integerModule) + 1)) :=
      congrArg (fun z : integerModule =>
        ((1 : ModuleCat.of ℤ (ZMod 2)) ⊗ₜ[ℤ] z : A)) hd_one
    have hrightAdd : @Eq A
        ((1 : ModuleCat.of ℤ (ZMod 2)) ⊗ₜ[ℤ] ((1 : integerModule) + 1)) (x + x) :=
      TensorProduct.tmul_add (R := ℤ) (1 : ModuleCat.of ℤ (ZMod 2))
        (1 : integerModule) 1
    have hleftAdd : @Eq A (x + x)
        (((1 : ModuleCat.of ℤ (ZMod 2)) + 1) ⊗ₜ[ℤ] (1 : integerModule)) :=
      (TensorProduct.add_tmul (R := ℤ) (1 : ModuleCat.of ℤ (ZMod 2)) 1
        (1 : integerModule)).symm
    have hcoefficient : @Eq A
        (((1 : ModuleCat.of ℤ (ZMod 2)) + 1) ⊗ₜ[ℤ] (1 : integerModule))
        ((0 : ModuleCat.of ℤ (ZMod 2)) ⊗ₜ[ℤ] (1 : integerModule)) :=
      congrArg (fun c : ModuleCat.of ℤ (ZMod 2) =>
        (c ⊗ₜ[ℤ] (1 : integerModule) : A)) hcoeff
    have hzeroTensor : @Eq A
        ((0 : ModuleCat.of ℤ (ZMod 2)) ⊗ₜ[ℤ] (1 : integerModule)) 0 :=
      TensorProduct.zero_tmul (R := ℤ) (ModuleCat.of ℤ (ZMod 2)) (1 : integerModule)
    exact Eq.trans (α := A) hentry
      (Eq.trans (α := A) hdouble
        (Eq.trans (α := A) hrightAdd
          (Eq.trans (α := A) hleftAdd
            (Eq.trans (α := A) hcoefficient hzeroTensor))))
  have hn : ¬ Function.Injective (F.map d).hom := by
    intro hi
    exact hx (hi (hzero.trans (map_zero (F.map d).hom).symm))
  refine ⟨hd, hn, ?_⟩
  intro hm
  letI : Mono (F.map d) := hm
  let U : TopModuleCat.{0} ℤ ⥤ ModuleCat.{0} ℤ := forget₂ _ _
  haveI : U.PreservesMonomorphisms :=
    CategoryTheory.preservesMonomorphisms_of_preservesLimitsOfShape U
  exact hn ((ModuleCat.mono_iff_injective (U.map (F.map d))).mp
    (Functor.map_mono U (F.map d)))

end TensorProductExamples
