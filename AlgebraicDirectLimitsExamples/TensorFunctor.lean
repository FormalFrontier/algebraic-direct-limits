/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicDirectLimits.Topology.TensorFunctor
public import AlgebraicDirectLimitsExamples.TensorProduct

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
-/

@[expose] public section

open CategoryTheory

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

end TensorProductExamples
