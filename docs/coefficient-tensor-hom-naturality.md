# Coefficient tensor–Hom naturality

Fix `R : Type uR` with `[CommRing R] [TopologicalSpace R]` and
`M : TopModuleCat.{w} R`. Write

- `F := TopModuleCat.coefficientTensor R M`, with coefficients in `ModuleCat.{w} R`;
- `G := (CategoryTheory.linearCoyoneda R (TopModuleCat.{w} R)).obj (Opposite.op M)`;
- `e(C,N) := TopModuleCat.coefficientTensorHomEquiv R M C N`.

Thus `e(C,N) : (F.obj C ⟶ N) ≃ (C ⟶ G.obj N)` is the existing **plain equivalence**.
`G.obj N` is the algebraic module of categorical continuous linear maps `M ⟶ N`;
no topology on this Hom module is chosen. On morphisms, `G.map v` is
postcomposition by `v`, through Mathlib's `CategoryTheory.Linear.rightComp`.

## Naturality signatures

The two identities are contravariance in the coefficient and covariance in the
target. Their signatures are stated in the following context:

```lean
import AlgebraicDirectLimits.Topology.CoefficientTensor

open CategoryTheory
universe uR w
namespace TopModuleCat
```

```lean
theorem coefficientTensorHomEquiv_naturality_left
    (R : Type uR) [CommRing R] [TopologicalSpace R]
    (M : TopModuleCat.{w} R) {C D : ModuleCat.{w} R}
    {N : TopModuleCat.{w} R} (u : D ⟶ C)
    (f : (TopModuleCat.coefficientTensor R M).obj C ⟶ N) :
    TopModuleCat.coefficientTensorHomEquiv R M D N
        ((TopModuleCat.coefficientTensor R M).map u ≫ f) =
      u ≫ TopModuleCat.coefficientTensorHomEquiv R M C N f
```

```lean
theorem coefficientTensorHomEquiv_naturality_right
    (R : Type uR) [CommRing R] [TopologicalSpace R]
    (M : TopModuleCat.{w} R) {C : ModuleCat.{w} R}
    {N N' : TopModuleCat.{w} R}
    (f : (TopModuleCat.coefficientTensor R M).obj C ⟶ N)
    (v : N ⟶ N') :
    TopModuleCat.coefficientTensorHomEquiv R M C N' (f ≫ v) =
      TopModuleCat.coefficientTensorHomEquiv R M C N f ≫
        ((CategoryTheory.linearCoyoneda R (TopModuleCat.{w} R)).obj
          (Opposite.op M)).map v
```

```lean
end TopModuleCat
```

The suffixes match Mathlib's
[`Adjunction.homEquiv_naturality_left` and `…_right`](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/CategoryTheory/Adjunction/Basic.lean#L230-L238).
Those general results require an adjunction; they do not supply naturality of
an arbitrary plain equivalence. Neither an adjunction nor a new Hom functor is
part of these signatures.

The scalar universe `uR` is independent of `w`. The common carrier universe `w`
for `C,D,M,N,N'` is exactly the scope of the existing categorical Hom equivalence.
The more general `coefficientTensor` already permits separate coefficient and
right-factor universes, with target universe their maximum; the signatures above
do not extend that capability to the Hom equivalence. All module and continuity
assumptions come from the stored category objects. There is no coefficient
topology, topological-ring or separation premise, finiteness/free-basis hypothesis,
projectivity assumption, or additional law witness.

## One nonzero integer model for both identities

Use the usual topology on the integers. The following constructor recipes use
only the existing functors and equivalence. `F` and `G` below are aliases, not new
functor constructions. In particular, `C = D = G.obj M` uses the canonical stored
module of categorical endomorphisms, without identifying separately chosen
module structures or putting a topology on `C`.

```lean
import AlgebraicDirectLimits.Topology.CoefficientTensor
import Mathlib.Topology.Instances.Int

open CategoryTheory
open scoped TensorProduct

namespace CoefficientTensorHomInteger
noncomputable section

abbrev M : TopModuleCat.{0} ℤ := TopModuleCat.of ℤ ℤ
abbrev N : TopModuleCat.{0} ℤ := M
abbrev N' : TopModuleCat.{0} ℤ := M
abbrev F : ModuleCat.{0} ℤ ⥤ TopModuleCat.{0} ℤ :=
  TopModuleCat.coefficientTensor ℤ M
abbrev G : TopModuleCat.{0} ℤ ⥤ ModuleCat.{0} ℤ :=
  (CategoryTheory.linearCoyoneda ℤ (TopModuleCat.{0} ℤ)).obj
    (Opposite.op M)
abbrev C : ModuleCat.{0} ℤ := G.obj M
abbrev D : ModuleCat.{0} ℤ := C

def φ : C := (𝟙 M : M ⟶ M)
def m : M := (1 : ℤ)
def h : C ⟶ G.obj M := 𝟙 C
def f : F.obj C ⟶ M :=
  (TopModuleCat.coefficientTensorHomEquiv ℤ M C M).symm h
def u : D ⟶ C := (2 : ℤ) • (𝟙 C)
def v : N ⟶ N' := (3 : ℤ) • (𝟙 M)
def t : F.obj C := φ ⊗ₜ[ℤ] m

end
end CoefficientTensorHomInteger
```

Here `φ` is an element of the coefficient module and also a categorical map
`M ⟶ M`. Thus `φ.hom m : M`; `h.hom φ : M ⟶ M`;
`(u.hom φ).hom m : M`; and `f.hom t : M`. These are distinct uses of
`ModuleCat.Hom.hom` and `TopModuleCat.Hom.hom`, not a coercion to a topological
Hom object. All displayed scalar values below lie in the carrier `M = ℤ`.

The characteristic contracts are

```text
φ.hom m = (1 : ℤ)
(h.hom φ).hom m = (1 : ℤ)
f.hom t = (1 : ℤ)
(u.hom φ).hom m = (2 : ℤ)
v.hom m = (3 : ℤ)
```

In particular `φ,h,f,u,v,t` are nonzero: the indicated evaluations detect them
against zero. Also `m = 1` is nonzero. The inverse-equivalence constructor of `f`
uses `h`, not either naturality identity.

Evaluating the left signature at `φ : D` and `m : M` has the contracts

```text
((TopModuleCat.coefficientTensorHomEquiv ℤ M D M
    (F.map u ≫ f)).hom φ).hom m = (2 : ℤ)
((u ≫ TopModuleCat.coefficientTensorHomEquiv ℤ M C M f).hom φ).hom m
    = (2 : ℤ)
```

Evaluating the right signature at `φ : C` and `m : M` has the contracts

```text
((TopModuleCat.coefficientTensorHomEquiv ℤ M C N'
    (f ≫ v)).hom φ).hom m = (3 : ℤ)
((TopModuleCat.coefficientTensorHomEquiv ℤ M C N f ≫ G.map v).hom φ).hom m
    = (3 : ℤ)
```

These numerical contracts follow from the existing pure-tensor evaluation APIs,
identity and composition evaluations, and the stored linear actions: the inverse
equivalence evaluates a pure tensor by `h`; a coefficient change sends its first
factor through `u`; target composition applies `v`. They do not assume either
new whole-map identity.

## Existing interfaces

- [`CoefficientTensor.lean`](../AlgebraicDirectLimits/Topology/CoefficientTensor.lean):
  `coefficientTensor` (lines 63–111), `coefficientTensorHomEquiv` (114–130),
  `coefficientTensor_map_hom`, `coefficientTensor_map_tmul` (150–160),
  `coefficientTensorHomEquiv_apply`, `…_symm_apply` (178–198),
  `…_apply_apply`, and `…_symm_apply_tmul` (201–218).
  In the inverse evaluation API the arguments are `ℤ M h φ m`, with `C` and `M`
  inferred as coefficient and target; the forward evaluation uses `ℤ M f φ m`.
- [`TensorHom.lean`](../AlgebraicDirectLimits/Topology/TensorHom.lean):
  `tensorCurry_comp_tensorMapCLM` (285–299) and `tensorCurry_comp` (325–341)
  already express the underlying continuous-map composition identities.
  These, together with the existing categorical wrappers, are the reuse route;
  no new tensor universal property is needed.
- Mathlib's [`linearCoyoneda`](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/CategoryTheory/Linear/Yoneda.lean#L47-L57)
  uses `ModuleCat.of R (M ⟶ N)` and `Linear.rightComp` exactly as above.
  [`ModuleCat/Topology/Basic.lean`](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/Algebra/Category/ModuleCat/Topology/Basic.lean#L103-L114)
  supplies `TopModuleCat.hom_comp`, `hom_id`, and (line 175) `hom_smul`;
  the corresponding algebraic wrappers are `ModuleCat.hom_comp`, `hom_id`,
  and `hom_smul`.
- The constructor `TopModuleCat.of ℤ ℤ` with this topology is also the existing
  `TensorHomExamples.integerModule` in
  [`AlgebraicDirectLimitsExamples/TensorHom.lean`](../AlgebraicDirectLimitsExamples/TensorHom.lean#L60-L61).
