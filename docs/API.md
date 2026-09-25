# Generated API reference

This reference contains 73 native library display sites and 23 boundary-client sites.
Import `AlgebraicDirectLimits` for the library; the test-target modules are separate.
Private/generated proof declarations still require the separate complete audit.
Native display-site counts are not a complete kernel-declaration census.

Headers below are native doc-gen4 display signatures, not complete declarations
with proof bodies. All native visible tokens, including implicit parameters and
noncomputable/abbrev modifiers, are retained; whitespace alone is normalized.
Native pretty-printing uses each source namespace, notation and type inference;
consult the linked source for suppressed inferred types and universe conventions.
These displayed fragments are not promised to elaborate alone in a fresh namespace.
Source links are relative to this same checkout.

The source/pin hashes and generation provenance are in [api-manifest.json](api-manifest.json).
See [generation instructions](README.md) and the [mathematical guide](Guide.md).
Where no source docstring exists, a separately authored **API note** is labeled explicitly.

## AlgebraicDirectLimits.CofinalSequence

Scope: library.

### IsCofinal.exists_monotone_nat

```lean
theorem IsCofinal.exists_monotone_nat {J : Type u} [Preorder J] [IsDirectedOrder J] [Nonempty J] {s : Set J} (hs : IsCofinal s) (hsc : s.Countable) : ∃ (f : ℕ → J), Monotone f ∧ IsCofinal (Set.range f)
```

A nonempty directed preorder with a countable cofinal subset admits a
monotone cofinal sequence.

[Source](../AlgebraicDirectLimits/CofinalSequence.lean#L31) (native range begins at line 31).

### IsCofinal.exists_final_functor_nat

```lean
theorem IsCofinal.exists_final_functor_nat {J : Type u} [Preorder J] [IsDirectedOrder J] [Nonempty J] {s : Set J} (hs : IsCofinal s) (hsc : s.Countable) : ∃ (F : CategoryTheory.Functor ℕ J), F.Final
```

A nonempty directed preorder with a countable cofinal subset admits a
final functor from `ℕ`.

[Source](../AlgebraicDirectLimits/CofinalSequence.lean#L53) (native range begins at line 53).

## AlgebraicDirectLimits.CofinalGroupCompletion

Scope: library.

### Algebra.GrothendieckAddGroup.isLocalizationMap_of_saturation_eq_top

```lean
theorem Algebra.GrothendieckAddGroup.isLocalizationMap_of_saturation_eq_top {M : Type u} [AddCommMonoid M] (L : AddSubmonoid M) (hL : L.saturation = ⊤) : L.IsLocalizationMap ⇑of
```

If `L` is cofinal, the canonical group-completion map localizes `M` at `L`.

[Source](../AlgebraicDirectLimits/CofinalGroupCompletion.lean#L30) (native range begins at line 30).

### Algebra.GrothendieckAddGroup.exists_cofinal_denominator

```lean
theorem Algebra.GrothendieckAddGroup.exists_cofinal_denominator {M : Type u} [AddCommMonoid M] (L : AddSubmonoid M) (hL : L.saturation = ⊤) (z : GrothendieckAddGroup M) : ∃ (m : M) (l : ↥L), z = of m - of ↑l
```

Every element of the group completion has a numerator in `M` and a denominator in `L`.

[Source](../AlgebraicDirectLimits/CofinalGroupCompletion.lean#L56) (native range begins at line 56).

### Algebra.GrothendieckAddGroup.of_eq_iff_exists_cofinal_stabilizer

```lean
theorem Algebra.GrothendieckAddGroup.of_eq_iff_exists_cofinal_stabilizer {M : Type u} [AddCommMonoid M] (L : AddSubmonoid M) (hL : L.saturation = ⊤) (m n : M) : of m = of n ↔ ∃ (l : ↥L), m + ↑l = n + ↑l
```

Two canonical images agree exactly when their representatives stabilize by an element
of the cofinal submonoid.

[Source](../AlgebraicDirectLimits/CofinalGroupCompletion.lean#L62) (native range begins at line 62).

### Algebra.GrothendieckAddGroup.lift_subtype_injective

```lean
theorem Algebra.GrothendieckAddGroup.lift_subtype_injective {M : Type u} [AddCommMonoid M] (L : AddSubmonoid M) (hL : L.saturation = ⊤) : Function.Injective ⇑(lift (of.comp L.subtype))
```

The map on group completions induced by the actual inclusion `L ↪ M` is injective.

[Source](../AlgebraicDirectLimits/CofinalGroupCompletion.lean#L70) (native range begins at line 70).

## AlgebraicDirectLimits.GradedStabilization

Scope: library.

### Algebra.GrothendieckAddGroup.GradedStabilization.degreeFiber

```lean
def Algebra.GrothendieckAddGroup.GradedStabilization.degreeFiber {M : Type uM} [AddCommMonoid M] {A : Type uA} [AddCommMonoid A] (d : M →+ A) (u : M) (n : ℕ) : Type uM
```

A natural-indexed fiber of the degree map; it is not a stagewise group.

[Source](../AlgebraicDirectLimits/GradedStabilization.lean#L44) (native range begins at line 44).

### Algebra.GrothendieckAddGroup.GradedStabilization.transition

```lean
def Algebra.GrothendieckAddGroup.GradedStabilization.transition {M : Type uM} [AddCommMonoid M] {A : Type uA} [AddCommMonoid A] (d : M →+ A) (u : M) (n k : ℕ) (h : n ≤ k) : TypeCat.Fun (degreeFiber d u n) (degreeFiber d u k)
```

Stabilization by the missing natural number of copies of `u`.

[Source](../AlgebraicDirectLimits/GradedStabilization.lean#L47) (native range begins at line 47).

### Algebra.GrothendieckAddGroup.GradedStabilization.degreeDirectedSystem

```lean
instance Algebra.GrothendieckAddGroup.GradedStabilization.degreeDirectedSystem {M : Type uM} [AddCommMonoid M] {A : Type uA} [AddCommMonoid A] (d : M →+ A) (u : M) : DirectedSystem (degreeFiber d u) fun (x1 x2 : ℕ) (x3 : x1 ≤ x2) => ⇑(transition d u x1 x2 x3)
```

The degree fibers and stabilization maps form a native directed system.

[Source](../AlgebraicDirectLimits/GradedStabilization.lean#L55) (native range begins at line 55).

### Algebra.GrothendieckAddGroup.GradedStabilization.inducedDegree

```lean
noncomputable def Algebra.GrothendieckAddGroup.GradedStabilization.inducedDegree {M : Type uM} [AddCommMonoid M] {A : Type uA} [AddCommMonoid A] (d : M →+ A) : GrothendieckAddGroup M →+ GrothendieckAddGroup A
```

The native completion homomorphism induced by degree.

[Source](../AlgebraicDirectLimits/GradedStabilization.lean#L71) (native range begins at line 71).

### Algebra.GrothendieckAddGroup.GradedStabilization.inducedDegree_of

```lean
theorem Algebra.GrothendieckAddGroup.GradedStabilization.inducedDegree_of {M : Type uM} [AddCommMonoid M] {A : Type uA} [AddCommMonoid A] (d : M →+ A) (m : M) : (inducedDegree d) (of m) = of (d m)
```

The induced degree homomorphism sends a canonical image to its degree image.

[Source](../AlgebraicDirectLimits/GradedStabilization.lean#L76) (native range begins at line 76).

### Algebra.GrothendieckAddGroup.GradedStabilization.inducedDegree_addMonoidOf

```lean
theorem Algebra.GrothendieckAddGroup.GradedStabilization.inducedDegree_addMonoidOf {M : Type uM} [AddCommMonoid M] {A : Type uA} [AddCommMonoid A] (d : M →+ A) (m : M) : (inducedDegree d) ((AddLocalization.addMonoidOf ⊤) m) = (AddLocalization.addMonoidOf ⊤) (d m)
```

The induced degree computation in the native localization simp normal form.

[Source](../AlgebraicDirectLimits/GradedStabilization.lean#L83) (native range begins at line 83).

### Algebra.GrothendieckAddGroup.GradedStabilization.normalizedAt

```lean
noncomputable def Algebra.GrothendieckAddGroup.GradedStabilization.normalizedAt {M : Type uM} [AddCommMonoid M] {A : Type uA} [AddCommMonoid A] (d : M →+ A) (u : M) (n : ℕ) (m : degreeFiber d u n) : ↥(inducedDegree d).ker
```

A degree-fiber representative determines an element of the actual kernel.

[Source](../AlgebraicDirectLimits/GradedStabilization.lean#L89) (native range begins at line 89).

### Algebra.GrothendieckAddGroup.GradedStabilization.normalizedAt_transition

```lean
theorem Algebra.GrothendieckAddGroup.GradedStabilization.normalizedAt_transition {M : Type uM} [AddCommMonoid M] {A : Type uA} [AddCommMonoid A] (d : M →+ A) (u : M) (n k : ℕ) (h : n ≤ k) (m : degreeFiber d u n) : normalizedAt d u n m = normalizedAt d u k ((transition d u n k h) m)
```

Stabilization preserves the normalized element of the completion kernel.

[Source](../AlgebraicDirectLimits/GradedStabilization.lean#L97) (native range begins at line 97).

### Algebra.GrothendieckAddGroup.GradedStabilization.normalization

```lean
noncomputable def Algebra.GrothendieckAddGroup.GradedStabilization.normalization {M : Type uM} [AddCommMonoid M] {A : Type uA} [AddCommMonoid A] (d : M →+ A) (u : M) : DirectLimit (degreeFiber d u) (transition d u) → ↥(inducedDegree d).ker
```

The descended normalized map, using the native set-valued direct limit.

[Source](../AlgebraicDirectLimits/GradedStabilization.lean#L111) (native range begins at line 111).

### Algebra.GrothendieckAddGroup.GradedStabilization.normalization_mk

```lean
theorem Algebra.GrothendieckAddGroup.GradedStabilization.normalization_mk {M : Type uM} [AddCommMonoid M] {A : Type uA} [AddCommMonoid A] (d : M →+ A) (u : M) (n : ℕ) (m : degreeFiber d u n) : ↑(normalization d u ⟦⟨n, m⟩⟧) = of ↑m - n • of u
```

Normalization on a direct-limit representative is the specified difference.

[Source](../AlgebraicDirectLimits/GradedStabilization.lean#L117) (native range begins at line 117).

### Algebra.GrothendieckAddGroup.GradedStabilization.exists_normalized_representative

```lean
theorem Algebra.GrothendieckAddGroup.GradedStabilization.exists_normalized_representative {M : Type uM} [AddCommMonoid M] (u : M) (hu : (AddSubmonoid.multiples u).saturation = ⊤) (z : GrothendieckAddGroup M) : ∃ (m : M) (n : ℕ), z = of m - n • of u
```

A cofinal cyclic submonoid supplies all normalized group representatives.

[Source](../AlgebraicDirectLimits/GradedStabilization.lean#L122) (native range begins at line 122).

### Algebra.GrothendieckAddGroup.GradedStabilization.of_eq_iff_cyclic_stabilizer

```lean
theorem Algebra.GrothendieckAddGroup.GradedStabilization.of_eq_iff_cyclic_stabilizer {M : Type uM} [AddCommMonoid M] (u : M) (hu : (AddSubmonoid.multiples u).saturation = ⊤) (x y : M) : of x = of y ↔ ∃ (ell : ℕ), x + ell • u = y + ell • u
```

Equality of canonical images is stabilization by copies of the same `u`.

[Source](../AlgebraicDirectLimits/GradedStabilization.lean#L131) (native range begins at line 131).

### Algebra.GrothendieckAddGroup.GradedStabilization.normalized_eq_iff

```lean
theorem Algebra.GrothendieckAddGroup.GradedStabilization.normalized_eq_iff {M : Type uM} [AddCommMonoid M] (u : M) (hu : (AddSubmonoid.multiples u).saturation = ⊤) (n n' : ℕ) (m m' : M) : of m - n • of u = of m' - n' • of u ↔ ∃ (ell : ℕ), m + (n' + ell) • u = m' + (n + ell) • u
```

Normalized equality is precisely equality after one common cyclic stabilization.

[Source](../AlgebraicDirectLimits/GradedStabilization.lean#L145) (native range begins at line 145).

### Algebra.GrothendieckAddGroup.GradedStabilization.normalization_injective

```lean
theorem Algebra.GrothendieckAddGroup.GradedStabilization.normalization_injective {M : Type uM} [AddCommMonoid M] {A : Type uA} [AddCommMonoid A] (d : M →+ A) (u : M) (hu : (AddSubmonoid.multiples u).saturation = ⊤) : Function.Injective (normalization d u)
```

Injectivity comes from eventual equality, not injective stage maps.

[Source](../AlgebraicDirectLimits/GradedStabilization.lean#L157) (native range begins at line 157).

### Algebra.GrothendieckAddGroup.GradedStabilization.mk_eq_iff

```lean
theorem Algebra.GrothendieckAddGroup.GradedStabilization.mk_eq_iff {M : Type uM} [AddCommMonoid M] {A : Type uA} [AddCommMonoid A] (d : M →+ A) (u : M) (hu : (AddSubmonoid.multiples u).saturation = ⊤) (n n' : ℕ) (m : degreeFiber d u n) (m' : degreeFiber d u n') : ⟦⟨n, m⟩⟧ = ⟦⟨n', m'⟩⟧ ↔ ∃ (ell : ℕ), ↑m + (n' + ell) • u = ↑m' + (n + ell) • u
```

The actual direct-limit equality relation is cyclic eventual equality.

[Source](../AlgebraicDirectLimits/GradedStabilization.lean#L174) (native range begins at line 174).

### Algebra.GrothendieckAddGroup.GradedStabilization.mk_same_stage_eq_iff

```lean
theorem Algebra.GrothendieckAddGroup.GradedStabilization.mk_same_stage_eq_iff {M : Type uM} [AddCommMonoid M] {A : Type uA} [AddCommMonoid A] (d : M →+ A) (u : M) (hu : (AddSubmonoid.multiples u).saturation = ⊤) (n : ℕ) (m m' : degreeFiber d u n) : ⟦⟨n, m⟩⟧ = ⟦⟨n, m'⟩⟧ ↔ ∃ (ell : ℕ), ↑m + ell • u = ↑m' + ell • u
```

Same-stage representatives need only become equal after stabilization.

[Source](../AlgebraicDirectLimits/GradedStabilization.lean#L183) (native range begins at line 183).

### Algebra.GrothendieckAddGroup.GradedStabilization.normalization_surjective

```lean
theorem Algebra.GrothendieckAddGroup.GradedStabilization.normalization_surjective {M : Type uM} [AddCommMonoid M] {A : Type uA} [AddCommMonoid A] [IsCancelAdd A] (d : M →+ A) (u : M) (hu : (AddSubmonoid.multiples u).saturation = ⊤) : Function.Surjective (normalization d u)
```

Target cancellation recovers the exact degree-fiber condition.

[Source](../AlgebraicDirectLimits/GradedStabilization.lean#L194) (native range begins at line 194).

### Algebra.GrothendieckAddGroup.GradedStabilization.normalizationEquiv

```lean
noncomputable def Algebra.GrothendieckAddGroup.GradedStabilization.normalizationEquiv {M : Type uM} [AddCommMonoid M] {A : Type uA} [AddCommMonoid A] [IsCancelAdd A] (d : M →+ A) (u : M) (hu : (AddSubmonoid.multiples u).saturation = ⊤) : DirectLimit (degreeFiber d u) (transition d u) ≃ ↥(inducedDegree d).ker
```

The native direct limit is equivalent to the native completion kernel.

[Source](../AlgebraicDirectLimits/GradedStabilization.lean#L209) (native range begins at line 209).

### Algebra.GrothendieckAddGroup.GradedStabilization.normalizationEquiv_mk

```lean
theorem Algebra.GrothendieckAddGroup.GradedStabilization.normalizationEquiv_mk {M : Type uM} [AddCommMonoid M] {A : Type uA} [AddCommMonoid A] [IsCancelAdd A] (d : M →+ A) (u : M) (hu : (AddSubmonoid.multiples u).saturation = ⊤) (n : ℕ) (m : degreeFiber d u n) : ↑((normalizationEquiv d u hu) ⟦⟨n, m⟩⟧) = of ↑m - n • of u
```

The equivalence retains the explicit normalization formula on representatives.

[Source](../AlgebraicDirectLimits/GradedStabilization.lean#L216) (native range begins at line 216).

### Algebra.GrothendieckAddGroup.GradedStabilization.normalizationEquiv_symm_eq_mk

```lean
theorem Algebra.GrothendieckAddGroup.GradedStabilization.normalizationEquiv_symm_eq_mk {M : Type uM} [AddCommMonoid M] {A : Type uA} [AddCommMonoid A] [IsCancelAdd A] (d : M →+ A) (u : M) (hu : (AddSubmonoid.multiples u).saturation = ⊤) (z : ↥(inducedDegree d).ker) (n : ℕ) (m : degreeFiber d u n) (hz : ↑z = of ↑m - n • of u) : (normalizationEquiv d u hu).symm z = ⟦⟨n, m⟩⟧
```

The choice-defined inverse returns every specified valid representative.

[Source](../AlgebraicDirectLimits/GradedStabilization.lean#L222) (native range begins at line 222).

## AlgebraicDirectLimits.LocalizationPi

Scope: library.

### Localization.awayPiComparison

```lean
noncomputable def Localization.awayPiComparison {R : Type u_1} [CommRing R] (r : R) : (Away fun (x : ℕ) => r) →+* ℕ → Away r
```

The canonical map from localization of a countable product at the constant tuple `r` to the
product of the localizations away from `r`.

[Source](../AlgebraicDirectLimits/LocalizationPi.lean#L24) (native range begins at line 24).

### Localization.awayPiComparison_algebraMap

```lean
theorem Localization.awayPiComparison_algebraMap {R : Type u_1} [CommRing R] (r : R) (a : ℕ → R) : (awayPiComparison r) ((algebraMap (ℕ → R) (Away fun (x : ℕ) => r)) a) = fun (i : ℕ) => (algebraMap R (Away r)) (a i)
```

The comparison map agrees coordinatewise with the localization maps on the original
countable product.

[Source](../AlgebraicDirectLimits/LocalizationPi.lean#L38) (native range begins at line 38).

### Localization.awayPiComparison_not_surjective

```lean
theorem Localization.awayPiComparison_not_surjective {R : Type u_1} [CommRing R] [IsDomain R] (r : R) (hr : r ≠ 0) (hr_unit : ¬IsUnit r) : ¬Function.Surjective ⇑(awayPiComparison r)
```

If `r` is nonzero and not a unit in a commutative domain, localization of a countable
product at the constant tuple `r` does not surject onto the product of the localizations away
from `r`.

[Source](../AlgebraicDirectLimits/LocalizationPi.lean#L47) (native range begins at line 47).

## AlgebraicDirectLimits.MittagLeffler

Scope: library.

### CategoryTheory.Functor.IsMittagLeffler.comp_monotone_cofinal

```lean
theorem CategoryTheory.Functor.IsMittagLeffler.comp_monotone_cofinal {I : Type u} {J : Type v} [Preorder I] [Preorder J] [IsDirectedOrder I] (F : Functor Jᵒᵖ (Type w)) (hF : F.IsMittagLeffler) {f : I → J} (hf : Monotone f) (hfc : IsCofinal (Set.range f)) : (hf.functor.op.comp F).IsMittagLeffler
```

Restriction along a monotone cofinal map preserves the Mittag--Leffler
condition for inverse systems indexed by directed preorders. The source preorder
need not be nonempty.

[Source](../AlgebraicDirectLimits/MittagLeffler.lean#L31) (native range begins at line 31).

### CategoryTheory.Functor.nonempty_sections_of_surjective_inverse_sequence

```lean
theorem CategoryTheory.Functor.nonempty_sections_of_surjective_inverse_sequence (F : Functor ℕᵒᵖ (Type u)) [∀ (n : ℕᵒᵖ), Nonempty (F.obj n)] (hF : ∀ (n : ℕ), Function.Surjective ⇑(ConcreteCategory.hom (F.map (homOfLE ⋯).op))) : F.sections.Nonempty
```

A surjective inverse sequence of nonempty types has a compatible section.

[Source](../AlgebraicDirectLimits/MittagLeffler.lean#L52) (native range begins at line 52).

### CategoryTheory.Functor.IsMittagLeffler.nonempty_sections_of_countable_cofinal

```lean
theorem CategoryTheory.Functor.IsMittagLeffler.nonempty_sections_of_countable_cofinal {J : Type v} [Preorder J] [IsDirectedOrder J] [Nonempty J] (F : Functor Jᵒᵖ (Type w)) (hF : F.IsMittagLeffler) [∀ (j : Jᵒᵖ), Nonempty (F.obj j)] {s : Set J} (hs : IsCofinal s) (hsc : s.Countable) : F.sections.Nonempty
```

A pointwise nonempty Mittag--Leffler inverse system of types over a
nonempty directed preorder with a countable cofinal subset has a compatible
section.

[Source](../AlgebraicDirectLimits/MittagLeffler.lean#L63) (native range begins at line 63).

### CategoryTheory.Functor.evalSectionToEventualRange

```lean
def CategoryTheory.Functor.evalSectionToEventualRange {J : Type v} [Preorder J] (F : Functor Jᵒᵖ (Type w)) (i : Jᵒᵖ) : ↑F.sections → ↑(F.eventualRange i)
```

Evaluation of a compatible section lands in the eventual range.

[Source](../AlgebraicDirectLimits/MittagLeffler.lean#L89) (native range begins at line 89).

### CategoryTheory.Functor.IsMittagLeffler.surjective_evalSectionToEventualRange

```lean
theorem CategoryTheory.Functor.IsMittagLeffler.surjective_evalSectionToEventualRange {J : Type v} [Preorder J] [IsDirectedOrder J] [Nonempty J] (F : Functor Jᵒᵖ (Type w)) (hF : F.IsMittagLeffler) {s : Set J} (hs : IsCofinal s) (hsc : s.Countable) (i : Jᵒᵖ) : Function.Surjective (F.evalSectionToEventualRange i)
```

For a Mittag--Leffler inverse system indexed by a nonempty directed
preorder with a countable cofinal subset, evaluation maps compatible sections
surjectively onto the eventual ranges.

[Source](../AlgebraicDirectLimits/MittagLeffler.lean#L94) (native range begins at line 94).

## AlgebraicDirectLimits.SimpleRing

Scope: library.

### RingCat.FilteredColimits.colimit_isSimpleRing

```lean
theorem RingCat.FilteredColimits.colimit_isSimpleRing {J : Type v} [CategoryTheory.SmallCategory J] [CategoryTheory.IsFiltered J] (F : CategoryTheory.Functor J RingCat) (hF : ∀ (j : J), IsSimpleRing ↑(F.obj j)) : IsSimpleRing ↑(colimit F)
```

A filtered colimit of simple rings is simple.

[Source](../AlgebraicDirectLimits/SimpleRing.lean#L46) (native range begins at line 46).

## AlgebraicDirectLimits.VaryingScalar

Scope: library.

### DirectLimit.VaryingScalar.ScalarLimit

```lean
abbrev DirectLimit.VaryingScalar.ScalarLimit {ι : Type u} [Preorder ι] [IsDirectedOrder ι] (A : ι → Type v) [(i : ι) → CommSemiring (A i)] (f : (i j : ι) → i ≤ j → A i →+* A j) [DirectedSystem A fun (x1 x2 : ι) (x3 : x1 ≤ x2) => ⇑(f x1 x2 x3)] : Type (max v u)
```

The concrete directed limit of the varying scalar semirings.

[Source](../AlgebraicDirectLimits/VaryingScalar.lean#L37) (native range begins at line 37).

### DirectLimit.VaryingScalar.smulDef

```lean
noncomputable def DirectLimit.VaryingScalar.smulDef {ι : Type u} [Preorder ι] [IsDirectedOrder ι] (A : ι → Type v) [(i : ι) → CommSemiring (A i)] (f : (i j : ι) → i ≤ j → A i →+* A j) [DirectedSystem A fun (x1 x2 : ι) (x3 : x1 ≤ x2) => ⇑(f x1 x2 x3)] (M : ι → Type w) [(i : ι) → AddCommMonoid (M i)] [(i : ι) → Module (A i) (M i)] (g : (i j : ι) → (h : i ≤ j) → M i →ₛₗ[f i j h] M j) [DirectedSystem M fun (x1 x2 : ι) (x3 : x1 ≤ x2) => ⇑(g x1 x2 x3)] : ScalarLimit A f → (DirectLimit M fun (i j : ι) (h : i ≤ j) => g i j h) → DirectLimit M fun (i j : ι) (h : i ≤ j) => g i j h
```

The representative-level action of the scalar-semiring limit on the module limit.

[Source](../AlgebraicDirectLimits/VaryingScalar.lean#L40) (native range begins at line 40).

### DirectLimit.VaryingScalar.smulDef_mk

```lean
theorem DirectLimit.VaryingScalar.smulDef_mk {ι : Type u} [Preorder ι] [IsDirectedOrder ι] (A : ι → Type v) [(i : ι) → CommSemiring (A i)] (f : (i j : ι) → i ≤ j → A i →+* A j) [DirectedSystem A fun (x1 x2 : ι) (x3 : x1 ≤ x2) => ⇑(f x1 x2 x3)] (M : ι → Type w) [(i : ι) → AddCommMonoid (M i)] [(i : ι) → Module (A i) (M i)] (g : (i j : ι) → (h : i ≤ j) → M i →ₛₗ[f i j h] M j) [DirectedSystem M fun (x1 x2 : ι) (x3 : x1 ≤ x2) => ⇑(g x1 x2 x3)] (i : ι) (a : A i) (m : M i) : smulDef A f M g ⟦⟨i, a⟩⟧ ⟦⟨i, m⟩⟧ = ⟦⟨i, a • m⟩⟧
```

**API note (not a source docstring):** On representatives at the same stage, the scalar action is the stagewise module action. This computation itself does not require a separate nonempty-index assumption.

[Source](../AlgebraicDirectLimits/VaryingScalar.lean#L49) (native range begins at line 49).

### DirectLimit.VaryingScalar.instModule

```lean
noncomputable instance DirectLimit.VaryingScalar.instModule {ι : Type u} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι] (A : ι → Type v) [(i : ι) → CommSemiring (A i)] (f : (i j : ι) → i ≤ j → A i →+* A j) [DirectedSystem A fun (x1 x2 : ι) (x3 : x1 ≤ x2) => ⇑(f x1 x2 x3)] (M : ι → Type w) [(i : ι) → AddCommMonoid (M i)] [(i : ι) → Module (A i) (M i)] (g : (i j : ι) → (h : i ≤ j) → M i →ₛₗ[f i j h] M j) [DirectedSystem M fun (x1 x2 : ι) (x3 : x1 ≤ x2) => ⇑(g x1 x2 x3)] : Module (ScalarLimit A f) (DirectLimit M fun (i j : ι) (h : i ≤ j) => g i j h)
```

**API note (not a source docstring):** The module direct limit is a module over the direct limit of the scalar semirings. Its action is smulDef; the representative law below specifies the action without assuming injective transition maps.

[Source](../AlgebraicDirectLimits/VaryingScalar.lean#L55) (native range begins at line 55).

### DirectLimit.VaryingScalar.smul_mk

```lean
theorem DirectLimit.VaryingScalar.smul_mk {ι : Type u} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι] (A : ι → Type v) [(i : ι) → CommSemiring (A i)] (f : (i j : ι) → i ≤ j → A i →+* A j) [DirectedSystem A fun (x1 x2 : ι) (x3 : x1 ≤ x2) => ⇑(f x1 x2 x3)] (M : ι → Type w) [(i : ι) → AddCommMonoid (M i)] [(i : ι) → Module (A i) (M i)] (g : (i j : ι) → (h : i ≤ j) → M i →ₛₗ[f i j h] M j) [DirectedSystem M fun (x1 x2 : ι) (x3 : x1 ≤ x2) => ⇑(g x1 x2 x3)] (i : ι) (a : A i) (m : M i) : ⟦⟨i, a⟩⟧ • ⟦⟨i, m⟩⟧ = ⟦⟨i, a • m⟩⟧
```

**API note (not a source docstring):** The installed module action sends same-stage scalar and module representatives to the representative of their stagewise product.

[Source](../AlgebraicDirectLimits/VaryingScalar.lean#L110) (native range begins at line 110).

### DirectLimit.VaryingScalar.of

```lean
def DirectLimit.VaryingScalar.of {ι : Type u} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι] (A : ι → Type v) [(i : ι) → CommSemiring (A i)] (f : (i j : ι) → i ≤ j → A i →+* A j) [DirectedSystem A fun (x1 x2 : ι) (x3 : x1 ≤ x2) => ⇑(f x1 x2 x3)] (M : ι → Type w) [(i : ι) → AddCommMonoid (M i)] [(i : ι) → Module (A i) (M i)] (g : (i j : ι) → (h : i ≤ j) → M i →ₛₗ[f i j h] M j) [DirectedSystem M fun (x1 x2 : ι) (x3 : x1 ≤ x2) => ⇑(g x1 x2 x3)] (i : ι) : M i →ₛₗ[Ring.of A (fun (x1 x2 : ι) (x3 : x1 ≤ x2) => f x1 x2 x3) i] DirectLimit M fun (i j : ι) (h : i ≤ j) => g i j h
```

The canonical semilinear map from a stage module to its varying-scalar limit.

[Source](../AlgebraicDirectLimits/VaryingScalar.lean#L117) (native range begins at line 117).

### DirectLimit.VaryingScalar.of_apply

```lean
theorem DirectLimit.VaryingScalar.of_apply {ι : Type u} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι] (A : ι → Type v) [(i : ι) → CommSemiring (A i)] (f : (i j : ι) → i ≤ j → A i →+* A j) [DirectedSystem A fun (x1 x2 : ι) (x3 : x1 ≤ x2) => ⇑(f x1 x2 x3)] (M : ι → Type w) [(i : ι) → AddCommMonoid (M i)] [(i : ι) → Module (A i) (M i)] (g : (i j : ι) → (h : i ≤ j) → M i →ₛₗ[f i j h] M j) [DirectedSystem M fun (x1 x2 : ι) (x3 : x1 ≤ x2) => ⇑(g x1 x2 x3)] (i : ι) (m : M i) : (of A f M g i) m = ⟦⟨i, m⟩⟧
```

**API note (not a source docstring):** The bundled semilinear stage map is the canonical quotient representative. This is the simplifier's representative normal form.

[Source](../AlgebraicDirectLimits/VaryingScalar.lean#L124) (native range begins at line 124).

### DirectLimit.VaryingScalar.of_map

```lean
theorem DirectLimit.VaryingScalar.of_map {ι : Type u} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι] (A : ι → Type v) [(i : ι) → CommSemiring (A i)] (f : (i j : ι) → i ≤ j → A i →+* A j) [DirectedSystem A fun (x1 x2 : ι) (x3 : x1 ≤ x2) => ⇑(f x1 x2 x3)] (M : ι → Type w) [(i : ι) → AddCommMonoid (M i)] [(i : ι) → Module (A i) (M i)] (g : (i j : ι) → (h : i ≤ j) → M i →ₛₗ[f i j h] M j) [DirectedSystem M fun (x1 x2 : ι) (x3 : x1 ≤ x2) => ⇑(g x1 x2 x3)] {i j : ι} (hij : i ≤ j) (m : M i) : (of A f M g j) ((g i j hij) m) = (of A f M g i) m
```

**API note (not a source docstring):** Moving a module element along a transition before taking its canonical stage image does not change the resulting direct-limit element.

[Source](../AlgebraicDirectLimits/VaryingScalar.lean#L127) (native range begins at line 127).

### DirectLimit.VaryingScalar.tensorMap

```lean
def DirectLimit.VaryingScalar.tensorMap {ι : Type u} [Preorder ι] (A : ι → Type v) [(i : ι) → CommSemiring (A i)] (f : (i j : ι) → i ≤ j → A i →+* A j) (M : ι → Type w) [(i : ι) → AddCommMonoid (M i)] [(i : ι) → Module (A i) (M i)] (g : (i j : ι) → (h : i ≤ j) → M i →ₛₗ[f i j h] M j) (N : ι → Type x) [(i : ι) → AddCommMonoid (N i)] [(i : ι) → Module (A i) (N i)] (h : (i j : ι) → (hij : i ≤ j) → N i →ₛₗ[f i j hij] N j) (i j : ι) (hij : i ≤ j) : TensorProduct (A i) (M i) (N i) →ₛₗ[f i j hij] TensorProduct (A j) (M j) (N j)
```

The transition map on tensor products induced by two semilinear systems.

[Source](../AlgebraicDirectLimits/VaryingScalar.lean#L137) (native range begins at line 137).

### DirectLimit.VaryingScalar.instDirectedSystemTensorProduct

```lean
instance DirectLimit.VaryingScalar.instDirectedSystemTensorProduct {ι : Type u} [Preorder ι] (A : ι → Type v) [(i : ι) → CommSemiring (A i)] (f : (i j : ι) → i ≤ j → A i →+* A j) (M : ι → Type w) [(i : ι) → AddCommMonoid (M i)] [(i : ι) → Module (A i) (M i)] (g : (i j : ι) → (h : i ≤ j) → M i →ₛₗ[f i j h] M j) [DirectedSystem M fun (x1 x2 : ι) (x3 : x1 ≤ x2) => ⇑(g x1 x2 x3)] (N : ι → Type x) [(i : ι) → AddCommMonoid (N i)] [(i : ι) → Module (A i) (N i)] (h : (i j : ι) → (hij : i ≤ j) → N i →ₛₗ[f i j hij] N j) [DirectedSystem N fun (x1 x2 : ι) (x3 : x1 ≤ x2) => ⇑(h x1 x2 x3)] : DirectedSystem (fun (i : ι) => TensorProduct (A i) (M i) (N i)) fun (x1 x2 : ι) (x3 : x1 ≤ x2) => ⇑(tensorMap A f M g N h x1 x2 x3)
```

**API note (not a source docstring):** The semilinear maps induced on the stagewise tensor products form a directed system. The displayed statement only needs a preorder and the two module-system laws, not directedness or a nonempty-index instance.

[Source](../AlgebraicDirectLimits/VaryingScalar.lean#L143) (native range begins at line 143).

### DirectLimit.VaryingScalar.tensorOf

```lean
def DirectLimit.VaryingScalar.tensorOf {ι : Type u} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι] (A : ι → Type v) [(i : ι) → CommSemiring (A i)] (f : (i j : ι) → i ≤ j → A i →+* A j) (M : ι → Type w) [(i : ι) → AddCommMonoid (M i)] [(i : ι) → Module (A i) (M i)] (g : (i j : ι) → (h : i ≤ j) → M i →ₛₗ[f i j h] M j) [DirectedSystem M fun (x1 x2 : ι) (x3 : x1 ≤ x2) => ⇑(g x1 x2 x3)] (N : ι → Type x) [(i : ι) → AddCommMonoid (N i)] [(i : ι) → Module (A i) (N i)] (h : (i j : ι) → (hij : i ≤ j) → N i →ₛₗ[f i j hij] N j) [DirectedSystem N fun (x1 x2 : ι) (x3 : x1 ≤ x2) => ⇑(h x1 x2 x3)] (i : ι) : TensorProduct (A i) (M i) (N i) →+ DirectLimit (fun (i : ι) => TensorProduct (A i) (M i) (N i)) fun (x1 x2 : ι) (x3 : x1 ≤ x2) => tensorMap A f M g N h x1 x2 x3
```

The canonical additive map from a stage tensor product to its direct limit.

[Source](../AlgebraicDirectLimits/VaryingScalar.lean#L155) (native range begins at line 155).

### DirectLimit.VaryingScalar.tensorOf_apply

```lean
theorem DirectLimit.VaryingScalar.tensorOf_apply {ι : Type u} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι] (A : ι → Type v) [(i : ι) → CommSemiring (A i)] (f : (i j : ι) → i ≤ j → A i →+* A j) (M : ι → Type w) [(i : ι) → AddCommMonoid (M i)] [(i : ι) → Module (A i) (M i)] (g : (i j : ι) → (h : i ≤ j) → M i →ₛₗ[f i j h] M j) [DirectedSystem M fun (x1 x2 : ι) (x3 : x1 ≤ x2) => ⇑(g x1 x2 x3)] (N : ι → Type x) [(i : ι) → AddCommMonoid (N i)] [(i : ι) → Module (A i) (N i)] (h : (i j : ι) → (hij : i ≤ j) → N i →ₛₗ[f i j hij] N j) [DirectedSystem N fun (x1 x2 : ι) (x3 : x1 ≤ x2) => ⇑(h x1 x2 x3)] (i : ι) (x : TensorProduct (A i) (M i) (N i)) : (tensorOf A f M g N h i) x = ⟦⟨i, x⟩⟧
```

**API note (not a source docstring):** The canonical additive map from a stage tensor product sends a tensor element to its quotient representative.

[Source](../AlgebraicDirectLimits/VaryingScalar.lean#L164) (native range begins at line 164).

### DirectLimit.VaryingScalar.tensorOf_map

```lean
theorem DirectLimit.VaryingScalar.tensorOf_map {ι : Type u} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι] (A : ι → Type v) [(i : ι) → CommSemiring (A i)] (f : (i j : ι) → i ≤ j → A i →+* A j) (M : ι → Type w) [(i : ι) → AddCommMonoid (M i)] [(i : ι) → Module (A i) (M i)] (g : (i j : ι) → (h : i ≤ j) → M i →ₛₗ[f i j h] M j) [DirectedSystem M fun (x1 x2 : ι) (x3 : x1 ≤ x2) => ⇑(g x1 x2 x3)] (N : ι → Type x) [(i : ι) → AddCommMonoid (N i)] [(i : ι) → Module (A i) (N i)] (h : (i j : ι) → (hij : i ≤ j) → N i →ₛₗ[f i j hij] N j) [DirectedSystem N fun (x1 x2 : ι) (x3 : x1 ≤ x2) => ⇑(h x1 x2 x3)] {i j : ι} (hij : i ≤ j) (x : TensorProduct (A i) (M i) (N i)) : (tensorOf A f M g N h j) ((tensorMap A f M g N h i j hij) x) = (tensorOf A f M g N h i) x
```

**API note (not a source docstring):** The canonical stage tensor maps are compatible with tensorMap, so taking an image after a transition gives the same direct-limit element.

[Source](../AlgebraicDirectLimits/VaryingScalar.lean#L168) (native range begins at line 168).

### DirectLimit.VaryingScalar.pairing

```lean
noncomputable def DirectLimit.VaryingScalar.pairing {ι : Type u} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι] (A : ι → Type v) [(i : ι) → CommSemiring (A i)] (f : (i j : ι) → i ≤ j → A i →+* A j) (M : ι → Type w) [(i : ι) → AddCommMonoid (M i)] [(i : ι) → Module (A i) (M i)] (g : (i j : ι) → (h : i ≤ j) → M i →ₛₗ[f i j h] M j) [DirectedSystem M fun (x1 x2 : ι) (x3 : x1 ≤ x2) => ⇑(g x1 x2 x3)] (N : ι → Type x) [(i : ι) → AddCommMonoid (N i)] [(i : ι) → Module (A i) (N i)] (h : (i j : ι) → (hij : i ≤ j) → N i →ₛₗ[f i j hij] N j) [DirectedSystem N fun (x1 x2 : ι) (x3 : x1 ≤ x2) => ⇑(h x1 x2 x3)] : (DirectLimit M fun (i j : ι) (hij : i ≤ j) => g i j hij) → (DirectLimit N fun (i j : ι) (hij : i ≤ j) => h i j hij) → DirectLimit (fun (i : ι) => TensorProduct (A i) (M i) (N i)) fun (x1 x2 : ι) (x3 : x1 ≤ x2) => tensorMap A f M g N h x1 x2 x3
```

Pair two module-limit representatives in the direct limit of stage tensor products.

[Source](../AlgebraicDirectLimits/VaryingScalar.lean#L180) (native range begins at line 180).

### DirectLimit.VaryingScalar.pairing_mk

```lean
theorem DirectLimit.VaryingScalar.pairing_mk {ι : Type u} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι] (A : ι → Type v) [(i : ι) → CommSemiring (A i)] (f : (i j : ι) → i ≤ j → A i →+* A j) (M : ι → Type w) [(i : ι) → AddCommMonoid (M i)] [(i : ι) → Module (A i) (M i)] (g : (i j : ι) → (h : i ≤ j) → M i →ₛₗ[f i j h] M j) [DirectedSystem M fun (x1 x2 : ι) (x3 : x1 ≤ x2) => ⇑(g x1 x2 x3)] (N : ι → Type x) [(i : ι) → AddCommMonoid (N i)] [(i : ι) → Module (A i) (N i)] (h : (i j : ι) → (hij : i ≤ j) → N i →ₛₗ[f i j hij] N j) [DirectedSystem N fun (x1 x2 : ι) (x3 : x1 ≤ x2) => ⇑(h x1 x2 x3)] (i : ι) (m : M i) (n : N i) : pairing A f M g N h ⟦⟨i, m⟩⟧ ⟦⟨i, n⟩⟧ = (tensorOf A f M g N h i) (m ⊗ₜ[A i] n)
```

**API note (not a source docstring):** On two representatives from one stage, the limit pairing is the canonical image of their stagewise pure tensor.

[Source](../AlgebraicDirectLimits/VaryingScalar.lean#L192) (native range begins at line 192).

### DirectLimit.VaryingScalar.pairing_add_left

```lean
theorem DirectLimit.VaryingScalar.pairing_add_left {ι : Type u} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι] (A : ι → Type v) [(i : ι) → CommSemiring (A i)] (f : (i j : ι) → i ≤ j → A i →+* A j) (M : ι → Type w) [(i : ι) → AddCommMonoid (M i)] [(i : ι) → Module (A i) (M i)] (g : (i j : ι) → (h : i ≤ j) → M i →ₛₗ[f i j h] M j) [DirectedSystem M fun (x1 x2 : ι) (x3 : x1 ≤ x2) => ⇑(g x1 x2 x3)] (N : ι → Type x) [(i : ι) → AddCommMonoid (N i)] [(i : ι) → Module (A i) (N i)] (h : (i j : ι) → (hij : i ≤ j) → N i →ₛₗ[f i j hij] N j) [DirectedSystem N fun (x1 x2 : ι) (x3 : x1 ≤ x2) => ⇑(h x1 x2 x3)] (m₁ m₂ : DirectLimit M fun (i j : ι) (hij : i ≤ j) => g i j hij) (n : DirectLimit N fun (i j : ι) (hij : i ≤ j) => h i j hij) : pairing A f M g N h (m₁ + m₂) n = pairing A f M g N h m₁ n + pairing A f M g N h m₂ n
```

**API note (not a source docstring):** The representative-induced pairing preserves addition in its left argument. The displayed hypotheses are those needed for this computation, rather than all hypotheses of the final tensor equivalence.

[Source](../AlgebraicDirectLimits/VaryingScalar.lean#L198) (native range begins at line 198).

### DirectLimit.VaryingScalar.pairing_add_right

```lean
theorem DirectLimit.VaryingScalar.pairing_add_right {ι : Type u} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι] (A : ι → Type v) [(i : ι) → CommSemiring (A i)] (f : (i j : ι) → i ≤ j → A i →+* A j) (M : ι → Type w) [(i : ι) → AddCommMonoid (M i)] [(i : ι) → Module (A i) (M i)] (g : (i j : ι) → (h : i ≤ j) → M i →ₛₗ[f i j h] M j) [DirectedSystem M fun (x1 x2 : ι) (x3 : x1 ≤ x2) => ⇑(g x1 x2 x3)] (N : ι → Type x) [(i : ι) → AddCommMonoid (N i)] [(i : ι) → Module (A i) (N i)] (h : (i j : ι) → (hij : i ≤ j) → N i →ₛₗ[f i j hij] N j) [DirectedSystem N fun (x1 x2 : ι) (x3 : x1 ≤ x2) => ⇑(h x1 x2 x3)] (m : DirectLimit M fun (i j : ι) (hij : i ≤ j) => g i j hij) (n₁ n₂ : DirectLimit N fun (i j : ι) (hij : i ≤ j) => h i j hij) : pairing A f M g N h m (n₁ + n₂) = pairing A f M g N h m n₁ + pairing A f M g N h m n₂
```

**API note (not a source docstring):** The pairing preserves addition in its right argument under the displayed directed module-system assumptions.

[Source](../AlgebraicDirectLimits/VaryingScalar.lean#L215) (native range begins at line 215).

### DirectLimit.VaryingScalar.pairing_smul_left

```lean
theorem DirectLimit.VaryingScalar.pairing_smul_left {ι : Type u} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι] (A : ι → Type v) [(i : ι) → CommSemiring (A i)] (f : (i j : ι) → i ≤ j → A i →+* A j) [DirectedSystem A fun (x1 x2 : ι) (x3 : x1 ≤ x2) => ⇑(f x1 x2 x3)] (M : ι → Type w) [(i : ι) → AddCommMonoid (M i)] [(i : ι) → Module (A i) (M i)] (g : (i j : ι) → (h : i ≤ j) → M i →ₛₗ[f i j h] M j) [DirectedSystem M fun (x1 x2 : ι) (x3 : x1 ≤ x2) => ⇑(g x1 x2 x3)] (N : ι → Type x) [(i : ι) → AddCommMonoid (N i)] [(i : ι) → Module (A i) (N i)] (h : (i j : ι) → (hij : i ≤ j) → N i →ₛₗ[f i j hij] N j) [DirectedSystem N fun (x1 x2 : ι) (x3 : x1 ≤ x2) => ⇑(h x1 x2 x3)] (a : ScalarLimit A f) (m : DirectLimit M fun (i j : ι) (hij : i ≤ j) => g i j hij) (n : DirectLimit N fun (i j : ι) (hij : i ≤ j) => h i j hij) : pairing A f M g N h (a • m) n = a • pairing A f M g N h m n
```

**API note (not a source docstring):** Multiplying the left argument by a scalar from the scalar direct limit multiplies the paired tensor-limit element by that scalar.

[Source](../AlgebraicDirectLimits/VaryingScalar.lean#L231) (native range begins at line 231).

### DirectLimit.VaryingScalar.pairing_smul_right

```lean
theorem DirectLimit.VaryingScalar.pairing_smul_right {ι : Type u} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι] (A : ι → Type v) [(i : ι) → CommSemiring (A i)] (f : (i j : ι) → i ≤ j → A i →+* A j) [DirectedSystem A fun (x1 x2 : ι) (x3 : x1 ≤ x2) => ⇑(f x1 x2 x3)] (M : ι → Type w) [(i : ι) → AddCommMonoid (M i)] [(i : ι) → Module (A i) (M i)] (g : (i j : ι) → (h : i ≤ j) → M i →ₛₗ[f i j h] M j) [DirectedSystem M fun (x1 x2 : ι) (x3 : x1 ≤ x2) => ⇑(g x1 x2 x3)] (N : ι → Type x) [(i : ι) → AddCommMonoid (N i)] [(i : ι) → Module (A i) (N i)] (h : (i j : ι) → (hij : i ≤ j) → N i →ₛₗ[f i j hij] N j) [DirectedSystem N fun (x1 x2 : ι) (x3 : x1 ≤ x2) => ⇑(h x1 x2 x3)] (a : ScalarLimit A f) (m : DirectLimit M fun (i j : ι) (hij : i ≤ j) => g i j hij) (n : DirectLimit N fun (i j : ι) (hij : i ≤ j) => h i j hij) : pairing A f M g N h m (a • n) = a • pairing A f M g N h m n
```

**API note (not a source docstring):** Multiplying the right argument by a scalar from the scalar direct limit multiplies the paired tensor-limit element by that scalar. Together with the left law, this is the balanced linear pairing used for toTensorLimit.

[Source](../AlgebraicDirectLimits/VaryingScalar.lean#L250) (native range begins at line 250).

### DirectLimit.VaryingScalar.pairingLinear

```lean
noncomputable def DirectLimit.VaryingScalar.pairingLinear {ι : Type u} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι] (A : ι → Type v) [(i : ι) → CommSemiring (A i)] (f : (i j : ι) → i ≤ j → A i →+* A j) [DirectedSystem A fun (x1 x2 : ι) (x3 : x1 ≤ x2) => ⇑(f x1 x2 x3)] (M : ι → Type w) [(i : ι) → AddCommMonoid (M i)] [(i : ι) → Module (A i) (M i)] (g : (i j : ι) → (h : i ≤ j) → M i →ₛₗ[f i j h] M j) [DirectedSystem M fun (x1 x2 : ι) (x3 : x1 ≤ x2) => ⇑(g x1 x2 x3)] (N : ι → Type x) [(i : ι) → AddCommMonoid (N i)] [(i : ι) → Module (A i) (N i)] (h : (i j : ι) → (hij : i ≤ j) → N i →ₛₗ[f i j hij] N j) [DirectedSystem N fun (x1 x2 : ι) (x3 : x1 ≤ x2) => ⇑(h x1 x2 x3)] : (DirectLimit M fun (i j : ι) (hij : i ≤ j) => g i j hij) →ₗ[ScalarLimit A f] (DirectLimit N fun (i j : ι) (hij : i ≤ j) => h i j hij) →ₗ[ScalarLimit A f] DirectLimit (fun (i : ι) => TensorProduct (A i) (M i) (N i)) fun (x1 x2 : ι) (x3 : x1 ≤ x2) => tensorMap A f M g N h x1 x2 x3
```

The bilinear pairing on the two varying-scalar direct limits.

[Source](../AlgebraicDirectLimits/VaryingScalar.lean#L269) (native range begins at line 269).

### DirectLimit.VaryingScalar.toTensorLimit

```lean
noncomputable def DirectLimit.VaryingScalar.toTensorLimit {ι : Type u} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι] (A : ι → Type v) [(i : ι) → CommSemiring (A i)] (f : (i j : ι) → i ≤ j → A i →+* A j) [DirectedSystem A fun (x1 x2 : ι) (x3 : x1 ≤ x2) => ⇑(f x1 x2 x3)] (M : ι → Type w) [(i : ι) → AddCommMonoid (M i)] [(i : ι) → Module (A i) (M i)] (g : (i j : ι) → (h : i ≤ j) → M i →ₛₗ[f i j h] M j) [DirectedSystem M fun (x1 x2 : ι) (x3 : x1 ≤ x2) => ⇑(g x1 x2 x3)] (N : ι → Type x) [(i : ι) → AddCommMonoid (N i)] [(i : ι) → Module (A i) (N i)] (h : (i j : ι) → (hij : i ≤ j) → N i →ₛₗ[f i j hij] N j) [DirectedSystem N fun (x1 x2 : ι) (x3 : x1 ≤ x2) => ⇑(h x1 x2 x3)] : TensorProduct (ScalarLimit A f) (DirectLimit M fun (i j : ι) (hij : i ≤ j) => g i j hij) (DirectLimit N fun (i j : ι) (hij : i ≤ j) => h i j hij) →ₗ[ScalarLimit A f] DirectLimit (fun (i : ι) => TensorProduct (A i) (M i) (N i)) fun (x1 x2 : ι) (x3 : x1 ≤ x2) => tensorMap A f M g N h x1 x2 x3
```

The map from the tensor product of the two limits to the limit of stage tensor products.

[Source](../AlgebraicDirectLimits/VaryingScalar.lean#L287) (native range begins at line 287).

### DirectLimit.VaryingScalar.toTensorLimit_tmul_mk

```lean
theorem DirectLimit.VaryingScalar.toTensorLimit_tmul_mk {ι : Type u} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι] (A : ι → Type v) [(i : ι) → CommSemiring (A i)] (f : (i j : ι) → i ≤ j → A i →+* A j) [DirectedSystem A fun (x1 x2 : ι) (x3 : x1 ≤ x2) => ⇑(f x1 x2 x3)] (M : ι → Type w) [(i : ι) → AddCommMonoid (M i)] [(i : ι) → Module (A i) (M i)] (g : (i j : ι) → (h : i ≤ j) → M i →ₛₗ[f i j h] M j) [DirectedSystem M fun (x1 x2 : ι) (x3 : x1 ≤ x2) => ⇑(g x1 x2 x3)] (N : ι → Type x) [(i : ι) → AddCommMonoid (N i)] [(i : ι) → Module (A i) (N i)] (h : (i j : ι) → (hij : i ≤ j) → N i →ₛₗ[f i j hij] N j) [DirectedSystem N fun (x1 x2 : ι) (x3 : x1 ≤ x2) => ⇑(h x1 x2 x3)] (i : ι) (m : M i) (n : N i) : (toTensorLimit A f M g N h) ((of A f M g i) m ⊗ₜ[ScalarLimit A f] (of A f N h i) n) = (tensorOf A f M g N h i) (m ⊗ₜ[A i] n)
```

**API note (not a source docstring):** The forward tensor-limit map sends a tensor of two canonical same-stage images to the canonical image of their pure tensor. Use this named rule with rw; ordinary simp uses the separately documented quotient-normal-form rule after of_apply.

[Source](../AlgebraicDirectLimits/VaryingScalar.lean#L296) (native range begins at line 296).

### DirectLimit.VaryingScalar.toTensorLimit_tmul_mk_mk

```lean
theorem DirectLimit.VaryingScalar.toTensorLimit_tmul_mk_mk {ι : Type u} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι] (A : ι → Type v) [(i : ι) → CommSemiring (A i)] (f : (i j : ι) → i ≤ j → A i →+* A j) [DirectedSystem A fun (x1 x2 : ι) (x3 : x1 ≤ x2) => ⇑(f x1 x2 x3)] (M : ι → Type w) [(i : ι) → AddCommMonoid (M i)] [(i : ι) → Module (A i) (M i)] (g : (i j : ι) → (h : i ≤ j) → M i →ₛₗ[f i j h] M j) [DirectedSystem M fun (x1 x2 : ι) (x3 : x1 ≤ x2) => ⇑(g x1 x2 x3)] (N : ι → Type x) [(i : ι) → AddCommMonoid (N i)] [(i : ι) → Module (A i) (N i)] (h : (i j : ι) → (hij : i ≤ j) → N i →ₛₗ[f i j hij] N j) [DirectedSystem N fun (x1 x2 : ι) (x3 : x1 ≤ x2) => ⇑(h x1 x2 x3)] (i : ι) (m : M i) (n : N i) : (toTensorLimit A f M g N h) (⟦⟨i, m⟩⟧ ⊗ₜ[ScalarLimit A f] ⟦⟨i, n⟩⟧) = ⟦⟨i, m ⊗ₜ[A i] n⟩⟧
```

The tensor-limit map on quotient representatives, its simp normal form.

[Source](../AlgebraicDirectLimits/VaryingScalar.lean#L304) (native range begins at line 304).

### DirectLimit.VaryingScalar.tensorToLimits

```lean
noncomputable def DirectLimit.VaryingScalar.tensorToLimits {ι : Type u} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι] (A : ι → Type v) [(i : ι) → CommSemiring (A i)] (f : (i j : ι) → i ≤ j → A i →+* A j) [DirectedSystem A fun (x1 x2 : ι) (x3 : x1 ≤ x2) => ⇑(f x1 x2 x3)] (M : ι → Type w) [(i : ι) → AddCommMonoid (M i)] [(i : ι) → Module (A i) (M i)] (g : (i j : ι) → (h : i ≤ j) → M i →ₛₗ[f i j h] M j) [DirectedSystem M fun (x1 x2 : ι) (x3 : x1 ≤ x2) => ⇑(g x1 x2 x3)] (N : ι → Type x) [(i : ι) → AddCommMonoid (N i)] [(i : ι) → Module (A i) (N i)] (h : (i j : ι) → (hij : i ≤ j) → N i →ₛₗ[f i j hij] N j) [DirectedSystem N fun (x1 x2 : ι) (x3 : x1 ≤ x2) => ⇑(h x1 x2 x3)] (i : ι) : TensorProduct (A i) (M i) (N i) →ₛₗ[Ring.of A (fun (x1 x2 : ι) (x3 : x1 ≤ x2) => f x1 x2 x3) i] TensorProduct (ScalarLimit A f) (DirectLimit M fun (i j : ι) (hij : i ≤ j) => g i j hij) (DirectLimit N fun (i j : ι) (hij : i ≤ j) => h i j hij)
```

Map a stage tensor product into the tensor product of the two limits.

[Source](../AlgebraicDirectLimits/VaryingScalar.lean#L311) (native range begins at line 311).

### DirectLimit.VaryingScalar.tensorToLimits_tmul

```lean
theorem DirectLimit.VaryingScalar.tensorToLimits_tmul {ι : Type u} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι] (A : ι → Type v) [(i : ι) → CommSemiring (A i)] (f : (i j : ι) → i ≤ j → A i →+* A j) [DirectedSystem A fun (x1 x2 : ι) (x3 : x1 ≤ x2) => ⇑(f x1 x2 x3)] (M : ι → Type w) [(i : ι) → AddCommMonoid (M i)] [(i : ι) → Module (A i) (M i)] (g : (i j : ι) → (h : i ≤ j) → M i →ₛₗ[f i j h] M j) [DirectedSystem M fun (x1 x2 : ι) (x3 : x1 ≤ x2) => ⇑(g x1 x2 x3)] (N : ι → Type x) [(i : ι) → AddCommMonoid (N i)] [(i : ι) → Module (A i) (N i)] (h : (i j : ι) → (hij : i ≤ j) → N i →ₛₗ[f i j hij] N j) [DirectedSystem N fun (x1 x2 : ι) (x3 : x1 ≤ x2) => ⇑(h x1 x2 x3)] (i : ι) (m : M i) (n : N i) : (tensorToLimits A f M g N h i) (m ⊗ₜ[A i] n) = (of A f M g i) m ⊗ₜ[ScalarLimit A f] (of A f N h i) n
```

**API note (not a source docstring):** The reverse stage map sends a pure tensor to the pure tensor of its two canonical images in the module limits.

[Source](../AlgebraicDirectLimits/VaryingScalar.lean#L319) (native range begins at line 319).

### DirectLimit.VaryingScalar.tensorToLimits_map

```lean
theorem DirectLimit.VaryingScalar.tensorToLimits_map {ι : Type u} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι] (A : ι → Type v) [(i : ι) → CommSemiring (A i)] (f : (i j : ι) → i ≤ j → A i →+* A j) [DirectedSystem A fun (x1 x2 : ι) (x3 : x1 ≤ x2) => ⇑(f x1 x2 x3)] (M : ι → Type w) [(i : ι) → AddCommMonoid (M i)] [(i : ι) → Module (A i) (M i)] (g : (i j : ι) → (h : i ≤ j) → M i →ₛₗ[f i j h] M j) [DirectedSystem M fun (x1 x2 : ι) (x3 : x1 ≤ x2) => ⇑(g x1 x2 x3)] (N : ι → Type x) [(i : ι) → AddCommMonoid (N i)] [(i : ι) → Module (A i) (N i)] (h : (i j : ι) → (hij : i ≤ j) → N i →ₛₗ[f i j hij] N j) [DirectedSystem N fun (x1 x2 : ι) (x3 : x1 ≤ x2) => ⇑(h x1 x2 x3)] {i j : ι} (hij : i ≤ j) (x : TensorProduct (A i) (M i) (N i)) : (tensorToLimits A f M g N h j) ((tensorMap A f M g N h i j hij) x) = (tensorToLimits A f M g N h i) x
```

**API note (not a source docstring):** The reverse stage maps commute with the tensor-product transition maps. This compatibility allows descent to the tensor direct limit.

[Source](../AlgebraicDirectLimits/VaryingScalar.lean#L325) (native range begins at line 325).

### DirectLimit.VaryingScalar.fromTensorLimitDef

```lean
noncomputable def DirectLimit.VaryingScalar.fromTensorLimitDef {ι : Type u} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι] (A : ι → Type v) [(i : ι) → CommSemiring (A i)] (f : (i j : ι) → i ≤ j → A i →+* A j) [DirectedSystem A fun (x1 x2 : ι) (x3 : x1 ≤ x2) => ⇑(f x1 x2 x3)] (M : ι → Type w) [(i : ι) → AddCommMonoid (M i)] [(i : ι) → Module (A i) (M i)] (g : (i j : ι) → (h : i ≤ j) → M i →ₛₗ[f i j h] M j) [DirectedSystem M fun (x1 x2 : ι) (x3 : x1 ≤ x2) => ⇑(g x1 x2 x3)] (N : ι → Type x) [(i : ι) → AddCommMonoid (N i)] [(i : ι) → Module (A i) (N i)] (h : (i j : ι) → (hij : i ≤ j) → N i →ₛₗ[f i j hij] N j) [DirectedSystem N fun (x1 x2 : ι) (x3 : x1 ≤ x2) => ⇑(h x1 x2 x3)] : (DirectLimit (fun (i : ι) => TensorProduct (A i) (M i) (N i)) fun (x1 x2 : ι) (x3 : x1 ≤ x2) => tensorMap A f M g N h x1 x2 x3) → TensorProduct (ScalarLimit A f) (DirectLimit M fun (i j : ι) (hij : i ≤ j) => g i j hij) (DirectLimit N fun (i j : ι) (hij : i ≤ j) => h i j hij)
```

The representative-level map from the limit of stage tensor products back to the
tensor product of the limits.

[Source](../AlgebraicDirectLimits/VaryingScalar.lean#L334) (native range begins at line 334).

### DirectLimit.VaryingScalar.fromTensorLimitDef_mk

```lean
theorem DirectLimit.VaryingScalar.fromTensorLimitDef_mk {ι : Type u} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι] (A : ι → Type v) [(i : ι) → CommSemiring (A i)] (f : (i j : ι) → i ≤ j → A i →+* A j) [DirectedSystem A fun (x1 x2 : ι) (x3 : x1 ≤ x2) => ⇑(f x1 x2 x3)] (M : ι → Type w) [(i : ι) → AddCommMonoid (M i)] [(i : ι) → Module (A i) (M i)] (g : (i j : ι) → (h : i ≤ j) → M i →ₛₗ[f i j h] M j) [DirectedSystem M fun (x1 x2 : ι) (x3 : x1 ≤ x2) => ⇑(g x1 x2 x3)] (N : ι → Type x) [(i : ι) → AddCommMonoid (N i)] [(i : ι) → Module (A i) (N i)] (h : (i j : ι) → (hij : i ≤ j) → N i →ₛₗ[f i j hij] N j) [DirectedSystem N fun (x1 x2 : ι) (x3 : x1 ≤ x2) => ⇑(h x1 x2 x3)] (i : ι) (x : TensorProduct (A i) (M i) (N i)) : fromTensorLimitDef A f M g N h ⟦⟨i, x⟩⟧ = (tensorToLimits A f M g N h i) x
```

**API note (not a source docstring):** The representative-level reverse map evaluates a quotient representative by the reverse map at that stage.

[Source](../AlgebraicDirectLimits/VaryingScalar.lean#L346) (native range begins at line 346).

### DirectLimit.VaryingScalar.fromTensorLimitDef_add

```lean
theorem DirectLimit.VaryingScalar.fromTensorLimitDef_add {ι : Type u} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι] (A : ι → Type v) [(i : ι) → CommSemiring (A i)] (f : (i j : ι) → i ≤ j → A i →+* A j) [DirectedSystem A fun (x1 x2 : ι) (x3 : x1 ≤ x2) => ⇑(f x1 x2 x3)] (M : ι → Type w) [(i : ι) → AddCommMonoid (M i)] [(i : ι) → Module (A i) (M i)] (g : (i j : ι) → (h : i ≤ j) → M i →ₛₗ[f i j h] M j) [DirectedSystem M fun (x1 x2 : ι) (x3 : x1 ≤ x2) => ⇑(g x1 x2 x3)] (N : ι → Type x) [(i : ι) → AddCommMonoid (N i)] [(i : ι) → Module (A i) (N i)] (h : (i j : ι) → (hij : i ≤ j) → N i →ₛₗ[f i j hij] N j) [DirectedSystem N fun (x1 x2 : ι) (x3 : x1 ≤ x2) => ⇑(h x1 x2 x3)] (x y : DirectLimit (fun (i : ι) => TensorProduct (A i) (M i) (N i)) fun (x1 x2 : ι) (x3 : x1 ≤ x2) => tensorMap A f M g N h x1 x2 x3) : fromTensorLimitDef A f M g N h (x + y) = fromTensorLimitDef A f M g N h x + fromTensorLimitDef A f M g N h y
```

**API note (not a source docstring):** The representative-level reverse map preserves addition; this supplies the additive part of its bundled linear map.

[Source](../AlgebraicDirectLimits/VaryingScalar.lean#L351) (native range begins at line 351).

### DirectLimit.VaryingScalar.fromTensorLimitDef_smul

```lean
theorem DirectLimit.VaryingScalar.fromTensorLimitDef_smul {ι : Type u} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι] (A : ι → Type v) [(i : ι) → CommSemiring (A i)] (f : (i j : ι) → i ≤ j → A i →+* A j) [DirectedSystem A fun (x1 x2 : ι) (x3 : x1 ≤ x2) => ⇑(f x1 x2 x3)] (M : ι → Type w) [(i : ι) → AddCommMonoid (M i)] [(i : ι) → Module (A i) (M i)] (g : (i j : ι) → (h : i ≤ j) → M i →ₛₗ[f i j h] M j) [DirectedSystem M fun (x1 x2 : ι) (x3 : x1 ≤ x2) => ⇑(g x1 x2 x3)] (N : ι → Type x) [(i : ι) → AddCommMonoid (N i)] [(i : ι) → Module (A i) (N i)] (h : (i j : ι) → (hij : i ≤ j) → N i →ₛₗ[f i j hij] N j) [DirectedSystem N fun (x1 x2 : ι) (x3 : x1 ≤ x2) => ⇑(h x1 x2 x3)] (a : ScalarLimit A f) (x : DirectLimit (fun (i : ι) => TensorProduct (A i) (M i) (N i)) fun (x1 x2 : ι) (x3 : x1 ≤ x2) => tensorMap A f M g N h x1 x2 x3) : fromTensorLimitDef A f M g N h (a • x) = a • fromTensorLimitDef A f M g N h x
```

**API note (not a source docstring):** The representative-level reverse map respects the action of the scalar direct limit, supplying the scalar part of the bundled linear map.

[Source](../AlgebraicDirectLimits/VaryingScalar.lean#L361) (native range begins at line 361).

### DirectLimit.VaryingScalar.fromTensorLimit

```lean
noncomputable def DirectLimit.VaryingScalar.fromTensorLimit {ι : Type u} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι] (A : ι → Type v) [(i : ι) → CommSemiring (A i)] (f : (i j : ι) → i ≤ j → A i →+* A j) [DirectedSystem A fun (x1 x2 : ι) (x3 : x1 ≤ x2) => ⇑(f x1 x2 x3)] (M : ι → Type w) [(i : ι) → AddCommMonoid (M i)] [(i : ι) → Module (A i) (M i)] (g : (i j : ι) → (h : i ≤ j) → M i →ₛₗ[f i j h] M j) [DirectedSystem M fun (x1 x2 : ι) (x3 : x1 ≤ x2) => ⇑(g x1 x2 x3)] (N : ι → Type x) [(i : ι) → AddCommMonoid (N i)] [(i : ι) → Module (A i) (N i)] (h : (i j : ι) → (hij : i ≤ j) → N i →ₛₗ[f i j hij] N j) [DirectedSystem N fun (x1 x2 : ι) (x3 : x1 ≤ x2) => ⇑(h x1 x2 x3)] : (DirectLimit (fun (i : ι) => TensorProduct (A i) (M i) (N i)) fun (x1 x2 : ι) (x3 : x1 ≤ x2) => tensorMap A f M g N h x1 x2 x3) →ₗ[ScalarLimit A f] TensorProduct (ScalarLimit A f) (DirectLimit M fun (i j : ι) (hij : i ≤ j) => g i j hij) (DirectLimit N fun (i j : ι) (hij : i ≤ j) => h i j hij)
```

The map from the limit of stage tensor products to the tensor product of the limits.

[Source](../AlgebraicDirectLimits/VaryingScalar.lean#L378) (native range begins at line 378).

### DirectLimit.VaryingScalar.fromTensorLimit_mk

```lean
theorem DirectLimit.VaryingScalar.fromTensorLimit_mk {ι : Type u} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι] (A : ι → Type v) [(i : ι) → CommSemiring (A i)] (f : (i j : ι) → i ≤ j → A i →+* A j) [DirectedSystem A fun (x1 x2 : ι) (x3 : x1 ≤ x2) => ⇑(f x1 x2 x3)] (M : ι → Type w) [(i : ι) → AddCommMonoid (M i)] [(i : ι) → Module (A i) (M i)] (g : (i j : ι) → (h : i ≤ j) → M i →ₛₗ[f i j h] M j) [DirectedSystem M fun (x1 x2 : ι) (x3 : x1 ≤ x2) => ⇑(g x1 x2 x3)] (N : ι → Type x) [(i : ι) → AddCommMonoid (N i)] [(i : ι) → Module (A i) (N i)] (h : (i j : ι) → (hij : i ≤ j) → N i →ₛₗ[f i j hij] N j) [DirectedSystem N fun (x1 x2 : ι) (x3 : x1 ≤ x2) => ⇑(h x1 x2 x3)] (i : ι) (x : TensorProduct (A i) (M i) (N i)) : (fromTensorLimit A f M g N h) ⟦⟨i, x⟩⟧ = (tensorToLimits A f M g N h i) x
```

**API note (not a source docstring):** The bundled reverse linear map has the same stage-representative formula as its underlying representative-level function.

[Source](../AlgebraicDirectLimits/VaryingScalar.lean#L389) (native range begins at line 389).

### DirectLimit.VaryingScalar.fromTensorLimit_toTensorLimit

```lean
theorem DirectLimit.VaryingScalar.fromTensorLimit_toTensorLimit {ι : Type u} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι] (A : ι → Type v) [(i : ι) → CommSemiring (A i)] (f : (i j : ι) → i ≤ j → A i →+* A j) [DirectedSystem A fun (x1 x2 : ι) (x3 : x1 ≤ x2) => ⇑(f x1 x2 x3)] (M : ι → Type w) [(i : ι) → AddCommMonoid (M i)] [(i : ι) → Module (A i) (M i)] (g : (i j : ι) → (h : i ≤ j) → M i →ₛₗ[f i j h] M j) [DirectedSystem M fun (x1 x2 : ι) (x3 : x1 ≤ x2) => ⇑(g x1 x2 x3)] (N : ι → Type x) [(i : ι) → AddCommMonoid (N i)] [(i : ι) → Module (A i) (N i)] (h : (i j : ι) → (hij : i ≤ j) → N i →ₛₗ[f i j hij] N j) [DirectedSystem N fun (x1 x2 : ι) (x3 : x1 ≤ x2) => ⇑(h x1 x2 x3)] (x : TensorProduct (ScalarLimit A f) (DirectLimit M fun (i j : ι) (hij : i ≤ j) => g i j hij) (DirectLimit N fun (i j : ι) (hij : i ≤ j) => h i j hij)) : (fromTensorLimit A f M g N h) ((toTensorLimit A f M g N h) x) = x
```

**API note (not a source docstring):** The reverse map after the forward map is the identity on the tensor product of the two module limits.

[Source](../AlgebraicDirectLimits/VaryingScalar.lean#L394) (native range begins at line 394).

### DirectLimit.VaryingScalar.toTensorLimit_fromTensorLimit

```lean
theorem DirectLimit.VaryingScalar.toTensorLimit_fromTensorLimit {ι : Type u} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι] (A : ι → Type v) [(i : ι) → CommSemiring (A i)] (f : (i j : ι) → i ≤ j → A i →+* A j) [DirectedSystem A fun (x1 x2 : ι) (x3 : x1 ≤ x2) => ⇑(f x1 x2 x3)] (M : ι → Type w) [(i : ι) → AddCommMonoid (M i)] [(i : ι) → Module (A i) (M i)] (g : (i j : ι) → (h : i ≤ j) → M i →ₛₗ[f i j h] M j) [DirectedSystem M fun (x1 x2 : ι) (x3 : x1 ≤ x2) => ⇑(g x1 x2 x3)] (N : ι → Type x) [(i : ι) → AddCommMonoid (N i)] [(i : ι) → Module (A i) (N i)] (h : (i j : ι) → (hij : i ≤ j) → N i →ₛₗ[f i j hij] N j) [DirectedSystem N fun (x1 x2 : ι) (x3 : x1 ≤ x2) => ⇑(h x1 x2 x3)] (x : DirectLimit (fun (i : ι) => TensorProduct (A i) (M i) (N i)) fun (x1 x2 : ι) (x3 : x1 ≤ x2) => tensorMap A f M g N h x1 x2 x3) : (toTensorLimit A f M g N h) ((fromTensorLimit A f M g N h) x) = x
```

**API note (not a source docstring):** The forward map after the reverse map is the identity on the direct limit of the stagewise tensor products.

[Source](../AlgebraicDirectLimits/VaryingScalar.lean#L416) (native range begins at line 416).

### DirectLimit.VaryingScalar.tensorProductEquiv

```lean
noncomputable def DirectLimit.VaryingScalar.tensorProductEquiv {ι : Type u} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι] (A : ι → Type v) [(i : ι) → CommSemiring (A i)] (f : (i j : ι) → i ≤ j → A i →+* A j) [DirectedSystem A fun (x1 x2 : ι) (x3 : x1 ≤ x2) => ⇑(f x1 x2 x3)] (M : ι → Type w) [(i : ι) → AddCommMonoid (M i)] [(i : ι) → Module (A i) (M i)] (g : (i j : ι) → (h : i ≤ j) → M i →ₛₗ[f i j h] M j) [DirectedSystem M fun (x1 x2 : ι) (x3 : x1 ≤ x2) => ⇑(g x1 x2 x3)] (N : ι → Type x) [(i : ι) → AddCommMonoid (N i)] [(i : ι) → Module (A i) (N i)] (h : (i j : ι) → (hij : i ≤ j) → N i →ₛₗ[f i j hij] N j) [DirectedSystem N fun (x1 x2 : ι) (x3 : x1 ≤ x2) => ⇑(h x1 x2 x3)] : TensorProduct (ScalarLimit A f) (DirectLimit M fun (i j : ι) (hij : i ≤ j) => g i j hij) (DirectLimit N fun (i j : ι) (hij : i ≤ j) => h i j hij) ≃ₗ[ScalarLimit A f] DirectLimit (fun (i : ι) => TensorProduct (A i) (M i) (N i)) fun (x1 x2 : ι) (x3 : x1 ≤ x2) => tensorMap A f M g N h x1 x2 x3
```

Tensor products commute with directed limits even when the scalar semiring varies along the
same directed system.

[Source](../AlgebraicDirectLimits/VaryingScalar.lean#L427) (native range begins at line 427).

### DirectLimit.VaryingScalar.tensorProductEquiv_tmul_mk

```lean
theorem DirectLimit.VaryingScalar.tensorProductEquiv_tmul_mk {ι : Type u} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι] (A : ι → Type v) [(i : ι) → CommSemiring (A i)] (f : (i j : ι) → i ≤ j → A i →+* A j) [DirectedSystem A fun (x1 x2 : ι) (x3 : x1 ≤ x2) => ⇑(f x1 x2 x3)] (M : ι → Type w) [(i : ι) → AddCommMonoid (M i)] [(i : ι) → Module (A i) (M i)] (g : (i j : ι) → (h : i ≤ j) → M i →ₛₗ[f i j h] M j) [DirectedSystem M fun (x1 x2 : ι) (x3 : x1 ≤ x2) => ⇑(g x1 x2 x3)] (N : ι → Type x) [(i : ι) → AddCommMonoid (N i)] [(i : ι) → Module (A i) (N i)] (h : (i j : ι) → (hij : i ≤ j) → N i →ₛₗ[f i j hij] N j) [DirectedSystem N fun (x1 x2 : ι) (x3 : x1 ≤ x2) => ⇑(h x1 x2 x3)] (i : ι) (m : M i) (n : N i) : (tensorProductEquiv A f M g N h) ((of A f M g i) m ⊗ₜ[ScalarLimit A f] (of A f N h i) n) = (tensorOf A f M g N h i) (m ⊗ₜ[A i] n)
```

**API note (not a source docstring):** The linear equivalence has the same pure-tensor computation as toTensorLimit. This named stage-map form supports rw; the quotient-normal-form companion supports simp.

[Source](../AlgebraicDirectLimits/VaryingScalar.lean#L440) (native range begins at line 440).

### DirectLimit.VaryingScalar.tensorProductEquiv_tmul_mk_mk

```lean
theorem DirectLimit.VaryingScalar.tensorProductEquiv_tmul_mk_mk {ι : Type u} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι] (A : ι → Type v) [(i : ι) → CommSemiring (A i)] (f : (i j : ι) → i ≤ j → A i →+* A j) [DirectedSystem A fun (x1 x2 : ι) (x3 : x1 ≤ x2) => ⇑(f x1 x2 x3)] (M : ι → Type w) [(i : ι) → AddCommMonoid (M i)] [(i : ι) → Module (A i) (M i)] (g : (i j : ι) → (h : i ≤ j) → M i →ₛₗ[f i j h] M j) [DirectedSystem M fun (x1 x2 : ι) (x3 : x1 ≤ x2) => ⇑(g x1 x2 x3)] (N : ι → Type x) [(i : ι) → AddCommMonoid (N i)] [(i : ι) → Module (A i) (N i)] (h : (i j : ι) → (hij : i ≤ j) → N i →ₛₗ[f i j hij] N j) [DirectedSystem N fun (x1 x2 : ι) (x3 : x1 ≤ x2) => ⇑(h x1 x2 x3)] (i : ι) (m : M i) (n : N i) : (tensorProductEquiv A f M g N h) (⟦⟨i, m⟩⟧ ⊗ₜ[ScalarLimit A f] ⟦⟨i, n⟩⟧) = ⟦⟨i, m ⊗ₜ[A i] n⟩⟧
```

The tensor equivalence on quotient representatives, its simp normal form.

[Source](../AlgebraicDirectLimits/VaryingScalar.lean#L446) (native range begins at line 446).

### DirectLimit.VaryingScalar.tensorProductEquiv_symm_mk

```lean
theorem DirectLimit.VaryingScalar.tensorProductEquiv_symm_mk {ι : Type u} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι] (A : ι → Type v) [(i : ι) → CommSemiring (A i)] (f : (i j : ι) → i ≤ j → A i →+* A j) [DirectedSystem A fun (x1 x2 : ι) (x3 : x1 ≤ x2) => ⇑(f x1 x2 x3)] (M : ι → Type w) [(i : ι) → AddCommMonoid (M i)] [(i : ι) → Module (A i) (M i)] (g : (i j : ι) → (h : i ≤ j) → M i →ₛₗ[f i j h] M j) [DirectedSystem M fun (x1 x2 : ι) (x3 : x1 ≤ x2) => ⇑(g x1 x2 x3)] (N : ι → Type x) [(i : ι) → AddCommMonoid (N i)] [(i : ι) → Module (A i) (N i)] (h : (i j : ι) → (hij : i ≤ j) → N i →ₛₗ[f i j hij] N j) [DirectedSystem N fun (x1 x2 : ι) (x3 : x1 ≤ x2) => ⇑(h x1 x2 x3)] (i : ι) (x : TensorProduct (A i) (M i) (N i)) : (tensorProductEquiv A f M g N h).symm ⟦⟨i, x⟩⟧ = (tensorToLimits A f M g N h i) x
```

**API note (not a source docstring):** The inverse equivalence sends a stage tensor representative through tensorToLimits at that stage; the stage tensor need not be pure.

[Source](../AlgebraicDirectLimits/VaryingScalar.lean#L453) (native range begins at line 453).

## CofinalGroupCompletionClient

Scope: boundary client (not re-exported by library root).

### CofinalGroupCompletionClient.evens

```lean
def CofinalGroupCompletionClient.evens : AddSubmonoid ℕ
```

The even natural numbers form a proper cofinal submonoid.

[Source](../tests/CofinalGroupCompletionClient.lean#L40) (native range begins at line 40).

### CofinalGroupCompletionClient.evens_saturation

```lean
theorem CofinalGroupCompletionClient.evens_saturation : evens.saturation = ⊤
```

**API note (not a source docstring):** Boundary client: every natural number has a complement whose sum is even, so the even submonoid has top saturation.

[Source](../tests/CofinalGroupCompletionClient.lean#L48) (native range begins at line 48).

### CofinalGroupCompletionClient.evens_proper

```lean
theorem CofinalGroupCompletionClient.evens_proper : 1 ∉ evens
```

**API note (not a source docstring):** Boundary client: the even submonoid is proper, since it does not contain one. Top saturation therefore need not mean equality with the ambient monoid.

[Source](../tests/CofinalGroupCompletionClient.lean#L56) (native range begins at line 56).

### CofinalGroupCompletionClient.evens_completion_injective

```lean
theorem CofinalGroupCompletionClient.evens_completion_injective : Function.Injective ⇑(Algebra.GrothendieckAddGroup.lift (Algebra.GrothendieckAddGroup.of.comp evens.subtype))
```

**API note (not a source docstring):** Boundary client: inclusion of the even submonoid into the natural numbers induces an injective map on their Grothendieck additive groups.

[Source](../tests/CofinalGroupCompletionClient.lean#L60) (native range begins at line 60).

### CofinalGroupCompletionClient.evens_denominators

```lean
theorem CofinalGroupCompletionClient.evens_denominators (z : Algebra.GrothendieckAddGroup ℕ) : ∃ (m : ℕ) (l : ↥evens), z = Algebra.GrothendieckAddGroup.of m - Algebra.GrothendieckAddGroup.of ↑l
```

**API note (not a source docstring):** Boundary client: every element of the group completion of the natural numbers is a difference whose second representative lies in the even submonoid.

[Source](../tests/CofinalGroupCompletionClient.lean#L64) (native range begins at line 64).

### CofinalGroupCompletionClient.noncancellative_canonical_map_not_injective

```lean
theorem CofinalGroupCompletionClient.noncancellative_canonical_map_not_injective : ¬Function.Injective ⇑Algebra.GrothendieckAddGroup.of
```

Multiplicative natural numbers regarded additively are noncancellative;
their canonical map into the completion identifies zero and one.

[Source](../tests/CofinalGroupCompletionClient.lean#L68) (native range begins at line 68).

### CofinalGroupCompletionClient.noncancellative_completion_injective

```lean
theorem CofinalGroupCompletionClient.noncancellative_completion_injective : Function.Injective ⇑(Algebra.GrothendieckAddGroup.lift (Algebra.GrothendieckAddGroup.of.comp ⊤.subtype))
```

**API note (not a source docstring):** Boundary client on multiplicative natural numbers viewed additively: inclusion of the top submonoid induces an injective map on completions even though the original monoid does not cancel. The separate canonical-map counterexample concerns a different map.

[Source](../tests/CofinalGroupCompletionClient.lean#L78) (native range begins at line 78).

### CofinalGroupCompletionClient.punit_completion_injective

```lean
theorem CofinalGroupCompletionClient.punit_completion_injective : Function.Injective ⇑(Algebra.GrothendieckAddGroup.lift (Algebra.GrothendieckAddGroup.of.comp ⊤.subtype))
```

**API note (not a source docstring):** Boundary client for the one-element additive monoid PUnit: the map on completions induced by the top-submonoid inclusion is injective. The native display suppresses this inferred ambient type; see the linked source.

[Source](../tests/CofinalGroupCompletionClient.lean#L83) (native range begins at line 83).

## GradedStabilizationClient

Scope: boundary client (not re-exported by library root).

### AlgebraicDirectLimits.Tests.GradedStabilization.nat_one_cofinal

```lean
theorem AlgebraicDirectLimits.Tests.GradedStabilization.nat_one_cofinal : (AddSubmonoid.multiples 1).saturation = ⊤
```

**API note (not a source docstring):** Boundary client: multiples of one in the additive natural numbers have top saturation, supplying the cofinality hypothesis for zero-degree stabilization.

[Source](../tests/GradedStabilizationClient.lean#L77) (native range begins at line 77).

### AlgebraicDirectLimits.Tests.GradedStabilization.zero_degree_distinguishes

```lean
theorem AlgebraicDirectLimits.Tests.GradedStabilization.zero_degree_distinguishes : Algebra.GrothendieckAddGroup.GradedStabilization.normalization 0 1 ⟦⟨0, ⟨0, ⋯⟩⟩⟧ ≠ Algebra.GrothendieckAddGroup.GradedStabilization.normalization 0 1 ⟦⟨0, ⟨1, ⋯⟩⟩⟧
```

Zero degree is allowed, and its normalized kernel need not be trivial.

[Source](../tests/GradedStabilizationClient.lean#L85) (native range begins at line 85).

### AlgebraicDirectLimits.Tests.GradedStabilization.zeroDegreeEquiv

```lean
noncomputable def AlgebraicDirectLimits.Tests.GradedStabilization.zeroDegreeEquiv : DirectLimit (Algebra.GrothendieckAddGroup.GradedStabilization.degreeFiber 0 1) (Algebra.GrothendieckAddGroup.GradedStabilization.transition 0 1) ≃ ↥(Algebra.GrothendieckAddGroup.GradedStabilization.inducedDegree 0).ker
```

Zero-degree stabilization of the additive natural numbers.

[Source](../tests/GradedStabilizationClient.lean#L95) (native range begins at line 95).

### AlgebraicDirectLimits.Tests.GradedStabilization.absorbing_cofinal

```lean
theorem AlgebraicDirectLimits.Tests.GradedStabilization.absorbing_cofinal : (AddSubmonoid.multiples (Additive.ofMul 0)).saturation = ⊤
```

Multiplicative naturals, viewed additively, have an absorbing element.
This is an existing type, not a new completion or quotient.

[Source](../tests/GradedStabilizationClient.lean#L99) (native range begins at line 99).

### AlgebraicDirectLimits.Tests.GradedStabilization.absorbingZero

```lean
def AlgebraicDirectLimits.Tests.GradedStabilization.absorbingZero : Algebra.GrothendieckAddGroup.GradedStabilization.degreeFiber 0 (Additive.ofMul 0) 0
```

The absorbing element in the stage-zero fiber for multiplicative naturals.

[Source](../tests/GradedStabilizationClient.lean#L112) (native range begins at line 112).

### AlgebraicDirectLimits.Tests.GradedStabilization.absorbingOne

```lean
def AlgebraicDirectLimits.Tests.GradedStabilization.absorbingOne : Algebra.GrothendieckAddGroup.GradedStabilization.degreeFiber 0 (Additive.ofMul 0) 0
```

The unit in the same stage-zero fiber, distinct before stabilization.

[Source](../tests/GradedStabilizationClient.lean#L116) (native range begins at line 116).

### AlgebraicDirectLimits.Tests.GradedStabilization.absorbing_representatives_distinct

```lean
theorem AlgebraicDirectLimits.Tests.GradedStabilization.absorbing_representatives_distinct : absorbingZero ≠ absorbingOne
```

**API note (not a source docstring):** Boundary client: zero and one in the stage-zero degree fiber of multiplicative natural numbers are distinct before passing to the direct limit.

[Source](../tests/GradedStabilizationClient.lean#L120) (native range begins at line 120).

### AlgebraicDirectLimits.Tests.GradedStabilization.absorbing_transition_not_injective

```lean
theorem AlgebraicDirectLimits.Tests.GradedStabilization.absorbing_transition_not_injective : ¬Function.Injective ⇑(Algebra.GrothendieckAddGroup.GradedStabilization.transition 0 (Additive.ofMul 0) 0 1 absorbing_transition_not_injective._proof_1)
```

The transition itself is not injective; no hidden cancellation of M.

[Source](../tests/GradedStabilizationClient.lean#L124) (native range begins at line 124).

### AlgebraicDirectLimits.Tests.GradedStabilization.absorbing_limit_equal

```lean
theorem AlgebraicDirectLimits.Tests.GradedStabilization.absorbing_limit_equal : ⟦⟨0, absorbingZero⟩⟧ = ⟦⟨0, absorbingOne⟩⟧
```

**API note (not a source docstring):** Boundary client: those distinct stage-zero elements become equal in the direct limit after multiplication by the absorbing stabilizer. This illustrates that transition maps need not be injective.

[Source](../tests/GradedStabilizationClient.lean#L134) (native range begins at line 134).

### AlgebraicDirectLimits.Tests.GradedStabilization.absorbingEquiv

```lean
noncomputable def AlgebraicDirectLimits.Tests.GradedStabilization.absorbingEquiv : DirectLimit (Algebra.GrothendieckAddGroup.GradedStabilization.degreeFiber 0 (Additive.ofMul 0)) (Algebra.GrothendieckAddGroup.GradedStabilization.transition 0 (Additive.ofMul 0)) ≃ ↥(Algebra.GrothendieckAddGroup.GradedStabilization.inducedDegree 0).ker
```

Normalization with a noncancellative source and absorbing stabilizer.

[Source](../tests/GradedStabilizationClient.lean#L141) (native range begins at line 141).

### AlgebraicDirectLimits.Tests.GradedStabilization.group_zero_cofinal

```lean
theorem AlgebraicDirectLimits.Tests.GradedStabilization.group_zero_cofinal {G : Type v} [AddCommGroup G] : (AddSubmonoid.multiples 0).saturation = ⊤
```

Zero is cofinal in an additive group; a positive-degree premise is absent.

[Source](../tests/GradedStabilizationClient.lean#L145) (native range begins at line 145).

### AlgebraicDirectLimits.Tests.GradedStabilization.groupZeroEquiv

```lean
noncomputable def AlgebraicDirectLimits.Tests.GradedStabilization.groupZeroEquiv : DirectLimit (Algebra.GrothendieckAddGroup.GradedStabilization.degreeFiber 0 0) (Algebra.GrothendieckAddGroup.GradedStabilization.transition 0 0) ≃ ↥(Algebra.GrothendieckAddGroup.GradedStabilization.inducedDegree 0).ker
```

Normalization for the zero degree and zero stabilizer on the integers.

[Source](../tests/GradedStabilizationClient.lean#L155) (native range begins at line 155).

### AlgebraicDirectLimits.Tests.GradedStabilization.product_diagonal_cofinal

```lean
theorem AlgebraicDirectLimits.Tests.GradedStabilization.product_diagonal_cofinal : (AddSubmonoid.multiples (1, 1)).saturation = ⊤
```

The degree codomain can be genuinely componentwise.

[Source](../tests/GradedStabilizationClient.lean#L163) (native range begins at line 163).

### AlgebraicDirectLimits.Tests.GradedStabilization.componentwiseEquiv

```lean
noncomputable def AlgebraicDirectLimits.Tests.GradedStabilization.componentwiseEquiv : DirectLimit (Algebra.GrothendieckAddGroup.GradedStabilization.degreeFiber (AddMonoidHom.id (ℕ × ℕ)) (1, 1)) (Algebra.GrothendieckAddGroup.GradedStabilization.transition (AddMonoidHom.id (ℕ × ℕ)) (1, 1)) ≃ ↥(Algebra.GrothendieckAddGroup.GradedStabilization.inducedDegree (AddMonoidHom.id (ℕ × ℕ))).ker
```

Normalization for the componentwise degree on pairs of natural numbers.

[Source](../tests/GradedStabilizationClient.lean#L174) (native range begins at line 174).

### AlgebraicDirectLimits.Tests.GradedStabilization.arbitrary_target_cross_stage

```lean
theorem AlgebraicDirectLimits.Tests.GradedStabilization.arbitrary_target_cross_stage {A : Type w} [AddCommMonoid A] : ⟦⟨0, ⟨Additive.ofMul 1, ⋯⟩⟩⟧ = ⟦⟨1, ⟨Additive.ofMul 0, ⋯⟩⟩⟧
```

Native cross-stage equality does not require cancellation of the degree target.

[Source](../tests/GradedStabilizationClient.lean#L178) (native range begins at line 178).
