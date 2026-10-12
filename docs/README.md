# API reference

[API.md](API.md) is a partial reference: 73 library display sites and 23 sites
from two boundary clients. These are selected signatures, **not** a theorem
count, a declaration census or documentation for the entire library. Client
namespaces are not re-exported by `AlgebraicDirectLimits`.

The seven library modules are `CofinalSequence`, `CofinalGroupCompletion`,
`GradedStabilization`, `LocalizationPi`, `MittagLeffler`, `SimpleRing` and
`VaryingScalar`. The boundary clients are `CofinalGroupCompletionClient` and
`GradedStabilizationClient`. The reference omits `MonoidalGroupCompletion`,
`PrimeSpectrumFilteredColimits`, `Topology.Coinduced`, `Topology.TensorProduct`,
`RingTheory.KrullDimension.FiniteCapture`, `RingTheory.KrullDimension.DirectLimit`,
aggregate/test roots and
private/generated declarations. Use the [root module table](../README.md#modules)
and [mathematical guide](Guide.md) for the rest of the library.

Of the 96 selected sites, 63 have source docstrings. For the other 33,
[`scripts/api_notes.json`](../scripts/api_notes.json) supplies explanations
labeled **API note (not a source docstring)**. The signatures use doc-gen4's
visible display format, with whitespace normalized. Pretty-printing can omit
inferable types or depend on source notation; consult the linked Lean files
for authoritative statements, hypotheses and proofs. Display fragments need
not elaborate alone in a fresh namespace.

[api-manifest.json](api-manifest.json) indexes this selection by module and
name, records the display counts and checks the API document's content hash.
It is documentation metadata, not proof certification.

## Documentation checks and optional adapter

From the repository root, check the shipped Markdown, display inventory,
relative source links, supplementary notes and manifest without Lean or network
access:

```sh
python3 scripts/generate_api.py --check
python3 scripts/test_generate_api.py
```

[`scripts/generate_api.py`](../scripts/generate_api.py) also adapts supplied
doc-gen4 `doc-data` with `--native-data PATH --source-revision FULL_COMMIT`.
The revision identifies the supplied records' GitHub source links; it is not
written to the public manifest. The adapter checks selected names, kinds,
visible signature tokens and source ranges against this fixed display inventory.
Add `--check` to compare both documents without writing. Supplying records does
not run doc-gen4 or Lean, establish their origin, certify proofs or expand the
module selection. See [CREDITS.md](CREDITS.md) for contributor and tool credit.
