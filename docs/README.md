# API reference

[API.md](API.md) retains a partial native-display reference for seven mathematical
modules: 73 library display sites and 23 sites from two boundary clients. These
sites are an authored display selection, **not** a theorem count, a declaration
census or documentation for the entire current library. Client namespaces are
not re-exported by `AlgebraicDirectLimits`.

The signatures and source docstrings come from historical native display records;
63 sites have genuine source docstrings. For the other 33 sites, explanations
written in [`scripts/api_notes.json`](../scripts/api_notes.json) are labeled
**API note (not a source docstring)** in [API.md](API.md). The adapter preserves
native visible signatures and their module/name mapping while normalizing
whitespace. Native pretty-printing can omit inferable types or depend on source
notation, so consult the linked Lean files for authoritative statements and
hypotheses. Neither the selection nor supplementary notes certify proofs.

The retained [manifest](api-manifest.json) labels its analyzed source revision
`96f074b6df709d2478d2565fb0acb3ddfc07fed4`. Its 15 recorded source/pin
hashes also match the [published initial library snapshot](https://github.com/FormalFrontier/algebraic-direct-limits/tree/d3e1787bbc962d028698af2259d2ef31212857d1):
this is **source-byte
equivalence**, not evidence that native records were generated at that public
commit. The seven documented leaves and boundary clients remain unchanged in
the current checkout, while the aggregate root, Lake configuration and test root
have changed. The reference does not cover the newer
[`MonoidalGroupCompletion`](../AlgebraicDirectLimits/MonoidalGroupCompletion.lean)
or [`PrimeSpectrumFilteredColimits`](../AlgebraicDirectLimits/PrimeSpectrumFilteredColimits.lean)
modules or their clients. See their source docstrings and the guide sections on
[monoidal object classes](Guide.md#monoidal-object-classes-and-actual-image-cofinality)
and [prime spectra](Guide.md#prime-spectra-of-filtered-colimits) for those APIs;
the [guide](Guide.md) also explains the other modules' scope.

## Optional adapter

[`scripts/generate_api.py`](../scripts/generate_api.py) accepts historical
doc-gen4 `doc-data` as `--native-data` and the manifest's exact analyzed revision
as `--source-revision`; `--check` compares the retained API and manifest without
rewriting them. Use a checkout with all 15 matching source/pin inputs (for example,
the published initial snapshot), **not** the changed current aggregate/test/Lake
inputs. Its recorded native tool revision is in the manifest; native input data
must be provided separately. The adapter validates source binding and rendered
records but cannot independently attest how supplied native data was generated.
No fresh native generation or full-current-module coverage is claimed. For
library builds and usage, consult the root README; for contributor and tool
attribution, see [CREDITS.md](CREDITS.md).
