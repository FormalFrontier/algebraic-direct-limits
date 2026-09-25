# API reference generation

[API.md](API.md) is the native-display reference for this library's seven
mathematical modules: 73 library display sites, plus 23 sites from two separate
boundary clients. It includes every name in the fixed display inventory, complete
native visible signatures and relative source links. The aggregate and the two
other test modules have no public native display sites but are included in the
twelve-module generation and provenance record. Client namespaces are not
re-exported by `AlgebraicDirectLimits`.

This is not a complete raw/kernel declaration census: private helpers, private
examples and compiler-generated declarations also need the separate proof audit.
Native display-site selection is distinct from both public-import and full-private
environment inventories. Read the [mathematical guide](Guide.md) for constructions
and hypotheses, and the root README for public import and build examples.

## What the adapter preserves

The adapter keeps all visible header tokens, including implicit arguments and
literal `noncomputable`/`abbrev` modifiers. It normalizes whitespace only, verifies
the exact module/name/kind map and checks each normalized signature against its
recorded SHA256. Native pretty-printing uses source namespaces, notation and type
inference. It may suppress inferable types, so these fragments are not promised
to elaborate alone in a fresh namespace; the linked source is authoritative.

Sixty-three display sites have native source docstrings. Thirty-three do not;
their supplementary explanations are authored in `scripts/api_notes.json` and
explicitly labeled **API note (not a source docstring)**. The generator refuses
unexpected missing or invented source docstrings. Notes and the mathematical
guide require semantic review just as other API documentation does. They do not
replace formal statements or add assumptions to them.

No dependency website, remote style, JavaScript, fonts or interactive search is
shipped. This reference does not purport to document Lean or all of mathlib.
It reproduces this project's own signatures/docstrings with local source links;
the third-party documentation implementation and its generated website/assets
are not bundled. See [CREDITS.md](CREDITS.md).

## Reproduce native records

Use a separate unchanged doc-gen4 checkout at
`97d4ecdfc8e09e7f511724c25e303d448de6a3db`, with its committed manifest and
Lean `v4.34.0-rc2`. Build that core-only tool with `lake build doc-gen4`; do not
alter this library's mathematical pins to install it. In this library's pinned
environment, first fetch the matching mathlib cache and build all default targets
as described in the root README. All twelve shipped modules must be built,
including `ReadinessTests`; the four test modules resolve below **tests/**.

The following uses Bash and Python3. Set the absolute path to the built native
executable. Use a fresh database and create its parent directories **before**
calling `single`, since the native SQLite opener does not create them:

```sh
docgen_executable=/absolute/path/to/doc-gen4
docs_work=$(mktemp -d)
mkdir "$docs_work/analysis" "$docs_work/rendered"
source_revision=$(python3 -c 'import json; print(json.load(open("docs/api-manifest.json"))["analyzed_source_revision"])')
for leaf in CofinalSequence CofinalGroupCompletion GradedStabilization LocalizationPi MittagLeffler SimpleRing VaryingScalar; do
  lake env "$docgen_executable" single --build "$docs_work/analysis" "AlgebraicDirectLimits.$leaf" api.db "https://github.com/FormalFrontier/algebraic-direct-limits/blob/$source_revision/AlgebraicDirectLimits/$leaf.lean"
done
lake env "$docgen_executable" single --build "$docs_work/analysis" AlgebraicDirectLimits api.db "https://github.com/FormalFrontier/algebraic-direct-limits/blob/$source_revision/AlgebraicDirectLimits.lean"
for module in CofinalGroupCompletionClient GradedStabilizationClient ReadinessClient ReadinessTests; do
  lake env "$docgen_executable" single --build "$docs_work/analysis" "$module" api.db "https://github.com/FormalFrontier/algebraic-direct-limits/blob/$source_revision/tests/$module.lean"
done
lake env "$docgen_executable" bibPrepass --build "$docs_work/rendered" --none
lake env "$docgen_executable" fromDb --build "$docs_work/rendered" --manifest "$docs_work/rendered/manifest.json" "$docs_work/analysis/api.db"
python3 -B scripts/generate_api.py --native-data "$docs_work/rendered/doc-data" --source-revision "$source_revision" --check
python3 -B scripts/test_generate_api.py
```

Run these commands in this project's `lake env`: the native executable carries
its implementation while resolving this project's built imports. Preserve both
resolved dependency manifests and record the effective search path. Native
warnings and failed attempts are findings, not silent passes. Do not substitute
a mutable branch for the full source commit. For reviewed regeneration after a
source change, use its actual full commit, renew the bounded inventory/notes as
necessary, and omit `--check` only after generating matching new native records.

The pinned native GitHub linker appends `#Lstart-Lend`. The adapter requires the
exact repository, full revision and module-specific path; a canonical positive
range starts at native `info.line` and ends within that source file. A test module
cannot silently use a root-level source path. A valid string does not establish
remote URL availability. Shipped Markdown links instead target the same checkout's
source, not an unpublished development URL.

## Reproduce without internal history

`api-manifest.json` records the analyzed source revision, all twelve source and
three Lean/Lake configuration/pin hashes, module/path mapping, tool revision,
three adapter/inventory/note hashes, canonical native-record hashes, exact display
names and output hash. Later documentation-only changes can be related through
those exact source/pin bytes; a changed mathematical source or pin requires new
native generation and renewed affected checks.

When the selected source Git object exists, the adapter checks every source/pin
against it and refuses any mismatch. A public release may have independent Git
ancestry: only Git's explicit `missing` result or a source-only tree with no `.git`
marker allows fallback to the committed manifest's exact fifteen source/pin
hashes, revision and module/tool selection. A broken Git command/repository or a
non-commit object refuses fallback. `--check` additionally compares both complete
generated files byte for byte, including all documentation/native-record hashes.

The data controls test this bounded contract with synthetic markup derived from
the shipped signatures; they are not native generation. Real records and command
receipts must be authenticated independently. Neither hashes nor this adapter
attest that supplied JSON came from doc-gen4, and neither is a kernel check,
copyright clearance or release decision. Complete mathematical/provenance review
and the separate raw/stored-proof audit remain distinct evidence.
