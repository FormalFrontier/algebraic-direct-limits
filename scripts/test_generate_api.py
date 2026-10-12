# SPDX-License-Identifier: Apache-2.0
# Authors: Formal Frontier Agents
"""Data-only adapter controls, not native doc-gen, Lean or proof verification.

Synthetic markup is reconstructed from the shipped display signatures. This
tests the bounded parser/inventory/refusal contract and deterministic rendering,
not whether supplied native records are genuine or Lean proofs are valid.
"""
import copy
from html import escape
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import unittest

import generate_api as api

ROOT = Path(__file__).resolve().parent.parent
REV = "a" * 40


def fixture():
    pairs = re.findall(
        r"^### ([^\n]+)\n\n```lean\n([^\n]+)\n```\n\n(.*?)\n\n"
        r"\[Source\]\(\.\./([^#]+)#L([0-9]+)\) \([^\n]+\)",
        (ROOT / "docs/API.md").read_text(), re.M | re.S)
    api.require(len(pairs) == 96, "fixture sites differ")
    sites = {name: (header, doc, path, int(line)) for name, header, doc, path, line in pairs}
    api.require(len(sites) == 96 and set(sites) == set(api.EXPECTED), "fixture names differ")
    records = {m: dict(name=m, declarations=[]) for m in api.MODULES}
    sources = {p: (ROOT / p).read_bytes() for p in api.INPUTS}
    for name, meta in api.EXPECTED.items():
        visible, doc, path, line = sites[name]
        prefix = meta["display_kind"] + " " + name
        api.require(visible.startswith(prefix), "fixture identity")
        tail = visible[len(prefix):]
        header = ('<div class="decl_header"><span class="decl_kind">'
                  + escape(meta["display_kind"]) + '</span> '
                  + '<span class="decl_name">' + escape(name) + '</span>'
                  + '<span>' + escape(tail) + '</span></div>')
        module = meta["module"]
        api.require(path == api.MODULE_PATHS[module], "fixture source path")
        records[module]["declarations"].append(dict(header=header, info=dict(
            name=name, kind=meta["kind"], line=line,
            sourceLink=api.GITHUB_SOURCE + REV + "/" + path + f"#L{line}-L{line + 1}",
            docLink="./" + module.replace(".", "/") + ".html#" + name,
            doc="" if name in api.NOTES else doc)))
    return records, sources


def first(records):
    return records[api.MODULES[0]]["declarations"][0]


class Controls(unittest.TestCase):
    def test_complete_display_inventory(self):
        records, sources = fixture()
        raw, manifest = api.render(records, REV, sources)
        facts = json.loads(manifest)
        self.assertEqual(raw.count(b"\n### "), 96)
        self.assertEqual(raw.count(b"**API note (not a source docstring):**"), 33)
        self.assertEqual(facts["library_display_sites"], 73)
        self.assertEqual(facts["boundary_client_display_sites"], 23)
        selected = [m for m in api.MODULES if records[m]["declarations"]]
        self.assertEqual(len(selected), 9)
        self.assertEqual(facts["format"], 2)
        self.assertEqual(facts["modules"], selected)
        self.assertEqual(facts["module_paths"], {m: api.MODULE_PATHS[m] for m in selected})
        self.assertEqual(set(facts), {"format", "modules", "module_paths",
                         "library_display_sites", "boundary_client_display_sites",
                         "public_declarations", "api_sha256", "proof_certification"})
        self.assertEqual(facts["api_sha256"], api.digest(raw))
        self.assertFalse(facts["proof_certification"])
        self.assertIn(b"not a complete kernel-declaration census", raw)
        self.assertIn(b"../tests/CofinalGroupCompletionClient.lean#L", raw)
        self.assertNotIn(b"../CofinalGroupCompletionClient.lean", raw)
        for module in ("AlgebraicDirectLimits", "ReadinessClient", "ReadinessTests"):
            self.assertEqual(records[module]["declarations"], [])
            self.assertNotIn(module, facts["modules"])

    def test_all_literal_kinds_and_signature_tokens(self):
        records, sources = fixture()
        raw, _ = api.render(records, REV, sources)
        self.assertEqual(sum(m["kind"] != m["display_kind"] for m in api.EXPECTED.values()), 19)
        for module in api.MODULES:
            for row in records[module]["declarations"]:
                text = api.Header(row["header"]).rendered()
                self.assertIn(text.encode(), raw)
                self.assertEqual(api.digest(text.encode()),
                                 api.EXPECTED[row["info"]["name"]]["header_sha256"])
        self.assertIn(b"[IsDirectedOrder J] [Nonempty J]", raw)
        self.assertIn(b"noncomputable def", raw)
        self.assertIn(b"abbrev", raw)

    def test_parser_entities_and_nested_names(self):
        self.assertEqual(api.Header('<div><span>{A : Type u} [Module R A]</span> :'
                                    '<div class="decl_type">x &lt; y ∧ x ≤ y</div></div>').rendered(),
                         '{A : Type u} [Module R A] : x < y ∧ x ≤ y')
        self.assertEqual(api.Header('<span><span>DirectLimit</span>.<span>VaryingScalar</span></span>').rendered(),
                         'DirectLimit.VaryingScalar')

    def test_parser_rejects_invalid_markup(self):
        for text in ('<script>x</script>', '<div><span></div>', '<div>unclosed',
                     '<span onclick="x">x</span>', '<div><!--comment--></div>',
                     '<!DOCTYPE html>', 'outside', '<div/>tail'):
            with self.subTest(text=text), self.assertRaises(ValueError):
                api.Header(text)

    def test_module_name_kind_and_completeness_refusals(self):
        mutations = [
            lambda r: r.pop(api.MODULES[-1]),
            lambda r: r.update(Extra=dict(name="Extra", declarations=[])),
            lambda r: r[api.MODULES[0]]["declarations"].pop(),
            lambda r: r[api.MODULES[0]]["declarations"].append(copy.deepcopy(first(r))),
            lambda r: r[api.MODULES[1]]["declarations"].append(copy.deepcopy(first(r))),
            lambda r: r[api.MODULES[0]].update(name="Wrong"),
        ]
        for key, value in (("name", "Wrong"), ("kind", "axiom"), ("line", 0),
                           ("line", 999999), ("line", True), ("docLink", "wrong"),
                           ("doc", "```inject")):
            mutations.append(lambda r, k=key, v=value: first(r)["info"].update({k: v}))
        for index, mutate in enumerate(mutations):
            with self.subTest(index=index):
                records, sources = fixture()
                mutate(records)
                with self.assertRaises(ValueError):
                    api.render(records, REV, sources)

    def test_signatures_refuse_implicit_and_modifier_loss(self):
        for needle in ("[IsDirectedOrder J]", "noncomputable ", "abbrev"):
            records, sources = fixture()
            row = next(row for r in records.values() for row in r["declarations"]
                       if needle in row["header"])
            replacement = "def" if needle == "abbrev" else ""
            row["header"] = row["header"].replace(needle, replacement)
            with self.subTest(needle=needle), self.assertRaises(ValueError):
                api.render(records, REV, sources)
        records, sources = fixture()
        first(records)["header"] = first(records)["header"].replace("Type u", "Type v")
        with self.assertRaises(ValueError):
            api.render(records, REV, sources)

    def test_docstring_absence_is_not_silently_fabricated(self):
        for absent in (False, True):
            records, sources = fixture()
            row = next(row for r in records.values() for row in r["declarations"]
                       if (row["info"]["name"] in api.NOTES) == absent)
            row["info"]["doc"] = "fabricated" if absent else ""
            with self.subTest(absent=absent), self.assertRaises(ValueError):
                api.render(records, REV, sources)

    def test_source_url_ranges_and_test_paths(self):
        records, sources = fixture()
        valid = first(records)["info"]["sourceLink"]
        line = first(records)["info"]["line"]
        span = f"#L{line}-L{line + 1}"
        changes = [valid.replace("github.com", "github.com.evil.invalid"),
                   valid.replace("https://", "http://"),
                   valid.replace("/algebraic-direct-limits/", "/other/"),
                   valid.replace(REV, "b" * 40),
                   valid.replace("CofinalSequence.lean", "Other.lean"),
                   valid.split("#")[0], valid + "?query=1", valid + "\n",
                   valid.replace(span, f"#L{line + 1}-L{line + 2}"),
                   valid.replace(span, f"#L{line}-L0"),
                   valid.replace(span, f"#L{line}-L999999"),
                   valid.replace(span, f"#L0{line}-L{line + 1}"),
                   valid.replace(span, f"#L{line}"),
                   valid + "#extra"]
        for value in changes:
            with self.subTest(value=value):
                altered = copy.deepcopy(records)
                first(altered)["info"]["sourceLink"] = value
                with self.assertRaises(ValueError): api.render(altered, REV, sources)
        row = records["CofinalGroupCompletionClient"]["declarations"][0]
        row["info"]["sourceLink"] = row["info"]["sourceLink"].replace("/tests/", "/")
        with self.assertRaises(ValueError): api.render(records, REV, sources)

    def test_source_inventory_and_full_revision(self):
        records, sources = fixture()
        for revision in ("main", "a" * 39, "A" * 40, "-" * 40):
            with self.subTest(revision=revision), self.assertRaises(ValueError):
                api.render(records, revision, sources)
        for path in sources:
            altered = dict(sources)
            altered.pop(path)
            with self.subTest(path=path), self.assertRaises(ValueError):
                api.render(records, REV, altered)

    def test_deterministic_render_and_shipped_document_check(self):
        records, sources = fixture()
        raw, manifest = api.render(records, REV, sources)
        self.assertEqual((raw, manifest), api.render(copy.deepcopy(records), REV, sources))
        self.assertEqual(raw, (ROOT / "docs/API.md").read_bytes())
        self.assertEqual(manifest, (ROOT / "docs/api-manifest.json").read_bytes())
        self.assertEqual(api.check_documents(raw, manifest, sources), 96)
        reordered = {m: dict(name=m, declarations=list(reversed(r["declarations"])))
                     for m, r in reversed(list(records.items()))}
        self.assertEqual((raw, manifest), api.render(reordered, REV, sources))

    def test_public_manifest_schema_and_content_refusals(self):
        records, sources = fixture()
        raw, encoded = api.render(records, REV, sources)
        manifest = json.loads(encoded)
        changes = [("format", 1), ("format", True), ("modules", []),
                   ("module_paths", {}), ("library_display_sites", 0),
                   ("boundary_client_display_sites", 0), ("public_declarations", []),
                   ("api_sha256", "0" * 64), ("proof_certification", True),
                   ("analyzed_source_revision", REV), ("native_record_sha256", {})]
        for key, value in changes:
            altered = (json.dumps(dict(manifest, **{key: value}),
                                  indent=2, sort_keys=True) + "\n").encode()
            with self.subTest(key=key, value=value), self.assertRaises(ValueError):
                api.check_documents(raw, altered, sources)
        for invalid in (b"{}", b"null", b"", encoded[:-1]):
            with self.subTest(invalid=invalid[:20]), self.assertRaises(ValueError):
                api.check_documents(raw, invalid, sources)

    def test_shipped_math_display_and_source_link_refusals(self):
        records, sources = fixture()
        raw, manifest = api.render(records, REV, sources)
        # Keep the manifest synchronized in these cases: the structural checks,
        # not just the content digest, must reject damaged mathematical displays.
        names = json.loads(manifest)["public_declarations"]
        mutations = [
            raw.replace(b"[IsDirectedOrder J] ", b"", 1),
            raw.replace(b"### IsCofinal.exists_monotone_nat",
                        b"### IsCofinal.exists_final_functor_nat", 1),
            raw.replace(b"../AlgebraicDirectLimits/CofinalSequence.lean#L31",
                        b"../AlgebraicDirectLimits/Other.lean#L31", 1),
            raw.replace(b"#L31) (native range begins at line 31)",
                        b"#L999999) (native range begins at line 999999)", 1),
            raw.replace(b"Scope: library.", b"Scope: boundary client.", 1),
            raw.replace(b"## AlgebraicDirectLimits.CofinalSequence",
                        b"## AlgebraicDirectLimits.VaryingScalar", 1),
            raw.replace(b"**API note (not a source docstring):**",
                        b"**Unlabeled explanation:**", 1),
            raw.replace(b"[Source]", b"[Unknown]", 1),
            raw + b"unrecognized trailing content\n",
            api.API_INTRO.encode(), b"",
        ]
        # Remove one complete site, leaving a nonempty but incomplete selection.
        begin = raw.index(b"### IsCofinal.exists_monotone_nat")
        end = raw.index(b"### IsCofinal.exists_final_functor_nat")
        mutations.append(raw[:begin] + raw[end:])
        for index, altered in enumerate(mutations):
            with self.subTest(index=index), self.assertRaises(ValueError):
                api.check_documents(altered, api.display_manifest(altered, names), sources)
        bad_sources = dict(sources)
        bad_sources[api.MODULE_PATHS[api.MODULES[0]]] = b""
        with self.assertRaises(ValueError): api.check_documents(raw, manifest, bad_sources)
        bad_sources.pop(api.INPUTS[-1])
        with self.assertRaises(ValueError): api.check_documents(raw, manifest, bad_sources)

    def test_document_check_cli_and_optional_adapter_comparison(self):
        command = [sys.executable, str(ROOT / "scripts/generate_api.py"), "--check"]
        output = subprocess.check_output(command, text=True)
        self.assertEqual(json.loads(output), dict(status="matched", display_sites=96))
        records, _ = fixture()
        # These are synthetic test controls, never native generation output.
        with tempfile.TemporaryDirectory(prefix="adl-display-controls-") as temp:
            for module, record in records.items():
                (Path(temp) / ("declaration-data-" + module + ".bmp")).write_text(json.dumps(record))
            output = subprocess.check_output(command + ["--native-data", temp,
                                             "--source-revision", REV], text=True)
            self.assertEqual(json.loads(output)["status"], "matched")
            first(records)["header"] = first(records)["header"].replace("Type u", "Type v")
            (Path(temp) / ("declaration-data-" + api.MODULES[0] + ".bmp")).write_text(
                json.dumps(records[api.MODULES[0]]))
            result = subprocess.run(command + ["--native-data", temp,
                                    "--source-revision", REV], capture_output=True, text=True)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("native display signature differs", result.stderr)


if __name__ == "__main__":
    unittest.main()
