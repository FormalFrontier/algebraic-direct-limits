# SPDX-License-Identifier: Apache-2.0
# Authors: Formal Frontier Agents
"""Data-only adapter controls, not native doc-gen, Lean or proof verification.

Synthetic markup is reconstructed from the shipped display signatures. This
tests the bounded parser/inventory/refusal contract, not whether native records
are genuine; actual native generation and source binding are separate evidence.
"""
import copy
from html import escape
import json
from pathlib import Path
import re
import subprocess
import tempfile
import unittest

import generate_api as api

ROOT = Path(__file__).resolve().parent.parent
REV = "a" * 40


def fixture():
    pairs = re.findall(r"^### ([^\n]+)\n\n```lean\n([^\n]+)\n```",
                       (ROOT / "docs/API.md").read_text(), re.M)
    api.require(len(pairs) == 96 and len(dict(pairs)) == 96, "fixture headers differ")
    headers = dict(pairs)
    api.require(set(headers) == set(api.EXPECTED), "fixture names differ")
    records = {m: dict(name=m, declarations=[]) for m in api.MODULES}
    sources = {p: (ROOT / p).read_bytes() for p in api.INPUTS}
    for name, meta in api.EXPECTED.items():
        prefix = meta["display_kind"] + " " + name
        api.require(headers[name].startswith(prefix), "fixture identity")
        tail = headers[name][len(prefix):]
        header = ('<div class="decl_header"><span class="decl_kind">'
                  + escape(meta["display_kind"]) + '</span> '
                  + '<span class="decl_name">' + escape(name) + '</span>'
                  + '<span>' + escape(tail) + '</span></div>')
        module = meta["module"]
        path = api.MODULE_PATHS[module]
        records[module]["declarations"].append(dict(header=header, info=dict(
            name=name, kind=meta["kind"], line=1,
            sourceLink=api.GITHUB_SOURCE + REV + "/" + path + "#L1-L2",
            docLink="./" + module.replace(".", "/") + ".html#" + name,
            doc="" if name in api.NOTES else "Synthetic control, not a source docstring.")))
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
        self.assertEqual(facts["modules"], list(api.MODULES))
        self.assertEqual(facts["module_paths"], api.MODULE_PATHS)
        self.assertEqual(set(facts["inputs"]), set(api.INPUTS))
        self.assertEqual(len(facts["inputs"]), 15)
        self.assertEqual(len(facts["documentation_inputs"]), 3)
        self.assertEqual(facts["api_sha256"], api.digest(raw))
        self.assertFalse(facts["proof_certification"])
        self.assertIn(b"not a complete kernel-declaration census", raw)
        self.assertIn(b"../tests/CofinalGroupCompletionClient.lean#L1", raw)
        self.assertNotIn(b"../CofinalGroupCompletionClient.lean", raw)
        for module in ("AlgebraicDirectLimits", "ReadinessClient", "ReadinessTests"):
            self.assertEqual(records[module]["declarations"], [])
            self.assertIn(module, facts["native_record_sha256"])

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
        changes = [valid.replace("github.com", "github.com.evil.invalid"),
                   valid.replace("https://", "http://"),
                   valid.replace("/algebraic-direct-limits/", "/other/"),
                   valid.replace(REV, "b" * 40),
                   valid.replace("CofinalSequence.lean", "Other.lean"),
                   valid.split("#")[0], valid + "?query=1", valid + "\n",
                   valid.replace("#L1-L2", "#L2-L3"),
                   valid.replace("#L1-L2", "#L1-L0"),
                   valid.replace("#L1-L2", "#L1-L999999"),
                   valid.replace("#L1-L2", "#L01-L2"),
                   valid.replace("#L1-L2", "#L1"),
                   valid.replace("#L1-L2", "#L1-L2#extra")]
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

    def test_manifest_binding_all_fifteen_inputs(self):
        records, sources = fixture()
        _, raw = api.render(records, REV, sources)
        manifest = json.loads(raw)
        api.manifest_source_binding(manifest, REV, sources)
        for key, value in (("format", 2), ("format", True), ("docgen_revision", "b" * 40),
                           ("analyzed_source_revision", "b" * 40),
                           ("modules", list(api.MODULES[:-1])), ("inputs", {})):
            with self.subTest(key=key), self.assertRaises(ValueError):
                api.manifest_source_binding(dict(manifest, **{key: value}), REV, sources)
        for path in api.INPUTS:
            with self.subTest(path=path), self.assertRaises(ValueError):
                api.manifest_source_binding(manifest, REV, dict(sources, **{path: b"changed"}))

    def test_git_source_absence_presence_and_failure(self):
        with tempfile.TemporaryDirectory(prefix="adl-api-git-") as temp:
            root = Path(temp)
            self.assertFalse(api.git_source_available(root, REV))
            (root / ".git").write_text("invalid worktree marker\n")
            with self.assertRaisesRegex(ValueError, "refusing fallback"):
                api.git_source_available(root, REV)
            (root / ".git").unlink()
            subprocess.run(["git", "init", "-q", str(root)], check=True)
            self.assertFalse(api.git_source_available(root, REV))
            def git(*args, data=None):
                return subprocess.check_output(["git", "-C", str(root), *args], input=data).decode().strip()
            tree = git("mktree", data=b"")
            commit = git("-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid",
                         "commit-tree", tree, data=b"Synthetic fixture only\n")
            self.assertTrue(api.git_source_available(root, commit))
            with self.assertRaisesRegex(ValueError, "not a commit"):
                api.git_source_available(root, tree)


if __name__ == "__main__":
    unittest.main()
