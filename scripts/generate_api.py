#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Authors: Formal Frontier Agents
"""Check the partial API reference or adapt supplied doc-gen4 display records.

This fixed-library adapter validates documentation, not Lean proofs or the
origin of supplied records. See docs/README.md for its display contract.
"""
import argparse
import hashlib
from html.parser import HTMLParser
import json
from pathlib import Path
import re

MODULE_PATHS = {
    **{"AlgebraicDirectLimits." + name: "AlgebraicDirectLimits/" + name + ".lean"
       for name in ("CofinalSequence", "CofinalGroupCompletion", "GradedStabilization",
                    "LocalizationPi", "MittagLeffler", "SimpleRing", "VaryingScalar")},
    "AlgebraicDirectLimits": "AlgebraicDirectLimits.lean",
    **{name: "tests/" + name + ".lean" for name in
       ("CofinalGroupCompletionClient", "GradedStabilizationClient",
        "ReadinessClient", "ReadinessTests")},
}
MODULES = tuple(MODULE_PATHS)
INPUTS = tuple(MODULE_PATHS.values())
HERE = Path(__file__).resolve().parent
EXPECTED = json.loads((HERE / "api_inventory.json").read_bytes())
NOTES = json.loads((HERE / "api_notes.json").read_bytes())
GITHUB_SOURCE = "https://github.com/FormalFrontier/algebraic-direct-limits/blob/"

API_INTRO = """# API reference

This reference contains 73 library display sites and 23 boundary-client sites.
Import `AlgebraicDirectLimits` for the library; the test-target modules are separate.
The selection covers seven library modules, not every API or private/generated declaration.
Display-site counts are not a complete kernel-declaration census.

Headers below use native doc-gen4 display signatures, not complete declarations
with proof bodies. All visible tokens, including implicit parameters and
noncomputable/abbrev modifiers, are retained; whitespace alone is normalized.
Pretty-printing uses each source namespace, notation and type inference;
consult the linked source for suppressed inferred types and universe conventions.
These displayed fragments are not promised to elaborate alone in a fresh namespace.
Source links are relative to this same checkout.

The selected modules and names are indexed in [api-manifest.json](api-manifest.json).
See the [reference overview](README.md) and the [mathematical guide](Guide.md).
Where no source docstring exists, a separately authored **API note** is labeled explicitly.

"""


def require(ok, message):
    if not ok:
        raise ValueError(message)


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def source_range(info, revision, path, sources):
    """Validate supplied GitHub source links, not remote URL availability."""
    line_count = len(sources[path].splitlines())
    require(type(info["line"]) is int and 0 < info["line"] <= line_count,
            "invalid native source line")
    expected = GITHUB_SOURCE + revision + "/" + path
    match = re.fullmatch(re.escape(expected) + r"#L([1-9][0-9]*)-L([1-9][0-9]*)",
                         info["sourceLink"])
    require(match is not None, "native GitHub source URI or range differs")
    start, end = map(int, match.groups())
    require(start == info["line"] and start <= end <= line_count,
            "native GitHub range disagrees with source line/bounds")


class Header(HTMLParser):
    """Keep all visible text, including every implicit argument; discard markup."""

    def __init__(self, value):
        super().__init__(convert_charrefs=True)
        self.stack = []
        self.text = []
        self.kinds = []
        self.names = []
        self.feed(value)
        self.close()
        require(not self.stack, "unclosed native header")

    def handle_starttag(self, tag, attrs):
        require(tag in {"div", "span", "a"}, "unexpected native header tag")
        attrs = dict(attrs)
        require(not any(k.startswith("on") for k in attrs), "active header attribute")
        if tag == "div" and "decl_type" in attrs.get("class", "").split():
            self.text.append(" ")
        self.stack.append((tag, set(attrs.get("class", "").split())))

    def handle_endtag(self, tag):
        require(bool(self.stack) and self.stack[-1][0] == tag, "unbalanced native header")
        self.stack.pop()

    def handle_data(self, value):
        require(bool(self.stack) or not value.strip(), "text outside native header")
        self.text.append(value)
        if any("decl_kind" in classes for _, classes in self.stack):
            self.kinds.append(value)
        if any("decl_name" in classes for _, classes in self.stack):
            self.names.append(value)

    def handle_comment(self, _):
        raise ValueError("unexpected header comment")

    def handle_decl(self, _):
        raise ValueError("unexpected header declaration")

    def rendered(self):
        # Whitespace alone is normalized; all tokens and implicit binders remain.
        return " ".join("".join(self.text).split())


def render(records, revision, sources):
    require(re.fullmatch(r"[0-9a-f]{40}", revision) is not None, "full source revision required")
    require(set(records) == set(MODULES), "shipped module records differ")
    require(set(sources) == set(INPUTS), "source inventory differs")
    require(len(EXPECTED) == 96 and len(NOTES) == 33 and set(NOTES) <= set(EXPECTED),
            "bounded documentation inventory differs")
    rows = []
    found = {}
    for module in MODULES:
        record = records[module]
        require(record["name"] == module, "native module name differs")
        for row in record["declarations"]:
            info = row["info"]
            name, kind = info["name"], info["kind"]
            require(name in EXPECTED and EXPECTED[name]["kind"] == kind
                    and EXPECTED[name]["module"] == module, "unexpected public name/kind/module")
            require(name not in found, "duplicate public declaration")
            path = MODULE_PATHS[module]
            source_range(info, revision, path, sources)
            require(info["docLink"] == "./" + module.replace(".", "/") + ".html#" + name,
                    "native self link differs")
            header = Header(row["header"])
            require("".join(header.names) == name
                    and "".join(header.kinds) == EXPECTED[name]["display_kind"],
                    "native header identity differs")
            text = header.rendered()
            require(digest(text.encode()) == EXPECTED[name]["header_sha256"],
                    "native display signature differs, including implicit parameters")
            require("```" not in text and "```" not in info["doc"], "unsupported Markdown fence")
            require(bool(info["doc"].strip()) == (name not in NOTES),
                    "native docstring presence differs from source inventory")
            found[name] = EXPECTED[name]
            rows.append(dict(name=name, kind=kind, header=text, module=module,
                             doc=info["doc"].strip(), path=path, line=info["line"]))
    require(found == EXPECTED, "missing public declaration")
    rows.sort(key=lambda row: (MODULES.index(row["module"]), row["line"], row["name"]))
    lines = API_INTRO.splitlines()
    previous = None
    for row in rows:
        if row["module"] != previous:
            previous = row["module"]
            scope = "library" if previous.startswith("AlgebraicDirectLimits.") else "boundary client (not re-exported by library root)"
            lines += ["## " + previous, "", "Scope: " + scope + ".", ""]
        lines += ["### " + row["name"], "", "```lean", row["header"], "```", ""]
        if row["doc"]:
            lines += [row["doc"], ""]
        else:
            note = NOTES[row["name"]]
            require(isinstance(note, str) and bool(note.strip()) and "```" not in note,
                    "invalid authored API note")
            lines += ["**API note (not a source docstring):** " + note, ""]
        lines += [f"[Source](../{row['path']}#L{row['line']}) (native range begins at line {row['line']}).", ""]
    markdown = "\n".join(lines).encode()
    return markdown, display_manifest(markdown, [r["name"] for r in rows])


def display_manifest(markdown, names):
    """Index only the displayed selection; no producer receipts or source pins."""
    require(len(EXPECTED) == 96 and len(names) == 96 and len(set(names)) == 96
            and set(names) == set(EXPECTED), "display inventory differs")
    modules = [m for m in MODULES if any(EXPECTED[n]["module"] == m for n in names)]
    require(sum(EXPECTED[n]["module"].startswith("AlgebraicDirectLimits.") for n in names) == 73
            and len(modules) == 9, "display module/count inventory differs")
    manifest = dict(format=2, modules=modules,
                    module_paths={m: MODULE_PATHS[m] for m in modules},
                    library_display_sites=73, boundary_client_display_sites=23,
                    public_declarations=names, api_sha256=digest(markdown),
                    proof_certification=False)
    return (json.dumps(manifest, indent=2, sort_keys=True) + "\n").encode()


def check_documents(markdown, manifest, sources):
    """Data-only checks of the shipped display contract, without native records."""
    require(set(sources) == set(INPUTS), "source inventory differs")
    require(len(EXPECTED) == 96 and len(NOTES) == 33 and set(NOTES) <= set(EXPECTED),
            "bounded documentation inventory differs")
    text = markdown.decode()
    require(text.startswith(API_INTRO), "API overview differs")
    parts = re.split(r"^## ([^\n]+)\n\nScope: ([^\n]+)\.\n\n",
                     text[len(API_INTRO):], flags=re.M)
    require(parts[0] == "" and len(parts) > 1, "API module sections differ")
    block = re.compile(
        r"### ([^\n]+)\n\n```lean\n([^\n]+)\n```\n\n(.*?)\n\n"
        r"\[Source\]\(\.\./([^)#]+)#L([1-9][0-9]*)\) "
        r"\(native range begins at line \5\)\.\n(?:\n|$)", re.S)
    names, modules = [], []
    for i in range(1, len(parts), 3):
        module, scope, body = parts[i:i + 3]
        require(module in MODULES and module not in modules, "API module differs")
        modules.append(module)
        expected_scope = ("library" if module.startswith("AlgebraicDirectLimits.")
                          else "boundary client (not re-exported by library root)")
        require(scope == expected_scope, "API scope differs")
        offset, positions = 0, []
        for match in block.finditer(body):
            require(match.start() == offset, "unrecognized API content")
            offset = match.end()
            name, header, doc, path, line = match.groups()
            require(name in EXPECTED and name not in names and
                    EXPECTED[name]["module"] == module, "API name/module differs")
            require(digest(header.encode()) == EXPECTED[name]["header_sha256"],
                    "API display signature differs")
            require(path == MODULE_PATHS[module] and
                    int(line) <= len(sources[path].splitlines()), "API source link differs")
            if name in NOTES:
                require(doc == "**API note (not a source docstring):** " + NOTES[name],
                        "API note differs")
            else:
                require(bool(doc.strip()) and not doc.startswith("**API note"),
                        "API source docstring missing")
            names.append(name)
            positions.append((int(line), name))
        require(offset == len(body) and positions and positions == sorted(positions),
                "API content/order differs")
    require(set(names) == set(EXPECTED), "API display inventory differs")
    require(modules == [m for m in MODULES if any(EXPECTED[n]["module"] == m for n in names)],
            "API module order differs")
    require(manifest == display_manifest(markdown, names), "API manifest differs")
    return len(names)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--native-data", type=Path,
                   help="supplied fromDb output doc-data directory")
    p.add_argument("--source-revision", help="full revision in supplied source links")
    p.add_argument("--check", action="store_true", help="compare, never write")
    args = p.parse_args()
    root = Path(__file__).resolve().parent.parent
    sources = {path: (root / path).read_bytes() for path in INPUTS}
    if args.native_data is None:
        require(args.check and args.source_revision is None,
                "use --check alone, or supply --native-data and --source-revision")
        count = check_documents((root / "docs/API.md").read_bytes(),
                                (root / "docs/api-manifest.json").read_bytes(), sources)
        print(json.dumps(dict(status="matched", display_sites=count)))
        return
    require(args.source_revision is not None, "source revision required for supplied records")
    records = {m: json.loads((args.native_data / ("declaration-data-" + m + ".bmp")).read_bytes())
               for m in MODULES}
    api, manifest = render(records, args.source_revision, sources)
    check_documents(api, manifest, sources)
    for name, raw in [("API.md", api), ("api-manifest.json", manifest)]:
        target = root / "docs" / name
        if args.check:
            require(target.read_bytes() == raw, "generated file differs: " + name)
        else:
            target.write_bytes(raw)
    print(json.dumps(dict(status="matched" if args.check else "rendered",
                          display_sites=len(EXPECTED), api_sha256=digest(api))))


if __name__ == "__main__":
    main()
