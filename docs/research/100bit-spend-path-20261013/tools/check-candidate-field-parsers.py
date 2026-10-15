#!/usr/bin/env python3
"""Verify retained candidate parser bodies and the LLBC Option tag row."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import re

REPO = Path(__file__).resolve().parents[4]
BASE = REPO / "docs/research/100bit-spend-path-20261013"
INPUT = BASE / "evidence/field-parser-candidate-retention-20261014/input/AspisR1CandidateParser"
TYPES = INPUT / "Types.lean"
FUNS = INPUT / "Funs.lean"
LLBC = INPUT / "R1FieldParser.llbc"
R259 = REPO / "docs/research/v8-full-view-zk-20260912/lean/AspisR259PrivateInputRaw.lean"
RETAINED = BASE / "lean/CandidateFieldParsers.lean"

PINS = {
    "Types.lean": "b1122429e934a22d9334ffe3c3d673cf10ef1873ef7e62643132139531e80067",
    "Funs.lean": "88817c538f86763ef18e8c09d2c68cbd1bdb673a63ba60da34b93bb52f15c776",
    "R1FieldParser.llbc": "cfddc4a69aa2e960727bfa83946f3bb6a406d181d6e9f1d79f0b7de286d5e75c",
    "translation.json": "53efcc94f36879348eb326c98e0d7096fce4f29e0c1caf6000957e52553ae40e",
    "AspisR259PrivateInputRaw.lean": "de1fa32d535bf4e3d10bac3235300b9c71d7ec1a2234fb9ebc91f8e56d8b5255",
}


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def namespace_body(text: str) -> str:
    start = "namespace AspisR1CandidateParser\n"
    end = "\nend AspisR1CandidateParser"
    if text.count(start) != 1 or text.count(end) != 1:
        raise SystemExit(f"expected exactly one candidate namespace in source: {start!r}")
    return text.split(start, 1)[1].split(end, 1)[0].strip("\n")


def support_block(text: str) -> str:
    start = "/-- Source-bound Option discriminant support:"
    stop = "\n\n/-- [core::option::"
    if text.count(start) != 1:
        raise SystemExit("expected exactly one pinned R259 Option support block")
    tail = text.split(start, 1)[1]
    if stop not in tail:
        raise SystemExit("could not delimit R259 Option support block")
    return (start + tail.split(stop, 1)[0]).rstrip("\n")


def check_llbc_option_row() -> None:
    document = json.loads(LLBC.read_text())
    translated = document["translated"]
    option_files = [f for f in translated["files"] if f["id"] == 1]
    if len(option_files) != 1 or option_files[0]["name"] != {"Local": "/rustc/library/core/src/option.rs"}:
        raise SystemExit("LLBC file id 1 is not the pinned core Option source")
    rows = [d for d in translated["type_decls"] if isinstance(d, dict) and d.get("item_meta", {}).get("lang_item") == "Option"]
    if len(rows) != 1:
        raise SystemExit("expected one LLBC Option lang-item declaration")
    row = rows[0]
    if row["def_id"] != 0 or row["item_meta"]["span"]["data"]["file_id"] != 1:
        raise SystemExit("LLBC Option row identity/file differs from pinned extraction")
    variants = row["kind"]["Enum"]
    expected = [(0, "None", {"Scalar": {"Signed": ["Isize", "0"]}}),
                (1, "Some", {"Scalar": {"Signed": ["Isize", "1"]}})]
    observed = [(v["id"], v["name"], v["discriminant"]) for v in variants]
    if observed != expected:
        raise SystemExit(f"LLBC Option discriminants changed: {observed!r}")
    print("LLBC Option tags: None=0#isize, Some=1#isize (def_id=0, file_id=1)")


def main() -> None:
    paths = {
        "Types.lean": TYPES,
        "Funs.lean": FUNS,
        "R1FieldParser.llbc": LLBC,
        "translation.json": INPUT / "translation.json",
        "AspisR259PrivateInputRaw.lean": R259,
    }
    for label, path in paths.items():
        if not path.is_file():
            raise SystemExit(f"missing pinned input: {path}")
        actual = digest(path)
        if actual != PINS[label]:
            raise SystemExit(f"{label} SHA-256 mismatch: {actual}")
        print(f"{label}: {actual}")

    types = TYPES.read_text()
    funs = FUNS.read_text()
    old_support = support_block(R259.read_text())
    retained = RETAINED.read_text()
    expected_body = "\n\n".join((namespace_body(types), old_support, namespace_body(funs)))
    if namespace_body(retained) != expected_body:
        raise SystemExit("retained namespace body differs from generated Types + R259 support + generated Funs")
    if re.search(r"(?m)^\s*(?:axiom|sorryAx|opaque)\b", retained):
        raise SystemExit("retained source contains an axiom/sorry/opaque declaration")
    if "import Aeneas\n" in retained:
        raise SystemExit("broad Aeneas umbrella import is forbidden; use pinned minimal imports")
    expected_audits = [
        "optionTag", "optionTag_none", "optionTag_some",
        "core.option.Option.Insts.CoreOpsTry_traitTry.branch",
        "core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual",
        "field.M31.from_le_bytes", "field.CM31.from_le_bytes", "field.QM31.from_le_bytes",
        "field.P", "parse_fields_probe",
    ]
    for name in expected_audits:
        if f"#print axioms AspisR1CandidateParser.{name}" not in retained:
            raise SystemExit(f"missing public axiom audit for {name}")
    check_llbc_option_row()
    print(f"retained body exact: {digest(RETAINED)}")


if __name__ == "__main__":
    main()
