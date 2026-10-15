#!/usr/bin/env python3
"""Retain exactly the h2 Wide parser functions with Lean-name-only renaming."""
from pathlib import Path
import argparse
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[4]
BASE = ROOT / "docs/research/100bit-spend-path-20261013"
EVIDENCE = BASE / "evidence/wide-parser-unrolled-extraction-20261015"
GENERATED = EVIDENCE / "attempt-h2/generated/AspisR1UnrolledWideParser"
SOURCE = BASE / "lean/UnrolledWideParserSource.lean"
PINS = {
    "attempt-h2/source/field.rs": "28df5a1abee13bde4b3aa9eeceb0489bedf00531f298460954a97661f5f1baea",
    "attempt-h2/source/field/wide_exact.rs": "6260fa9d179328714e7df59640abb7a76a326e98900993ce7d3da98c6411d10b",
    "attempt-h2/R1FieldParser.llbc": "e4ad5e110023a5767210887f465fb107d7454941886c3843dd172c21b749788f",
    "attempt-h2/generated/AspisR1UnrolledWideParser/Types.lean": "05dccb702ad73fb0e3ab446395e6f35203e71f397f50365bbf0892206333947e",
    "attempt-h2/generated/AspisR1UnrolledWideParser/Funs.lean": "89910b9399a5cbd2cd42ccd4aaa087c7f5daf5b3c0af89533930fc5a57e00829",
    "attempt-h2/generated/translation.json": "ef23f19be9611b75235d93008d7a70e4fd66e0b15ccfa3a432ebb4aaf86f25db",
}
RENAMES = {
    "field.wide_exact.WideExact.from_limbs": "field.wide_exact.WideExact.from_limbs_unrolled",
    "field.wide_exact.WideExact.from_le_bytes": "field.wide_exact.WideExact.from_le_bytes_unrolled",
    "parse_wide_exact_probe": "parse_unrolled_wide_exact_probe",
}


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def declaration_blocks(text: str) -> dict[str, str]:
    """Map generated declaration names to exact comment+declaration chunks."""
    namespace_match = re.search(r"(?m)^namespace ([A-Za-z0-9_.]+)$", text)
    assert namespace_match
    namespace = namespace_match.group(1)
    body = text.split(namespace_match.group(0) + "\n", 1)[1].split("\nend " + namespace, 1)[0]
    chunks = re.split(r"(?=\n/-- \[)", "\n" + body)
    out = {}
    for chunk in chunks:
        chunk = chunk.strip()
        if not chunk:
            continue
        match = re.search(r"(?m)^(?:@\[[^\n]*\]\s*)?(?:def|structure)\s+([A-Za-z0-9_.]+)", chunk)
        assert match, chunk[:200]
        name = match.group(1)
        assert name not in out, name
        out[name] = chunk
    return out


def imported_decl_unit(text: str, name: str) -> str:
    """Return exact generated comment and one declaration only, excluding following helpers."""
    decl = re.search(r"(?m)^(?:@\[[^\n]*\]\s*)?(?:def|structure)\s+" + re.escape(name) + r"\b", text)
    assert decl, name
    start = text.rfind("/-- [", 0, decl.start())
    assert start >= 0, name
    # Keep attributes between the generated comment and declaration.
    lines = text[start:].splitlines(True)
    out = []
    saw_decl = False
    is_structure = False
    for line in lines:
        if not saw_decl:
            out.append(line)
            if re.search(r"(?:def|structure)\s+" + re.escape(name) + r"\b", line):
                saw_decl = True
                is_structure = "structure " in line
                if not is_structure:
                    break
            continue
        if is_structure:
            if not line.startswith("  ") or not line.strip():
                break
            out.append(line)
        else:
            break
    result = "".join(out).strip()
    assert saw_decl
    return result


def body_after_generated_comment(block: str) -> tuple[str, str]:
    end = block.find("-/")
    assert end >= 0
    return block[:end + 2], block[end + 2:]


def renamed(block: str, mapping: dict[str, str]) -> str:
    comment, code = body_after_generated_comment(block)
    for old, new in mapping.items():
        code = code.replace(old, new)
    return comment + code


def expected_source(types: dict[str, str], funs: dict[str, str]) -> str:
    names = list(RENAMES)
    body = "\n\n".join(renamed(funs[name], RENAMES) for name in names)
    return """import R1CandidateWideParserSource

/-! The three unrolled Wide parser functions are retained from the h2 Aeneas
translation. Existing field types, `field.P`, and `BYTE_LEN` are reused from
`R1CandidateWideParserSource` after exact generated-block comparison. The
checker pins h2 source, LLBC, and generated metadata, and permits only the
listed Lean identifier relocations in the retained function blocks. This is
generated-source retention, not a Rust execution refinement or runtime change. -/
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048

namespace AspisR1CandidateParser

""" + body + "\n\nend AspisR1CandidateParser\n\n" + "\n".join(
        "#print axioms AspisR1CandidateParser." + name for name in RENAMES.values()
    ) + "\n"


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--write", action="store_true")
    args = ap.parse_args()
    for rel, expected in PINS.items():
        actual = sha((EVIDENCE / rel).read_bytes())
        assert actual == expected, f"pin mismatch {rel}: {actual}"
    generated_types = declaration_blocks((GENERATED / "Types.lean").read_text())
    generated_funs = declaration_blocks((GENERATED / "Funs.lean").read_text())
    # Reuse the declarations that already exist in the checked candidate parser imports.
    old_field = (BASE / "lean/CandidateFieldParsers.lean").read_text()
    old_wide = (BASE / "lean/CandidateWideParserSource.lean").read_text()
    shared = {
        "field.M31": old_field,
        "field.CM31": old_field,
        "field.QM31": old_field,
        "field.wide_exact.WideExact": old_wide,
    }
    for name, old_text in shared.items():
        assert imported_decl_unit(old_text, name) == generated_types[name], name
    for name, old_text in {
        "field.P": old_field,
        "field.wide_exact.WideExact.BYTE_LEN": old_wide,
    }.items():
        assert imported_decl_unit(old_text, name) == generated_funs[name], name
    assert set(generated_types) == set(shared)
    assert set(generated_funs) == {
        "field.wide_exact.WideExact.BYTE_LEN", "field.P", *RENAMES.keys()
    }
    metadata = json.loads((EVIDENCE / "attempt-h2/generated/translation.json").read_text())
    assert len(metadata["functions"]) == 3
    assert all(not item["is_opaque"] for item in metadata["functions"])
    assert {item["lean_name"].split("AspisR1UnrolledWideParser.", 1)[-1] for item in metadata["functions"]} == set(RENAMES)
    expected = expected_source(generated_types, generated_funs)
    if args.write:
        SOURCE.write_text(expected)
    assert SOURCE.read_text() == expected, "retained source differs from pinned generated blocks plus allowed renames"
    assert not re.search(r"(?m)^\s*(?:axiom|opaque|sorryAx)\b", expected)
    print(json.dumps({
        "shared_types_reused": len(shared),
        "shared_constants_reused": 2,
        "new_retained_functions": len(RENAMES),
        "nonopaque_translated_functions": len(metadata["functions"]),
        "retained_source_sha256": sha(SOURCE.read_bytes()),
        "all_checks_passed": True,
    }, indent=2))


if __name__ == "__main__":
    main()
