#!/usr/bin/env python3
"""Check retained M31 Aeneas declarations against pinned extraction c."""
from __future__ import annotations

import hashlib
from pathlib import Path
import sys


EXPECTED = {
    "Types.lean": "ef2b880ba62107f3924c1a0f77d9d942d23f9337bb20a7a6d1de09932c1d3da6",
    "Funs.lean": "3f1ff28ca0cbe86f10e598da520833ca5defd4fe6689099f13ff3053412c2ad3",
}


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def namespace_body(text: str) -> str:
    start = "namespace AspisR1M31Parser\n"
    end = "\nend AspisR1M31Parser"
    if text.count(start) != 1 or text.count(end) != 1:
        raise ValueError("unexpected generated namespace structure")
    return text.split(start, 1)[1].rsplit(end, 1)[0]


def main() -> int:
    root = Path(__file__).resolve().parents[4]
    evidence = root / "docs/research/100bit-spend-path-20261013/evidence/field-parser-extraction-20261014/c-generated/AspisR1M31Parser"
    retained = root / "docs/research/100bit-spend-path-20261013/lean/ExtractedM31Parser.lean"
    generated: dict[str, str] = {}
    for name, expected in EXPECTED.items():
        path = evidence / name
        actual = sha256(path)
        if actual != expected:
            raise SystemExit(f"source hash mismatch: {path}: {actual} != {expected}")
        generated[name] = path.read_text()

    source = retained.read_text()
    imports = [line for line in source.splitlines() if line.startswith("import ")]
    if imports != ["import Aeneas.Std.Primitives", "import Aeneas.Std.Scalar.CoreConvertNum"]:
        raise SystemExit(f"unexpected wrapper imports: {imports!r}")
    expected_body = namespace_body(generated["Types.lean"]) + "\n" + namespace_body(generated["Funs.lean"])
    actual_body = namespace_body(source)
    audit = "\n#print axioms field.P\n#print axioms field.M31.from_le_bytes\n#print axioms parse_m31_probe\n"
    if not actual_body.endswith(audit):
        raise SystemExit("expected public axiom audit commands are missing")
    actual_body = actual_body[:-len(audit)]
    if actual_body != expected_body:
        raise SystemExit("retained generated declarations differ from pinned source bodies")
    if "axiom " in source or "opaque " in source or "FunsExternal" in source:
        raise SystemExit("retained file contains an opaque/external declaration")
    print("PASS: pinned generated sources and retained declaration bodies match")
    print("PASS: retained module has no opaque/external declarations")
    return 0


if __name__ == "__main__":
    sys.exit(main())
