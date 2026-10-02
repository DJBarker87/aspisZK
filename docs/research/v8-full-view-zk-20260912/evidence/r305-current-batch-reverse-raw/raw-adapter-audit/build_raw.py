#!/usr/bin/env python3
"""Deterministically stage four unchanged R292 reverse-loop declarations."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parent
PROV = ROOT / "provenance"
FUNS = PROV / "R292Funs.input.lean"
OUT = ROOT / "AspisR305BatchReverseRaw.lean"
EXPECTED_INPUT_SHA = "4d40a5b7b540adec90efef80a5ed8a5b4403704b388506af21f357761d95aec4"
DECLS = [
    ("circle_norm.joined_inverse.line_norm.r110_norm.batch_loop2.body", 66),
    ("circle_norm.joined_inverse.line_norm.r110_norm.batch_loop2", 66),
    ("circle_norm.joined_inverse.line_norm.r110_norm.batch_loop3.body", 67),
    ("circle_norm.joined_inverse.line_norm.r110_norm.batch_loop3", 67),
]


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def line_number(text: str, offset: int) -> int:
    return text.count("\n", 0, offset) + 1


def extract(text: str, name: str, source_line: int) -> tuple[str, int, int]:
    # Include the source doc comment, rust_loop attribute, and full declaration.
    signature = re.compile(r"(?m)^def " + re.escape(name) + r"(?:\s|$)")
    hits = list(signature.finditer(text))
    if len(hits) != 1:
        raise RuntimeError(f"expected one declaration for {name}, found {len(hits)}")
    def_at = hits[0].start()
    start = text.rfind("/--", 0, def_at)
    if start < 0:
        raise RuntimeError(f"missing declaration doc comment for {name}")
    next_doc = text.find("/--", def_at)
    if next_doc < 0:
        next_doc = len(text)
    block = text[start:next_doc].rstrip("\n")
    expected = f"Source: '../r110_norm.rs', lines {source_line}:"
    if expected not in block:
        raise RuntimeError(f"source span mismatch for {name}; expected {expected!r}")
    return block, line_number(text, start), line_number(text, next_doc) - 1


def main() -> None:
    raw = FUNS.read_bytes()
    actual = sha256(raw)
    if actual != EXPECTED_INPUT_SHA:
        raise RuntimeError(f"input hash mismatch: {actual}")
    text = raw.decode()
    blocks = []
    records = []
    for name, source_line in DECLS:
        block, start, end = extract(text, name, source_line)
        blocks.append(block)
        records.append({
            "name": name,
            "generated_lines_inclusive": [start, end],
            "source_file": "r110_norm.rs",
            "source_line": source_line,
            "block_sha256": sha256(block.encode()),
            "exact_source_bytes_preserved": True,
        })

    prefix = """import Aeneas.Std
import AspisR249R110Raw

open Aeneas Aeneas.Std Result ControlFlow Error AspisR249R110Raw

noncomputable section
namespace AspisR305BatchReverseRaw

"""
    prints = "\n\n".join(f"#print axioms {name}" for name, _ in DECLS)
    output = prefix + "\n\n".join(blocks) + "\n\n" + prints + "\n\nend AspisR305BatchReverseRaw\n"
    OUT.write_text(output)
    result = {
        "task": "R305 raw reverse-loop declaration staging; no Lean compilation",
        "input": {"path": str(FUNS.relative_to(ROOT)), "sha256": actual},
        "output": {"path": OUT.name, "sha256": sha256(output.encode())},
        "declarations": records,
        "all_extracted_declaration_blocks_verbatim": True,
    }
    (ROOT / "staging-audit.json").write_text(json.dumps(result, indent=2) + "\n")


if __name__ == "__main__":
    main()
