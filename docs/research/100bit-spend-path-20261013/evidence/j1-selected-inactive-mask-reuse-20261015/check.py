#!/usr/bin/env python3
"""Read-only exact literal comparison of the R0 Rust and old Lean row masks."""
from __future__ import annotations
import ast
import hashlib
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[5]
RUST_REL = Path("crates/aspis-core/src/r0/opening.rs")
COPY_REL = Path("docs/research/v8-r0-sem-proof-20261008/lean/R0P/CopyConstants.lean")
T163_REL = Path("docs/research/v8-full-view-zk-20260912/lean/AspisV8R19/T163SourceTable.lean")
EXPECTED_HASHES = {
    str(RUST_REL): "349dc999c1165e9e3be07a840ce99dc7a0b567c7a0545088baea80894476ee7d",
    str(COPY_REL): "cca9bdd0d2988693652d23010e068155abe0bc52fe36d030dbd8c163fe4f4f68",
    str(T163_REL): "6aaf8bc2e1fce9a5a0116eac8eda44b5ca2032e5dcb5d2824587e05bf8ff3795",
}


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def exactly_one(pattern: str, text: str, label: str) -> re.Match[str]:
    matches = list(re.finditer(pattern, text, re.S))
    if len(matches) != 1:
        raise ValueError(f"expected exactly one {label}; found {len(matches)}")
    return matches[0]


def main() -> int:
    rust_path, copy_path, t163_path = (ROOT / RUST_REL, ROOT / COPY_REL, ROOT / T163_REL)
    source_paths = {str(RUST_REL): rust_path, str(COPY_REL): copy_path, str(T163_REL): t163_path}
    hashes = {str(rel): digest(path) for rel, path in source_paths.items()}
    for rel, expected in EXPECTED_HASHES.items():
        if hashes[rel] != expected:
            raise ValueError(f"source hash changed for {rel}: {hashes[rel]} != {expected}")

    rust = rust_path.read_text()
    copy = copy_path.read_text()
    t163 = t163_path.read_text()
    rust_match = exactly_one(r"pub const COPY_ACTIVE_ROW_MASKS: \[u16; 64\] = \[(.*?)\];", rust, "Rust COPY_ACTIVE_ROW_MASKS")
    copy_match = exactly_one(r"def copyActiveRowMasks : Fin 64 → Nat := !\[(.*?)\]", copy, "Lean copyActiveRowMasks")
    table_match = exactly_one(r"def inactiveBlocks : List \(List Bool\) := (\[\[.*?\]\])\ndef forward", t163, "T163 inactiveBlocks")
    rust_masks = [int(x) for x in re.findall(r"\d+", rust_match.group(1))]
    copy_masks = [int(x) for x in re.findall(r"\d+", copy_match.group(1))]
    old_blocks = ast.literal_eval(re.sub(r"\btrue\b", "True", re.sub(r"\bfalse\b", "False", table_match.group(1))))
    old_inactive = [entry for block in old_blocks for entry in block]
    if len(rust_masks) != 64 or len(copy_masks) != 64 or len(old_blocks) != 32 or any(len(block) != 32 for block in old_blocks):
        raise ValueError("unexpected mask/table dimensions")
    rust_inactive = [((rust_masks[row // 16] >> (row % 16)) & 1) == 0 for row in range(1024)]
    copy_inactive = [((copy_masks[row // 16] >> (row % 16)) & 1) == 0 for row in range(1024)]
    if rust_masks != copy_masks:
        raise ValueError("64 Rust and Lean mask values differ")
    if rust_inactive != old_inactive:
        differing = [i for i, (a, b) in enumerate(zip(rust_inactive, old_inactive)) if a != b]
        raise ValueError(f"Rust/T163 inactive booleans differ at rows {differing}")
    if rust_inactive != copy_inactive:
        differing = [i for i, (a, b) in enumerate(zip(rust_inactive, copy_inactive)) if a != b]
        raise ValueError(f"Rust/Copy inactive booleans differ at rows {differing}")

    out = {
        "result": "pass",
        "scope": "literal numeric/definition comparison only; no Rust refinement is established",
        "sources": {
            str(RUST_REL): {"sha256": hashes[str(RUST_REL)], "declarations": ["COPY_ACTIVE_ROW_MASKS", "inactive"]},
            str(COPY_REL): {"sha256": hashes[str(COPY_REL)], "declarations": ["copyActiveRowMasks", "CopyActiveRow", "copyInactiveRows"]},
            str(T163_REL): {"sha256": hashes[str(T163_REL)], "declarations": ["inactiveBlocks", "isInactive", "inactive"]},
        },
        "comparison": {
            "mask_count": 64,
            "rust_masks_equal_copyActiveRowMasks": True,
            "rows_compared": 1024,
            "rust_inactive_formula": "((COPY_ACTIVE_ROW_MASKS[r / 16] >> (r % 16)) & 1) == 0",
            "T163_inactive_formula": "inactiveBlocks.getD (r / 32) [].getD (r % 32) false",
            "all_rust_inactive_values_equal_T163_isInactive": True,
            "all_rust_inactive_values_equal_R0P_copyInactiveRows": True,
            "inactive_row_count": sum(rust_inactive),
        },
        "reusable_lean_names": [
            "R0P.copyActiveRowMasks",
            "R0P.CopyActiveRow",
            "R0P.copyInactiveRows",
            "AspisR19.T163SourceTable.inactiveBlocks",
            "AspisR19.T163SourceTable.isInactive",
            "AspisR19.T163SourceTable.inactive",
        ],
    }
    print(json.dumps(out, indent=2))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except Exception as exc:
        print(f"mask comparison failed: {exc}", file=sys.stderr)
        raise SystemExit(1)
