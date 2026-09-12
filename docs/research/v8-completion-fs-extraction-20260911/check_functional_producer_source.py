#!/usr/bin/env python3
"""Fail-closed constant/layout check for the Lean functional-byte constructor."""

from __future__ import annotations

import re
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[3]
LEAN = ROOT / "docs/research/v8-completion-fs-extraction-20260911/lean/SameBodyFunctionalProducerSource.lean"
RUST = ROOT / "docs/research/v8-no-work-100-20260907/experiments/structured_weights.rs"
CONSTANTS = ROOT / "crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal_constants.rs"


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def decimal_list(source: str, name: str) -> list[int]:
    match = re.search(rf"def\s+{re.escape(name)}\b.*?:=.*?\[(.*?)\]", source, re.S)
    require(match is not None, f"missing Lean list {name}")
    return [int(value) for value in re.findall(r"\d+", match.group(1))]


def rust_array(source: str, name: str, length: int) -> list[int]:
    match = re.search(
        rf"{re.escape(name)}:\s*\[[^;]+;\s*{length}\]\s*=\s*\[(.*?)\];",
        source,
        re.S,
    )
    require(match is not None, f"missing Rust array {name}")
    return [int(value.strip()) for value in match.group(1).split(",") if value.strip()]


def main() -> int:
    lean = LEAN.read_text()
    rust = RUST.read_text()
    constants = CONSTANTS.read_text()

    prefix = bytes(decimal_list(lean, "functionalPrefix"))
    rust_prefix_match = re.search(r'let mut desc=b"([^"]+)"\.to_vec\(\);', rust)
    require(rust_prefix_match is not None, "missing Rust functional prefix")
    rust_prefix = rust_prefix_match.group(1).encode("ascii")
    require(prefix == rust_prefix, "functional prefix bytes differ")
    require(len(prefix) == 43, f"functional prefix length is {len(prefix)}, expected 43")

    groups = decimal_list(lean, "inactiveGroups")
    masks = decimal_list(lean, "inactiveMasks")
    rust_groups = rust_array(constants, "INACTIVE_ROW_GROUPS", 64)
    rust_masks = rust_array(constants, "INACTIVE_GROUP_MASKS", 7)
    require(groups == rust_groups, "64-entry inactive group list differs")
    require(masks == rust_masks, "7-entry inactive mask list differs")

    lean_mask_bytes = b"".join(masks[group].to_bytes(2, "little") for group in groups)
    rust_mask_bytes = b"".join(rust_masks[group].to_bytes(2, "little") for group in rust_groups)
    require(lean_mask_bytes == rust_mask_bytes, "generated u16-LE mask bytes differ")
    require(len(lean_mask_bytes) == 128, "mask byte length is not 128")

    metadata = "[20,22,10,4,4,ifvalue.prepared.useXthen1else0]"
    require(metadata in re.sub(r"\s+", "", lean), "Lean six-byte metadata layout differs")
    require("desc.extend([20,22,10,4,4,use_xasu8]);" in re.sub(r"\s+", "", rust),
            "Rust six-byte metadata layout differs")

    lean_order = [
        "encodeList (List.ofFn z)",
        "encodeList (List.ofFn value.prepared.scales)",
        "encodeList (List.ofFn value.prepared.abc)",
        "encodeList [value.prepared.intercept, value.prepared.slope]",
        "encodeList [data.x0, data.y0, data.x1, data.y1, data.gamma]",
        "inactiveMaskBytes",
    ]
    rust_order = [
        "desc.extend(bytes(&d.z))",
        "desc.extend(bytes(&scales))",
        "desc.extend(bytes(&abc))",
        "desc.extend(bytes(&iv))",
        "desc.extend(bytes(&[s0.x,s0.y,s1.x,s1.y,gamma]))",
        "for j in 0..64{desc.extend(masks[groups[j] as usize].to_le_bytes());}",
    ]
    lean_description = lean[lean.index("def descriptionBytes") : lean.index("def encoded")]
    require(all(lean_description.find(a) < lean_description.find(b)
                for a, b in zip(lean_order, lean_order[1:])),
            "Lean description fields are out of order")
    require(all(rust.find(a) < rust.find(b) for a, b in zip(rust_order, rust_order[1:])),
            "Rust description fields are out of order")

    total = len(prefix) + 6 + (10 + 3 + 3 + 2 + 5) * 16 + len(lean_mask_bytes)
    require(total == 545, f"computed description length is {total}, expected 545")

    print(
        "PASS functional_producer_source "
        f"prefix={len(prefix)} metadata=6 groups={len(groups)} masks={len(masks)} "
        f"mask_bytes={len(lean_mask_bytes)} total={total} order=matched"
    )
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (AssertionError, OSError, ValueError) as error:
        print(f"FAIL functional_producer_source: {error}", file=sys.stderr)
        raise SystemExit(1)
