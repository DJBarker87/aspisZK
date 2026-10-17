#!/usr/bin/env python3
"""Build the pure source cut for Pool's post-verification lane constructor.

Only names/types unavailable to the standalone Charon crate are adapted.
The function control-flow/body is copied from the pinned production source.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[5]
OUT = Path(__file__).resolve().parent
SOURCES = {
    "pair_forest": ROOT / "programs/aspis-pool/src/pair_forest.rs",
    "pair_tree": ROOT / "crates/aspis-statement/src/pool_v1/incremental_merkle.rs",
    "pair_accounts": ROOT / "crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs",
    "pair_terminal": ROOT / "crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs",
    "pair_afterstate": ROOT / "crates/aspis-statement/src/pool_v1/pair_terminal.rs",
    "transition_kind": ROOT / "crates/aspis-statement/src/pool_v1/historical_anchor.rs",
    "m31": ROOT / "crates/aspis-core/src/field.rs",
}


def decl(path: Path, anchor: str) -> tuple[str, int, int]:
    lines = path.read_text().splitlines(keepends=True)
    start = next(i for i, line in enumerate(lines) if anchor in line)
    # Include derive/doc attributes directly above the declaration.
    while start and (lines[start - 1].lstrip().startswith("#") or
                     lines[start - 1].lstrip().startswith("///") or
                     not lines[start - 1].strip()):
        start -= 1
    if "pub struct M31(" in lines[next(i for i in range(start, len(lines)) if anchor in lines[i])]:
        end = next(i for i in range(start, len(lines)) if ";" in lines[i])
        return "".join(lines[start:end + 1]), start + 1, end + 1
    depth = 0
    opened = False
    end = start
    for end in range(start, len(lines)):
        for ch in lines[end]:
            if ch == "{":
                depth += 1
                opened = True
            elif ch == "}":
                depth -= 1
                if opened and depth == 0:
                    return "".join(lines[start:end + 1]), start + 1, end + 1
    raise RuntimeError(f"declaration not closed: {anchor}")


def function(path: Path, anchor: str) -> tuple[str, int, int]:
    lines = path.read_text().splitlines(keepends=True)
    start = next(i for i, line in enumerate(lines) if anchor in line)
    while start and (lines[start - 1].lstrip().startswith("#") or
                     lines[start - 1].lstrip().startswith("///") or
                     not lines[start - 1].strip()):
        start -= 1
    depth = 0
    opened = False
    for end in range(start, len(lines)):
        for ch in lines[end]:
            if ch == "{":
                depth += 1
                opened = True
            elif ch == "}":
                depth -= 1
                if opened and depth == 0:
                    return "".join(lines[start:end + 1]), start + 1, end + 1
    raise RuntimeError(f"function not closed: {anchor}")


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def main() -> None:
    pieces: list[tuple[str, Path, int, int]] = []
    for key, anchor in [
        ("m31", "pub struct M31"),
        ("transition_kind", "pub enum PoolV1TransitionKind"),
        ("pair_tree", "pub struct IncrementalMerkleTreeV1"),
        ("pair_afterstate", "pub struct PoolV1PairVerifiedAfterstateV1"),
        ("pair_accounts", "pub struct PoolV1PairForestLaneStateV1"),
        ("pair_terminal", "pub struct PoolV1PairForestTerminalResultV1"),
    ]:
        text, first, last = decl(SOURCES[key], anchor)
        pieces.append((text, SOURCES[key], first, last))
    body, first, last = function(SOURCES["pair_forest"], "fn next_pair_forest_lane_v1(")
    pieces.append((body, SOURCES["pair_forest"], first, last))

    # Isolated dependency shims: preserve the function's Rust body while
    # replacing its Solana error conversion with the corresponding one-variant
    # local carrier and making the production empty-root constant an explicit
    # input. These are the only function/type-context adaptations.
    prelude = """#![allow(dead_code)]
use core::convert::From;

pub const POOL_V1_TREE_DEPTH: usize = 20;
pub const POOL_V1_PAIR_TREE_DEPTH: usize = 20;
pub type Digest = [M31; 8];

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PoolV1ProgramError { StateHistoryMismatch }
pub type ProgramError = PoolV1ProgramError;

"""
    rendered: list[str] = [prelude]
    source_records = []
    for text, path, first, last in pieces:
        original = text
        transformed = text
        transformed = transformed.replace("super::POOL_V1_PAIR_TREE_DEPTH", "POOL_V1_PAIR_TREE_DEPTH")
        transformed = transformed.replace("aspis_statement::pool_v1::PoolV1PairForestTerminalResultV1", "PoolV1PairForestTerminalResultV1")
        transformed = transformed.replace("POOL_V1_PAIR_EMPTY_ROOTS[level]", "pair_empty_roots[level]")
        if "fn next_pair_forest_lane_v1(" in transformed:
            transformed = transformed.replace(
                "    result: &PoolV1PairForestTerminalResultV1,\n",
                "    pair_empty_roots: &[Digest; POOL_V1_PAIR_TREE_DEPTH + 1],\n    result: &PoolV1PairForestTerminalResultV1,\n",
                1,
            )
        rendered.append(transformed + "\n\n")
        source_records.append({
            "source": str(path.relative_to(ROOT)),
            "source_file_sha256": sha(path.read_bytes()),
            "line_start": first,
            "line_end_exclusive": last + 1,
            "anchor_fragment_sha256": sha(original.encode()),
            "cut_fragment_sha256": sha(transformed.encode()),
            "adaptations": [
                "POOL_V1_PAIR_EMPTY_ROOTS[level] -> explicit pair_empty_roots[level] argument",
                "production qualified result type -> copied local result record",
                "afterstate nested depth path -> local depth constant",
            ] if "fn next_pair_forest_lane_v1(" in original else [],
        })
    output = "".join(rendered).encode()
    (OUT / "lib.rs").write_bytes(output)
    (OUT / "source-manifest.json").write_text(json.dumps({
        "crate": "pair-forest-lane-write-source-cut",
        "purpose": "Aeneas source cut for next_pair_forest_lane_v1's successful record projections",
        "source_root": str(ROOT),
        "production_pair_forest_sha256": sha(SOURCES["pair_forest"].read_bytes()),
        "output_lib_sha256": sha(output),
        "records": source_records,
    }, indent=2) + "\n")


if __name__ == "__main__":
    main()
