#!/usr/bin/env python3
"""Check the narrowly documented Aeneas-to-Lean fibre_point adapter.

This does not validate the mathematics of the CM31 implementation or prove
table/domain exponent correspondence. It checks that the adapted Lean owner
retains the extracted control flow, ordered literal tables, and named array
length arguments, with only CM31 new/mul made explicit as an operation record.
"""
from __future__ import annotations

import hashlib
import argparse
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit(f"FAIL: {message}")


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def balanced_brackets(text: str, start: int, left: str = "[", right: str = "]") -> str:
    depth = 0
    for i in range(start, len(text)):
        if text[i] == left:
            depth += 1
        elif text[i] == right:
            depth -= 1
            if depth == 0:
                return text[start : i + 1]
    raise ValueError(f"unclosed {left} starting at {start}")


PAIR = re.compile(r"\(\s*(\d+)#u32\s*,\s*(\d+)#u32\s*\)")


def raw_table_pairs(text: str, name: str) -> list[tuple[int, int]]:
    marker = f"def fast_domain.{name} :"
    pos = text.index(marker)
    array_make = text.index("Array.make", pos)
    list_start = text.index("[", array_make)
    body = balanced_brackets(text, list_start)
    pairs = [(int(a), int(b)) for a, b in PAIR.findall(body)]
    require(len(pairs) == 512, f"raw {name} has {len(pairs)} pairs, expected 512")
    return pairs


def adapted_chunk_pairs(text: str, prefix: str) -> tuple[list[tuple[int, int]], list[str]]:
    chunks: list[list[tuple[int, int]]] = []
    names: list[str] = []
    for i in range(16):
        name = f"fast_domain.{prefix}_chunk_{i:02d}"
        marker = f"def {name} :"
        pos = text.index(marker)
        eq = text.index(" := ", pos) + len(" := ")
        line_end = text.index("\n", eq)
        rhs = text[eq:line_end]
        pairs = [(int(a), int(b)) for a, b in PAIR.findall(rhs)]
        require(len(pairs) == 32, f"{name} has {len(pairs)} entries, expected 32")
        theorem = f"theorem {name}_length : {name}.length = 32 := rfl"
        require(theorem in text, f"missing named rfl length proof for {name}")
        chunks.append(pairs)
        names.append(name)
    return [pair for chunk in chunks for pair in chunk], names


def definition_body(text: str, name: str, next_marker: str) -> str:
    start = text.index(f"def {name}")
    body_start = text.index(":= do\n", start) + len(":= do\n")
    end = text.index(next_marker, body_start)
    return text[body_start:end].strip()


def normalize_body(body: str, *, adapted: bool) -> str:
    body = re.sub(r"\s+", " ", body).strip()
    if adapted:
        body = body.replace("fast_domain.table_value ops", "fast_domain.table_value")
        body = body.replace("ops.mul", "field.CM31.mul")
    else:
        body = body.replace("field.CM31.new", "ops.new")
    return body


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--packet-root", type=Path, default=ROOT,
                        help="root containing extraction/ and sources/ from the fibre-point packet")
    packet_root = parser.parse_args().packet_root
    raw_path = packet_root / "extraction" / "Funs.lean"
    adapted_path = packet_root / "sources" / "Funs-chunked-adapter.lean"
    chunk_probe_path = packet_root / "sources" / "ChunkLengthProbe.lean"
    raw = raw_path.read_text()
    adapted = adapted_path.read_text()
    chunk_probe = chunk_probe_path.read_text()

    # The resource-only overrides in the raw generated file are deliberately
    # absent from the elaborated adapter; the check does not infer a replay.
    require("set_option maxHeartbeats 1000000" in raw, "raw pin lacks expected heartbeat option")
    require("set_option maxRecDepth 2048" in raw, "raw pin lacks expected recursion option")
    require("set_option maxHeartbeats" not in adapted, "adapter retained heartbeat override")
    require("set_option maxRecDepth" not in adapted, "adapter retained recursion override")

    ops = re.search(r"structure CM31Ops where\s+new : ([^\n]+)\n\s+mul : ([^\n]+)", adapted)
    require(ops is not None, "explicit CM31Ops record not found")
    require(ops.group(1).strip() == "field.M31 → field.M31 → Result field.CM31", "CM31Ops.new signature changed")
    require(ops.group(2).strip() == "field.CM31 → field.CM31 → Result field.CM31", "CM31Ops.mul signature changed")

    for table in ("TABLE_A", "TABLE_B"):
        raw_pairs = raw_table_pairs(raw, table)
        adapted_pairs, names = adapted_chunk_pairs(adapted, table)
        require(adapted_pairs == raw_pairs, f"ordered literal pairs changed for {table}")
        entries = f"fast_domain.{table}_entries"
        expected_concat = " ++ ".join(names)
        entry_line = re.search(rf"def {re.escape(entries)} :[^\n]*:= ([^\n]+)", adapted)
        require(entry_line is not None and entry_line.group(1) == expected_concat,
                f"{table} chunk concatenation order differs")
        length_name = f"fast_domain.{table}_entries_length"
        require(re.search(rf"theorem {re.escape(length_name)} : {re.escape(entries)}\.length = 512 := by simp \[", adapted) is not None,
                f"missing named 512-entry proof for {table}")
        array_decl = re.search(rf"def fast_domain\.{table} :[^\n]*:=\n\s*Array\.make 512#usize {re.escape(entries)} \(by exact {re.escape(length_name)}\)", adapted)
        require(array_decl is not None, f"{table} Array.make does not consume named length theorem")

    require("theorem chunk0_length : chunk0.length = 32 := rfl" in chunk_probe,
            "standalone named chunk-length probe missing")
    require("theorem chunks_length : chunks.length = 64 := by simp [chunks, chunk0_length, chunk1_length]" in chunk_probe,
            "standalone concatenated length proof missing")

    raw_table_value = definition_body(raw, "fast_domain.table_value", "/-- [r17_querygeo_extraction::fast_domain::fibre_point]")
    ad_table_value = definition_body(adapted, "fast_domain.table_value", "/-- [r17_querygeo_extraction::fast_domain::fibre_point]")
    raw_fibre = definition_body(raw, "fast_domain.fibre_point", "\nend AspisR1QueryGeometryActual")
    ad_fibre = definition_body(adapted, "fast_domain.fibre_point", "\nend AspisR1QueryGeometryActual")
    require(normalize_body(raw_table_value, adapted=False) == normalize_body(ad_table_value, adapted=True),
            "table_value body differs beyond explicit CM31Ops.new replacement")
    require(normalize_body(raw_fibre, adapted=False) == normalize_body(ad_fibre, adapted=True),
            "fibre_point control-flow body differs beyond table_value ops arg / CM31Ops.mul")

    print("adapter checks: PASS")
    print(f"raw Funs SHA256: {digest(raw_path)}")
    print(f"adapted Funs SHA256: {digest(adapted_path)}")
    print("verified: explicit new/mul fields; no resource overrides; exact ordered A/B pairs; chunk concatenation; named lengths; body normalization")


if __name__ == "__main__":
    main()
