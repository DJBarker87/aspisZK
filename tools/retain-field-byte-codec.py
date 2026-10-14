#!/usr/bin/env python3
"""Retain pinned field-byte codec declarations under a narrow namespace."""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "docs/research/100bit-spend-path-20261013/FIELD-BYTE-CODEC-REUSE-SOURCES.json"

def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()

def source_text(entry: dict) -> str:
    path = ROOT / entry["path"]
    data = path.read_bytes()
    got = sha256(data)
    if got != entry["sha256"]:
        raise ValueError(f"source hash mismatch for {entry['path']}: {got}")
    return data.decode("utf-8")

def between(source: str, start: str, end: str) -> str:
    if source.count(start) != 1 or source.count(end) != 1:
        raise ValueError(f"extraction markers must each occur exactly once: {start!r}, {end!r}")
    i = source.index(start)
    j = source.index(end)
    if j <= i:
        raise ValueError(f"end marker precedes start: {start!r}")
    return source[i:j].rstrip()

def extract(manifest: dict) -> str:
    sampler = source_text(manifest["sources"]["sampler"])
    rep = source_text(manifest["sources"]["representation"])
    transcript = source_text(manifest["sources"]["transcript"])
    merkle = source_text(manifest["sources"]["merkle"])

    alias_lines = []
    for declaration in manifest["sources"]["sampler"]["lines"]:
        if sampler.splitlines().count(declaration) != 1:
            raise ValueError(f"expected exactly one declaration: {declaration}")
        alias_lines.append(declaration)

    rep_block = between(rep, manifest["sources"]["representation"]["start"],
                        manifest["sources"]["representation"]["end"])
    tr_blocks = [between(transcript, start, end)
                 for start, end in manifest["sources"]["transcript"]["chunks"]]
    merkle_block = between(merkle, manifest["sources"]["merkle"]["start"],
                           manifest["sources"]["merkle"]["end"])

    old = manifest["allowed_qualifier_replacement"]["from"]
    new = manifest["allowed_qualifier_replacement"]["to"]
    body = "\n\n".join(["\n".join(alias_lines), rep_block, *tr_blocks, merkle_block])
    replacements = body.count(old)
    expected = manifest["allowed_qualifier_replacement"]["expected_count"]
    if replacements != expected:
        raise ValueError(f"expected {expected} allowed qualifier replacements, found {replacements}")
    body = body.replace(old, new)

    imports = "\n".join(f"import {name}" for name in manifest["imports"])
    header = (imports + "\n\n" +
              "/-! Verbatim retained byte and field codec declarations. Their source pins and "
              "the only permitted namespace qualification replacement are checked by "
              "tools/retain-field-byte-codec.py. This is a retained model interface, "
              "not a new source correspondence proof. -/\n" +
              "set_option autoImplicit false\n\n" +
              "namespace AspisR1.RetainedFieldByteCodec\n\n")
    audits = "\n\n".join([
        "#print axioms decodeWordLE_encodeWordLE",
        "#print axioms decodeM31LE_encodeM31LE",
        "#print axioms decodeQM31LE_encodeQM31LE",
        "#print axioms encodeWordLE_decodeWordLE",
        "#print axioms encodeQM31LE_of_decodeQM31LE",
        "#print axioms decodeQM31Bytes",
    ])
    return header + body + "\n\n" + audits + "\n\nend AspisR1.RetainedFieldByteCodec\n"

def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    manifest = json.loads(MANIFEST.read_text())
    output = ROOT / manifest["output"]
    expected = extract(manifest)
    if args.check:
        try:
            actual = output.read_text()
        except FileNotFoundError:
            print(f"missing generated file: {output}", file=sys.stderr)
            return 1
        if actual != expected:
            print(f"generated output differs: {output}", file=sys.stderr)
            return 1
        print(f"checked {output.relative_to(ROOT)}")
        return 0
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(expected)
    print(f"wrote {output.relative_to(ROOT)}")
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
