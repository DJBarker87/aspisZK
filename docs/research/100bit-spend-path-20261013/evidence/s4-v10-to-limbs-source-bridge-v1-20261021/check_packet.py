#!/usr/bin/env python3
"""Verify the source-only V10 to_limbs extraction/adapter packet."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parent


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def verify_files(manifest: dict) -> None:
    expected_paths = {item["path"] for item in manifest["files"]}
    actual_paths = {
        path.relative_to(ROOT).as_posix()
        for path in ROOT.rglob("*")
        if path.is_file() and path.name not in {"manifest.json", "SHA256SUMS"}
    }
    assert expected_paths == actual_paths, (
        f"file inventory mismatch; omitted={sorted(actual_paths - expected_paths)}, "
        f"stale={sorted(expected_paths - actual_paths)}"
    )
    for item in manifest["files"]:
        path = ROOT / item["path"]
        assert path.is_file(), f"missing file: {item['path']}"
        data = path.read_bytes()
        assert len(data) == item["size_bytes"], f"size mismatch: {item['path']}"
        assert hashlib.sha256(data).hexdigest() == item["sha256"], (
            f"hash mismatch: {item['path']}"
        )


def verify_extraction(manifest: dict) -> None:
    raw_funs = ROOT / "sources/raw-extraction/AspisR1FastDotsCurrent/Funs.lean"
    clean_body = ROOT / "sources/lean/AspisR1FastDotsCurrent/ToLimbsBody.lean"
    raw = raw_funs.read_text()
    clean = clean_body.read_text()
    start_marker = (
        "/-- [aspis_core::field::wide_exact::{aspis_core::field::wide_exact::"
        "WideExact}::to_limbs]:"
    )
    start = raw.index(start_marker)
    end = raw.index("\n\n/-- ", start)
    extracted_item = raw[start:end]
    assert raw.count(start_marker) == 1
    assert clean.count(extracted_item) == 1, "adapted body is not the exact emitted item"
    assert manifest["extraction"]["generated_funs_sha256"] == sha(raw_funs)

    raw_types_path = ROOT / "sources/raw-extraction/AspisR1FastDotsCurrent/Types.lean"
    clean_types_path = ROOT / "sources/lean/AspisR1FastDotsCurrent/Types.lean"
    raw_types = raw_types_path.read_text()
    clean_types = clean_types_path.read_text()
    filtered = "".join(
        line
        for line in raw_types.splitlines(keepends=True)
        if line.strip() != "import AspisR1FastDotsCurrent.TypesExternal"
        and not line.lstrip().startswith("set_option ")
        and "maxHeartbeats" not in line
        and "maxRecDepth" not in line
    )
    assert filtered == clean_types, "clean Types is not exact source with only forbidden template/option lines removed"
    assert manifest["extraction"]["generated_types_sha256"] == sha(raw_types_path)

    llbc = ROOT / "sources/raw-extraction/four_dots.llbc"
    assert sha(llbc) == manifest["extraction"]["llbc_sha256"]
    assert manifest["extraction"]["selected_item"] == (
        "aspis_core::field::wide_exact::{aspis_core::field::wide_exact::WideExact}::to_limbs"
    )
    assert manifest["extraction"]["selected_item_translation"] == "Transparent"

    rust_source = ROOT / "sources/rust/crates/aspis-core/src/field/wide_exact.rs"
    assert sha(rust_source) == manifest["extraction"]["rust_method_file_sha256"]
    lines = rust_source.read_text().splitlines()
    source_body = "\n".join(lines[237:249])
    expected = """    pub const fn to_limbs(self) -> [u32; Self::LIMB_COUNT] {
        [
            self.c0.c0.a.0,
            self.c0.c0.b.0,
            self.c0.c1.a.0,
            self.c0.c1.b.0,
            self.c1.c0.a.0,
            self.c1.c0.b.0,
            self.c1.c1.a.0,
            self.c1.c1.b.0,
        ]
    }"""
    assert source_body == expected, "Rust method body or pinned source span changed"

    translation_path = ROOT / "sources/raw-extraction/translation.json"
    translation = json.loads(translation_path.read_text())
    matches = [
        item for item in translation["functions"]
        if item.get("def_id") == 24
        and item.get("rust_name") == manifest["extraction"]["selected_item"]
    ]
    assert len(matches) == 1
    item = matches[0]
    assert item["lean_file"] == "AspisR1FastDotsCurrent/Funs.lean"
    assert item["is_opaque"] is False and item["can_fail"] is True
    assert item["source"] == {
        "file": "crates/aspis-core/src/field/wide_exact.rs",
        "begin_line": 238,
        "end_line": 238,
    }


def main() -> None:
    manifest = json.loads((ROOT / "manifest.json").read_text())
    assert manifest["schema"] == "focused-extractor-proof-packet-v1"
    verify_files(manifest)
    verify_extraction(manifest)
    print("packet integrity and exact extraction checks: PASS")


if __name__ == "__main__":
    main()
