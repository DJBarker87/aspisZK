#!/usr/bin/env python3
"""Check source-only Charon extraction evidence and its structural comparison."""

from __future__ import annotations

import hashlib
import json
from collections import Counter
from pathlib import Path


ROOT = Path(__file__).resolve().parent
ATTEMPTS = ROOT / "attempts"


def digest(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for block in iter(lambda: f.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def read_json(path: Path):
    return json.loads(path.read_text())


def llbc(folder: str):
    return read_json(ATTEMPTS / folder / "from_fn.llbc")


def name(meta):
    if not isinstance(meta, dict):
        return ""
    parts = []
    for item in meta.get("name") or []:
        ident = item.get("Ident") if isinstance(item, dict) else None
        if ident:
            parts.append(ident[0])
        else:
            parts.append(json.dumps(item, sort_keys=True))
    return "::".join(parts)


def main() -> None:
    manifest = read_json(ROOT / "manifest.json")
    for rel, expected in manifest["files"].items():
        path = ROOT / rel
        assert path.is_file(), f"missing: {rel}"
        actual = digest(path)
        assert actual == expected, f"SHA256 mismatch: {rel}: {actual} != {expected}"

    # No compiled objects, native executables, or binary build products belong
    # in this source-only packet. LLBC files here are JSON text.
    forbidden = {
        ".olean", ".ilean", ".o", ".a", ".so", ".dylib", ".dll", ".exe",
        ".elf", ".rlib", ".rmeta", ".bin", ".wasm",
    }
    for path in ROOT.rglob("*"):
        if path.is_file():
            assert path.suffix.lower() not in forbidden, f"binary artifact present: {path}"
    for rel in manifest["llbc_json"]:
        json.loads((ROOT / rel).read_text())

    union = llbc("01-union-transparent")
    cut = llbc("02-guard-only-selector")
    verified = llbc("03-guard-only-cgroup-verification")
    assert union["has_errors"] is False
    assert cut["has_errors"] is False
    assert verified["has_errors"] is False

    # Exact output equivalence modulo the two known serializer-only changes.
    cut_t = cut["translated"]
    verified_t = verified["translated"]
    assert cut.keys() == verified.keys()
    assert cut["charon_version"] == verified["charon_version"]
    assert cut["has_errors"] == verified["has_errors"]
    assert cut_t.keys() == verified_t.keys()
    assert Counter(map(lambda x: json.dumps(x, sort_keys=True), cut_t["short_names"])) == Counter(
        map(lambda x: json.dumps(x, sort_keys=True), verified_t["short_names"])
    )
    option_keys = set(cut_t["options"]) | set(verified_t["options"])
    option_diffs = {
        k for k in option_keys if cut_t["options"].get(k) != verified_t["options"].get(k)
    }
    assert option_diffs == {"dest_file"}, f"unexpected options difference: {option_diffs}"
    cut_normalized = json.loads(json.dumps(cut_t))
    verified_normalized = json.loads(json.dumps(verified_t))
    cut_normalized["options"]["dest_file"] = "<OUTPUT>"
    verified_normalized["options"]["dest_file"] = "<OUTPUT>"
    order_key = lambda x: json.dumps(x["key"], sort_keys=True)
    cut_normalized["short_names"] = sorted(cut_normalized["short_names"], key=order_key)
    verified_normalized["short_names"] = sorted(verified_normalized["short_names"], key=order_key)
    assert cut_normalized == verified_normalized, "unaccounted LLBC structural difference"

    # Guard-only selector contract: exact named type/function declarations
    # exist and have the intended visibility. We inspect metadata only; this is
    # not an Aeneas semantic proof.
    type_by_name = {name(d.get("item_meta")): d for d in cut_t["type_decls"]
                    if isinstance(d, dict) and isinstance(d.get("item_meta"), dict)}
    maybe = next(d for n, d in type_by_name.items() if n.endswith("MaybeUninit"))
    guard = next(d for n, d in type_by_name.items() if n.endswith("Guard"))
    assert maybe["item_meta"]["opacity"] == "Opaque"
    assert guard["item_meta"]["opacity"] == "Transparent"
    funs = cut_t["fun_decls"]
    by_name = {name(d.get("item_meta")): d for d in funs
               if isinstance(d, dict) and isinstance(d.get("item_meta"), dict)}
    required_fragments = (
        "core::array::from_fn",
        "core::array::try_from_fn",
        "core::array::try_from_fn_erased",
        "push_unchecked",
        "drop_glue",
    )
    for fragment in required_fragments:
        matches = [d for n, d in by_name.items() if fragment in n]
        assert matches, f"missing emitted declaration containing {fragment}"
        assert any(d.get("item_meta", {}).get("opacity") == "Transparent" for d in matches), (
            f"expected transparent declaration for {fragment}"
        )
    assert manifest["llbc_hashes"]["attempts/01-union-transparent/from_fn.llbc"] == digest(
        ATTEMPTS / "01-union-transparent/from_fn.llbc"
    )
    print("PASS: source-only packet hashes, three LLBC JSON files, structural diff, selector properties")


if __name__ == "__main__":
    main()
