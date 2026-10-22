#!/usr/bin/env python3
"""Validate the source-only evidence for the two narrowed Charon cuts."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def sha(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for b in iter(lambda: f.read(1024 * 1024), b""):
            h.update(b)
    return h.hexdigest()


def load_llbc(folder: str):
    p = ROOT / folder / "from_fn.llbc"
    return json.loads(p.read_text()), sha(p)


def item_name(meta) -> str:
    if not isinstance(meta, dict):
        return ""
    return "::".join(
        x["Ident"][0]
        for x in (meta.get("name") or [])
        if isinstance(x, dict) and "Ident" in x
    )


def declarations(t, field):
    return [d for d in t[field] if isinstance(d, dict) and isinstance(d.get("item_meta"), dict)]


def main() -> None:
    manifest = json.loads((ROOT / "manifest.json").read_text())
    for rel, expected in manifest["files"].items():
        p = ROOT / rel
        assert p.is_file(), f"missing file: {rel}"
        assert sha(p) == expected, f"hash mismatch: {rel}"

    forbidden = {".olean", ".ilean", ".o", ".a", ".so", ".dylib", ".dll", ".exe", ".elf", ".rlib", ".bin", ".wasm"}
    for p in ROOT.rglob("*"):
        if p.is_file():
            assert p.suffix.lower() not in forbidden, f"binary artifact: {p}"

    one, one_sha = load_llbc("attempt-01-index-opaque")
    two, two_sha = load_llbc("attempt-02-index-and-len-opaque")
    assert one_sha == manifest["llbc_sha256"]["attempt-01-index-opaque/from_fn.llbc"]
    assert two_sha == manifest["llbc_sha256"]["attempt-02-index-and-len-opaque/from_fn.llbc"]
    assert one["has_errors"] is False and two["has_errors"] is False
    for output in (one, two):
        t = output["translated"]
        types = declarations(t, "type_decls")
        funs = declarations(t, "fun_decls")
        maybe = next(d for d in types if item_name(d["item_meta"]).endswith("MaybeUninit"))
        guard = next(d for d in types if item_name(d["item_meta"]).endswith("Guard"))
        assert maybe["item_meta"]["opacity"] == "Opaque"
        assert guard["item_meta"]["opacity"] == "Transparent"
        assert any("push_unchecked" in item_name(d["item_meta"]) and d["item_meta"]["opacity"] == "Transparent" for d in funs)
        assert any("try_from_fn_erased" in item_name(d["item_meta"]) and d["item_meta"]["opacity"] == "Transparent" for d in funs)

    one_t = one["translated"]
    two_t = two["translated"]
    one_funs = declarations(one_t, "fun_decls")
    two_funs = declarations(two_t, "fun_decls")
    one_named = {item_name(d["item_meta"]): d for d in one_funs}
    two_named = {item_name(d["item_meta"]): d for d in two_funs}
    one_len = next(d for n, d in one_named.items() if n.endswith("core::slice::len"))
    two_len = next(d for n, d in two_named.items() if n.endswith("core::slice::len"))
    assert one_len["item_meta"]["opacity"] == "Transparent"
    assert two_len["item_meta"]["opacity"] == "Foreign"
    ptr_meta = [d for n, d in one_named.items() if n.endswith("core::ptr::metadata::metadata")]
    assert ptr_meta and ptr_meta[0]["item_meta"]["opacity"] == "Foreign"
    assert not any(n.endswith("core::ptr::metadata::metadata") for n in two_named)
    assert "Pointee" in json.dumps(one_t)
    assert "Pointee" not in json.dumps(two_t)
    for n, d in two_named.items():
        if "get_unchecked_mut" in n:
            assert d["item_meta"]["opacity"] == "Foreign", (n, d["item_meta"]["opacity"])
    print("PASS: hashes, source-only contents, LLBC JSON, and intended declaration-opacity deltas")


if __name__ == "__main__":
    main()
