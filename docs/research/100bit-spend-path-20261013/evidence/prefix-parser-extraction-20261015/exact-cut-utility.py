#!/usr/bin/env python3
"""Copy exact Rust declarations and render a provenance-pinned extraction input.

No declaration is rewritten. The generated lib.rs inserts each copied source
span verbatim into a namespace-only layout template. This script does not build,
run Charon/Aeneas, or prove a Rust-to-Lean refinement.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[5]
OUT = Path(__file__).resolve().parent
TEMPLATE = OUT / "layout.template.rs"

ITEMS = [
    ("compiled_variant", "crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs", "enum CompiledVariant"),
    ("semantic_public", "crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs", "struct SemanticPublic<'a>"),
    ("private_public", "crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs", "fn private_public<'a>("),
    ("withdrawal_public", "crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs", "fn withdrawal_public<'a>("),
    ("r0_public_enum", "crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs", "pub enum Public<'a>"),
    ("r0_public_semantic_method", "crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs", "fn semantic(self) -> SemanticPublic<'a>"),
    ("public_bytes_method", "crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs", "pub fn public_bytes(self) -> Result<Vec<u8>, Error>"),
    ("transfer_public", "crates/aspis-statement/src/pool_v1/payment_relation.rs", "pub struct PoolV1PrivateTransferPublicV1"),
    ("withdrawal_public_type", "crates/aspis-statement/src/pool_v1/payment_relation.rs", "pub struct PoolV1WithdrawalPublicV1"),
    ("live_snapshot", "crates/aspis-statement/src/pool_v1/pair_tree_profile.rs", "pub struct PoolV1PairLiveSnapshotV1"),
    ("late_public_statement", "crates/aspis-statement/src/pool_v1/pair_tree_profile.rs", "pub struct PoolV1PairLatePublicStatementV1"),
    ("verified_afterstate", "crates/aspis-statement/src/pool_v1/pair_terminal.rs", "pub struct PoolV1PairVerifiedAfterstateV1"),
    ("digest_elems", "crates/aspis-statement/src/poseidon2.rs", "pub const DIGEST_ELEMS: usize"),
    ("digest_alias", "crates/aspis-statement/src/poseidon2.rs", "pub type Digest"),
    ("m31_type", "crates/aspis-core/src/field.rs", "pub struct M31(pub u32)"),
    ("m31_modulus", "crates/aspis-core/src/field.rs", "pub const P: u32"),
    ("pair_tree_depth", "crates/aspis-statement/src/pool_v1/pair_tree_profile.rs", "pub const POOL_V1_PAIR_TREE_DEPTH: usize"),
    ("pool_tree_depth", "crates/aspis-statement/src/pool_v1/format.rs", "pub const POOL_V1_TREE_DEPTH: usize"),
    ("r0_error", "crates/aspis-core/src/state_only_prefix.rs", "pub enum Error {\n        Allocation,"),
]


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def git_blob_sha(revision: str, relpath: str) -> str | None:
    result = subprocess.run(["git", "-C", str(ROOT), "show", f"{revision}:{relpath}"],
                            stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
    return sha(result.stdout) if result.returncode == 0 else None


def declaration_start(text: str, at: int) -> int:
    """Include contiguous doc/attribute/comment lines immediately above item."""
    start = text.rfind("\n", 0, at) + 1
    while start > 0:
        prev_end = start - 1
        prev_start = text.rfind("\n", 0, prev_end) + 1
        prev = text[prev_start:prev_end].strip()
        if prev.startswith(("///", "#[", "//")):
            start = prev_start
        else:
            break
    return start


def line_end_exclusive(text: str, end: int) -> int:
    # Source spans terminate before the line's newline. If a span itself ends
    # with newline, that newline already moves the cursor to the exclusive line.
    return text.count("\n", 0, end) + (1 if end > 0 and text[end - 1] == "\n" else 2)


def top_level_semicolon(text: str, start: int) -> int:
    """Find a declaration terminator, ignoring nested type/array punctuation."""
    paren = square = brace = 0
    state = "code"
    block_depth = 0
    escaped = False
    i = start
    while i < len(text):
        ch = text[i]
        nxt = text[i:i+2]
        if state == "line":
            if ch == "\n": state = "code"
        elif state == "block":
            if nxt == "/*": block_depth += 1; i += 1
            elif nxt == "*/":
                block_depth -= 1; i += 1
                if block_depth == 0: state = "code"
        elif state in ("string", "char"):
            if escaped: escaped = False
            elif ch == "\\": escaped = True
            elif (state == "string" and ch == '"') or (state == "char" and ch == "'"): state = "code"
        else:
            if nxt == "//": state = "line"; i += 1
            elif nxt == "/*": state = "block"; block_depth = 1; i += 1
            elif ch == '"': state = "string"
            elif ch == "'" and i + 2 < len(text) and text[i+2] == "'": state = "char"
            elif ch == "(": paren += 1
            elif ch == ")": paren -= 1
            elif ch == "[": square += 1
            elif ch == "]": square -= 1
            elif ch == "{": brace += 1
            elif ch == "}": brace -= 1
            elif ch == ";" and paren == square == brace == 0: return i
        i += 1
    return -1


def find_item(path: Path, anchor: str) -> tuple[bytes, int, int, int, int]:
    raw = path.read_bytes()
    text = raw.decode("utf-8")
    at = text.find(anchor)
    if at < 0 or text.find(anchor, at + 1) >= 0:
        raise ValueError(f"anchor must occur exactly once: {path}:{anchor!r}")
    start = declaration_start(text, at)
    brace = text.find("{", at)
    semi = top_level_semicolon(text, at)
    if semi >= 0 and (brace < 0 or semi < brace):
        end = semi + 1
        fragment = text[start:end].encode("utf-8")
        byte_start = len(text[:start].encode("utf-8"))
        byte_end = len(text[:end].encode("utf-8"))
        return fragment, byte_start, byte_end, text.count("\n", 0, start) + 1, line_end_exclusive(text, end)
    if brace < 0:
        raise ValueError(f"no body brace or declaration semicolon for {path}:{anchor!r}")

    # Selected items have no raw-string literals. Brace balancing ignores line
    # comments, nested block comments, ordinary strings, and character literals.
    depth = 0
    i = brace
    state = "code"
    block_depth = 0
    escaped = False
    while i < len(text):
        ch = text[i]
        nxt = text[i:i+2]
        if state == "line":
            if ch == "\n": state = "code"
        elif state == "block":
            if nxt == "/*": block_depth += 1; i += 1
            elif nxt == "*/":
                block_depth -= 1; i += 1
                if block_depth == 0: state = "code"
        elif state in ("string", "char"):
            if escaped: escaped = False
            elif ch == "\\": escaped = True
            elif (state == "string" and ch == '"') or (state == "char" and ch == "'"): state = "code"
        else:
            if nxt == "//": state = "line"; i += 1
            elif nxt == "/*": state = "block"; block_depth = 1; i += 1
            elif ch == '"': state = "string"
            elif ch == "'" and i + 2 < len(text) and text[i+2] == "'": state = "char"
            elif ch == "{": depth += 1
            elif ch == "}":
                depth -= 1
                if depth == 0:
                    end = i + 1
                    if end < len(text) and text[end] == ";": end += 1
                    fragment = text[start:end].encode("utf-8")
                    byte_start = len(text[:start].encode("utf-8"))
                    byte_end = len(text[:end].encode("utf-8"))
                    return fragment, byte_start, byte_end, text.count("\n", 0, start) + 1, line_end_exclusive(text, end)
        i += 1
    raise ValueError(f"unclosed item: {path}:{anchor!r}")


def render_layout() -> tuple[bytes, list[dict[str, object]]]:
    template = TEMPLATE.read_text()
    output = bytearray()
    output_spans: list[dict[str, object]] = []
    for line in template.splitlines(keepends=True):
        match = re.fullmatch(r'\s*include!\("fragments/([a-z0-9_]+)\.rs"\);\n?', line)
        if not match:
            output.extend(line.encode("utf-8"))
            continue
        name = match.group(1)
        fragment_path = OUT / "fragments" / f"{name}.rs"
        fragment = fragment_path.read_bytes()
        start = len(output)
        output.extend(fragment)
        end = len(output)
        output_spans.append({"name": name, "byte_start": start, "byte_end_exclusive": end,
                             "fragment_sha256": sha(fragment)})
        if not fragment.endswith(b"\n"):
            output.extend(b"\n")
    return bytes(output), output_spans


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true", help="verify generated spans, layout and kit pins")
    args = parser.parse_args()
    old_manifest_path = OUT / "source-manifest.json"
    current_revision = subprocess.check_output(["git", "-C", str(ROOT), "rev-parse", "HEAD"], text=True).strip()
    recorded = json.loads(old_manifest_path.read_text()) if args.check and old_manifest_path.is_file() else None
    if recorded is not None:
        # Preserve the revision at kit generation; current file hashes below
        # independently detect relevant source changes.
        source_revision = recorded["source_revision"]
        subprocess.run(["git", "-C", str(ROOT), "cat-file", "-e", f"{source_revision}^{{commit}}"],
                       check=True, stdout=subprocess.DEVNULL, stderr=subprocess.PIPE)
    else:
        source_revision = current_revision

    manifest: dict[str, object] = {"format": 1,
        "purpose": "exact source fragments and extraction-input provenance; no build/refinement claim",
        "repository_root": ".", "source_revision": source_revision, "items": []}
    items = []
    for name, rel, anchor in ITEMS:
        src = ROOT / rel
        fragment, start, end, line_start, line_end = find_item(src, anchor)
        rel_out = f"fragments/{name}.rs"
        source_revision_sha256 = git_blob_sha(source_revision, rel)
        record = {"name": name, "source_path": rel, "source_sha256": sha(src.read_bytes()),
                  "source_revision_sha256": source_revision_sha256, "anchor": anchor,
                  "byte_start": start, "byte_end_exclusive": end, "line_start": line_start, "line_end_exclusive": line_end,
                  "fragment_path": rel_out, "fragment_sha256": sha(fragment)}
        if args.check and recorded is not None:
            prior = next((entry for entry in recorded["items"] if entry["name"] == name), None)
            if prior is None or prior.get("source_revision_sha256") != source_revision_sha256:
                print(f"pinned revision source mismatch/unavailable: {rel}", file=sys.stderr)
                return 1
        items.append(record)
        manifest["items"].append(record)
        out = OUT / rel_out
        if args.check:
            if not out.is_file() or out.read_bytes() != fragment:
                print(f"mismatch: {rel_out}", file=sys.stderr)
                return 1
        else:
            out.parent.mkdir(parents=True, exist_ok=True)
            out.write_bytes(fragment)

    layout_bytes, output_spans = render_layout()
    expected_names = [name for name, _, _ in ITEMS]
    rendered_names = [str(span["name"]) for span in output_spans]
    if len(rendered_names) != len(expected_names) or set(rendered_names) != set(expected_names):
        raise ValueError(f"layout insertions do not match item list: {rendered_names!r}")
    layout_path = OUT / "lib.rs"
    layout_record = {"path": "lib.rs", "sha256": sha(layout_bytes), "inserted_fragment_spans": output_spans}
    manifest["rendered_layout"] = layout_record
    if args.check:
        if not layout_path.is_file() or layout_path.read_bytes() != layout_bytes:
            print("mismatch: lib.rs", file=sys.stderr)
            return 1
    else:
        layout_path.write_bytes(layout_bytes)

    manifest_path = OUT / "source-manifest.json"
    serialized = json.dumps(manifest, indent=2, sort_keys=True) + "\n"
    if args.check:
        if not manifest_path.is_file() or manifest_path.read_text() != serialized:
            print("mismatch: source-manifest.json", file=sys.stderr)
            return 1
    else:
        manifest_path.write_text(serialized)

    source_files = [OUT / "Cargo.toml", layout_path, TEMPLATE, manifest_path,
                    *(OUT / record["fragment_path"] for record in items)]
    source_pins = {"format": 1, "sources": {str(path.relative_to(OUT)): {"sha256": sha(path.read_bytes())}
                                                   for path in sorted(source_files)}}
    pin_path = OUT / "source-pins.json"
    pins_serialized = json.dumps(source_pins, indent=2, sort_keys=True) + "\n"
    if args.check:
        if not pin_path.is_file() or pin_path.read_text() != pins_serialized:
            print("mismatch: source-pins.json", file=sys.stderr)
            return 1
    else:
        pin_path.write_text(pins_serialized)

    print(f"{'verified' if args.check else 'prepared'} {len(ITEMS)} exact declaration spans and source-pinned lib.rs")
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
