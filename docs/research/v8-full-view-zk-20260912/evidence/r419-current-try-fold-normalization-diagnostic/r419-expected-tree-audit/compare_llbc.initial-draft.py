#!/usr/bin/env python3
"""Fail-closed JSON comparator for an immutable LLBC input and a candidate.

No LLBC rewriting occurs. Optional edits are checked against exact JSON paths
and exact before/after values in a separate lead-reviewed manifest. With no
manifest, every difference is reported and the comparison fails.
"""
from __future__ import annotations
import argparse
import copy
import hashlib
import json
from pathlib import Path
from typing import Any


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def collect_hashcons(node: Any, table: dict[int, Any]) -> None:
    if isinstance(node, dict):
        if set(node) == {"HashConsedValue"}:
            ident, value = node["HashConsedValue"]
            ident = int(ident)
            if ident in table and table[ident] != value:
                raise ValueError(f"conflicting HashConsedValue id {ident}")
            table[ident] = value
            collect_hashcons(value, table)
        elif "Deduplicated" not in node:
            for value in node.values():
                collect_hashcons(value, table)
    elif isinstance(node, list):
        for value in node:
            collect_hashcons(value, table)


def decode(node: Any, table: dict[int, Any], seen: tuple[int, ...] = ()) -> Any:
    if isinstance(node, dict):
        if set(node) == {"HashConsedValue"}:
            ident, value = node["HashConsedValue"]
            ident = int(ident)
            if ident in seen:
                return {"$cycle_hashcons_id": ident}
            return decode(value, table, seen + (ident,))
        if set(node) == {"Deduplicated"}:
            ident = int(node["Deduplicated"])
            if ident not in table:
                raise ValueError(f"unresolved Deduplicated id {ident}")
            if ident in seen:
                return {"$cycle_hashcons_id": ident}
            return decode(table[ident], table, seen + (ident,))
        return {key: decode(value, table, seen) for key, value in node.items()}
    if isinstance(node, list):
        return [decode(value, table, seen) for value in node]
    return node


def at_path(root: Any, path: list[Any]) -> Any:
    value = root
    for part in path:
        value = value[part]
    return value


def apply_approved_edits(root: Any, edits: list[dict[str, Any]]) -> tuple[Any, list[dict[str, Any]]]:
    """Apply manifest edits to a private deep copy, with exact old/new guards."""
    result = copy.deepcopy(root)
    records = []
    paths = [tuple(e["path"]) for e in edits]
    if len(paths) != len(set(paths)):
        raise ValueError("duplicate edit path; edits must be uniquely inventoried")
    for edit in edits:
        path = list(edit["path"])
        kind = edit["kind"]
        parent = at_path(result, path[:-1]) if path else None
        key = path[-1] if path else None
        if kind == "replace_exact":
            old = at_path(result, path)
            if old != edit["before"]:
                raise ValueError(f"before-value mismatch at {path!r}")
            if edit["after"] == old:
                raise ValueError(f"no-op replacement at {path!r}")
            if path:
                parent[key] = copy.deepcopy(edit["after"])
            else:
                result = copy.deepcopy(edit["after"])
            records.append({"path": path, "kind": kind, "before": old, "after": edit["after"]})
        elif kind == "drop_list_item_exact":
            seq = at_path(result, path)
            index = int(edit["index"])
            if not isinstance(seq, list) or index < 0 or index >= len(seq):
                raise ValueError(f"invalid list/index at {path!r}:{index}")
            old_item = seq[index]
            if old_item != edit["before_item"]:
                raise ValueError(f"before-item mismatch at {path!r}[{index}]")
            if "expected_after" in edit:
                expected = copy.deepcopy(seq)
                del expected[index]
                if expected != edit["expected_after"]:
                    raise ValueError(f"expected_after mismatch at {path!r}")
            del seq[index]
            records.append({"path": path, "kind": kind, "index": index, "before_item": old_item})
        else:
            raise ValueError(f"unsupported edit kind {kind!r}; fail closed")
    return result, records


def diff_paths(a: Any, b: Any, path: tuple[Any, ...] = ()) -> list[dict[str, Any]]:
    if type(a) is not type(b):
        return [{"path": list(path), "kind": "type", "left": type(a).__name__, "right": type(b).__name__}]
    if isinstance(a, dict):
        out = []
        for key in sorted(set(a) | set(b), key=str):
            if key not in a:
                out.append({"path": list(path + (key,)), "kind": "missing_left", "right": b[key]})
            elif key not in b:
                out.append({"path": list(path + (key,)), "kind": "missing_right", "left": a[key]})
            else:
                out.extend(diff_paths(a[key], b[key], path + (key,)))
        return out
    if isinstance(a, list):
        if len(a) != len(b):
            out = [{"path": list(path), "kind": "list_length", "left": len(a), "right": len(b)}]
        else:
            out = []
        for i, (x, y) in enumerate(zip(a, b)):
            out.extend(diff_paths(x, y, path + (i,)))
        return out
    if a != b:
        return [{"path": list(path), "kind": "value", "left": a, "right": b}]
    return []


def classify(path: list[Any]) -> list[str]:
    keys = {str(p) for p in path if isinstance(p, str)}
    tags = []
    if keys & {"body", "statements", "statement", "kind", "terminator", "target"}:
        tags.append("executable-or-control-flow")
    if keys & {"source_text", "span", "files", "item_meta", "attrs", "attributes"}:
        tags.append("source-or-attributes")
    if "ordered_decls" in keys:
        tags.append("declaration-order")
    if keys & {"generics", "trait_type_constraints", "types", "ty", "type", "generic_args"}:
        tags.append("typed-generic-data")
    return tags or ["other"]


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("original", type=Path)
    ap.add_argument("candidate", type=Path)
    ap.add_argument("--edits", type=Path, help="lead-reviewed exact-path edits JSON; defaults to none")
    ap.add_argument("--report", type=Path, required=True)
    args = ap.parse_args()
    raw_a = json.loads(args.original.read_text())
    raw_b = json.loads(args.candidate.read_text())
    ta: dict[int, Any] = {}; tb: dict[int, Any] = {}
    collect_hashcons(raw_a, ta); collect_hashcons(raw_b, tb)
    a = decode(raw_a, ta); b = decode(raw_b, tb)
    edits = []
    edit_manifest = None
    if args.edits:
        edit_manifest = json.loads(args.edits.read_text())
        if edit_manifest.get("status") != "lead-reviewed exact path/value allowlist":
            raise ValueError("edit manifest lacks exact required status; fail closed")
        edits = edit_manifest.get("edits", [])
    a_norm, edit_records = apply_approved_edits(a, edits)
    differences = diff_paths(a_norm, b)
    report = {
        "classification": "mechanical structural comparison only; no semantic or source-correspondence conclusion",
        "inputs": [
            {"path": str(args.original), "sha256": sha(args.original), "bytes": args.original.stat().st_size,
             "hashcons_definitions": len(ta)},
            {"path": str(args.candidate), "sha256": sha(args.candidate), "bytes": args.candidate.stat().st_size,
             "hashcons_definitions": len(tb)},
        ],
        "edit_manifest": ({"path": str(args.edits), "sha256": sha(args.edits)} if args.edits else None),
        "approved_edits_applied_to_original_copy": edit_records,
        "remaining_diff_count": len(differences),
        "remaining_diffs": [{**d, "categories": classify(d["path"])} for d in differences],
        "result": "exact-after-explicit-edits" if not differences else "mismatches-reported",
        "limits": [
            "Every transformation must be a fully enumerated exact JSON-path operation with exact expected before/after values.",
            "No generic field name is globally ignored or stripped.",
            "An empty edit manifest permits no changes. This draft does not decide which edits are admissible.",
            "Hash-cons cycles are represented with their serialized IDs; differing cycle markers remain visible as mismatches.",
        ],
    }
    args.report.parent.mkdir(parents=True, exist_ok=True)
    args.report.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"result": report["result"], "remaining_diff_count": len(differences), "report": str(args.report)}, indent=2))
    return 0 if not differences else 2

if __name__ == "__main__":
    raise SystemExit(main())
