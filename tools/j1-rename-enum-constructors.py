#!/usr/bin/env python3
"""Proposed name-only LLBC adaptation for Aeneas b59 enum constructor clashes.

Sets only item_meta.attr_info.rename on a function whose full Rust name equals
an enum variant's full Rust name. Does not alter Rust, bodies, types, IDs, calls,
variant names, or any other metadata. Restoring the recorded rename fields must
recover the complete original JSON value. This is not a compiler-correctness
proof; its use is explicitly recorded in the source boundary evidence.
"""
import argparse
import copy
import hashlib
import json
from pathlib import Path


def key(name):
    return json.dumps(name, sort_keys=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("report", type=Path)
    args = parser.parse_args()
    assert not args.output.exists() and not args.report.exists()
    raw = args.input.read_bytes()
    original = json.loads(raw)
    assert not original["has_errors"]
    updated = copy.deepcopy(original)
    crate = updated["translated"]
    variants = set()
    for declaration in crate["type_decls"]:
        if declaration is None:
            continue
        enum = declaration["kind"].get("Enum", []) if isinstance(declaration["kind"], dict) else []
        for variant in enum:
            variants.add(key(declaration["item_meta"]["name"] + [{"Ident": [variant["name"], 0]}]))
    occupied = {key(d["item_meta"]["name"]) for group in ["type_decls", "fun_decls", "global_decls"]
                for d in crate[group] if d is not None}
    changes = []
    for index, declaration in enumerate(crate["fun_decls"]):
        if declaration is None or key(declaration["item_meta"]["name"]) not in variants:
            continue
        meta = declaration["item_meta"]
        assert meta["attr_info"]["rename"] is None
        name = meta["name"][-1]["Ident"][0]
        replacement = name + "Constructor"
        candidate = key(meta["name"][:-1] + [{"Ident": [replacement, 0]}])
        assert candidate not in occupied and candidate not in variants
        occupied.add(candidate)
        meta["attr_info"]["rename"] = replacement
        changes.append({"function_index": index, "def_id": declaration["def_id"],
                        "rust_name": meta["name"], "span": meta["span"],
                        "old_rename": None, "new_rename": replacement})
    assert changes, "no name collisions found; refusing an unchanged rerun"
    restored = copy.deepcopy(updated)
    for change in changes:
        restored["translated"]["fun_decls"][change["function_index"]]["item_meta"]["attr_info"]["rename"] = change["old_rename"]
    assert restored == original, "non-name mutation"
    output = (json.dumps(updated, separators=(",", ":")) + "\n").encode()
    args.output.write_bytes(output)
    report = {"scope": "Proposed LLBC rename metadata only; no body/type/ID/source change",
              "input_sha256": hashlib.sha256(raw).hexdigest(),
              "output_sha256": hashlib.sha256(output).hexdigest(),
              "adapter_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              "restored_complete_json_equals_input": True, "changes": changes}
    args.report.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"name_only_changes": len(changes), "input_sha256": report["input_sha256"],
                      "output_sha256": report["output_sha256"]}))


if __name__ == "__main__":
    main()
