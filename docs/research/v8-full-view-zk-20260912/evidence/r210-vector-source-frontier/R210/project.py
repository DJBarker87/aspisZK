#!/usr/bin/env python3
"""Project R207 LLBC to five bodies while preserving hash-cons IDs/values."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parent
INPUT = ROOT.parent / "r207-vector-copy" / "R207VectorCopy.llbc"
OUTPUT = ROOT / "R210VectorLeafDiagnostic.llbc"
KEEP_BODY_IDS = {9, 49, 50, 91, 92}


class HashConsed:
    def __init__(self, ident: int, value: Any):
        self.ident = ident
        self.value = value


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def canonical(value: Any) -> Any:
    if isinstance(value, HashConsed):
        return {"$HashConsedValue": [value.ident, canonical(value.value)]}
    if isinstance(value, dict):
        return {key: canonical(item) for key, item in value.items()}
    if isinstance(value, list):
        return [canonical(item) for item in value]
    return value


def canonical_bytes(value: Any) -> bytes:
    return json.dumps(canonical(value), sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode()


source_bytes = INPUT.read_bytes()
raw = json.loads(source_bytes)

# First pass: collect every definition before resolving any reference.
definitions: dict[int, Any] = {}


def collect(node: Any) -> None:
    if isinstance(node, dict):
        if set(node) == {"HashConsedValue"}:
            ident, value = node["HashConsedValue"]
            if ident in definitions and definitions[ident] != value:
                raise ValueError(f"conflicting HashConsedValue definitions for id {ident}")
            definitions[ident] = value
            collect(value)
            return
        for value in node.values():
            collect(value)
    elif isinstance(node, list):
        for value in node:
            collect(value)


collect(raw)

resolved: dict[int, HashConsed] = {}


def resolve(ident: int, stack: tuple[int, ...] = ()) -> HashConsed:
    if ident in resolved:
        return resolved[ident]
    if ident not in definitions:
        raise ValueError(f"unresolved Deduplicated id {ident}")
    if ident in stack:
        raise ValueError(f"recursive hash-cons definition for id {ident}: {stack}")
    value = decode(definitions[ident], stack + (ident,))
    result = HashConsed(ident, value)
    resolved[ident] = result
    return result


def decode(node: Any, stack: tuple[int, ...] = ()) -> Any:
    if isinstance(node, dict):
        if set(node) == {"HashConsedValue"}:
            ident, _value = node["HashConsedValue"]
            return resolve(ident, stack)
        if set(node) == {"Deduplicated"}:
            return resolve(node["Deduplicated"], stack)
        return {key: decode(value, stack) for key, value in node.items()}
    if isinstance(node, list):
        return [decode(value, stack) for value in node]
    return node


decoded = decode(raw)
translated_before = decoded["translated"]
rows_before = translated_before["fun_decls"]
found = {row["def_id"] for row in rows_before if row is not None and row["def_id"] in KEEP_BODY_IDS}
if found != KEEP_BODY_IDS:
    raise ValueError(f"target function IDs missing: {sorted(KEEP_BODY_IDS - found)}")

protected_metadata = {
    field: canonical_bytes(translated_before[field])
    for field in ("type_decls", "trait_decls", "trait_impls", "global_decls")
}
protected_signatures = {
    row["def_id"]: canonical_bytes(row.get("signature"))
    for row in rows_before
    if row is not None
}

retained_before: dict[int, bytes] = {}
removed_body_ids: list[int] = []
all_other_ids: list[int] = []
original_body_kinds: dict[str, int] = {}
for row in rows_before:
    if row is None:
        continue
    ident = row["def_id"]
    if ident in KEEP_BODY_IDS:
        retained_before[ident] = canonical_bytes(row)
        continue
    all_other_ids.append(ident)
    old_body = row.get("body")
    if old_body != "Opaque":
        removed_body_ids.append(ident)
        kind = next(iter(old_body)) if isinstance(old_body, dict) else type(old_body).__name__
        original_body_kinds[kind] = original_body_kinds.get(kind, 0) + 1
    row["body"] = "Opaque"
    row["item_meta"]["opacity"] = "Foreign"

# Verify the requested metadata boundary before writing.
for row in translated_before["fun_decls"]:
    if row is not None and row["def_id"] not in KEEP_BODY_IDS:
        assert row["body"] == "Opaque"
        assert row["item_meta"]["opacity"] == "Foreign"

# Re-emit hash-cons values in first-occurrence order. This can move a definition
# out of an erased body while preserving its original ID and decoded value.
seen: set[int] = set()


def encode(node: Any) -> Any:
    if isinstance(node, HashConsed):
        if node.ident in seen:
            return {"Deduplicated": node.ident}
        seen.add(node.ident)
        return {"HashConsedValue": [node.ident, encode(node.value)]}
    if isinstance(node, dict):
        return {key: encode(value) for key, value in node.items()}
    if isinstance(node, list):
        return [encode(value) for value in node]
    return node


encoded = encode(decoded)
output_bytes = (json.dumps(encoded, indent=2, ensure_ascii=False) + "\n").encode()
OUTPUT.write_bytes(output_bytes)

# Decode the actual output and verify every retained function row is unchanged.
output_raw = json.loads(output_bytes)
output_definitions: dict[int, Any] = {}


def collect_output(node: Any) -> None:
    if isinstance(node, dict):
        if set(node) == {"HashConsedValue"}:
            ident, value = node["HashConsedValue"]
            if ident in output_definitions and output_definitions[ident] != value:
                raise ValueError(f"conflicting output definitions for id {ident}")
            output_definitions[ident] = value
            collect_output(value)
            return
        for value in node.values():
            collect_output(value)
    elif isinstance(node, list):
        for value in node:
            collect_output(value)


collect_output(output_raw)
output_resolved: dict[int, HashConsed] = {}


def resolve_output(ident: int, stack: tuple[int, ...] = ()) -> HashConsed:
    if ident in output_resolved:
        return output_resolved[ident]
    if ident not in output_definitions:
        raise ValueError(f"output has unresolved Deduplicated id {ident}")
    if ident in stack:
        raise ValueError(f"recursive output hash-cons definition for id {ident}")
    value = decode_output(output_definitions[ident], stack + (ident,))
    result = HashConsed(ident, value)
    output_resolved[ident] = result
    return result


def decode_output(node: Any, stack: tuple[int, ...] = ()) -> Any:
    if isinstance(node, dict):
        if set(node) == {"HashConsedValue"}:
            return resolve_output(node["HashConsedValue"][0], stack)
        if set(node) == {"Deduplicated"}:
            return resolve_output(node["Deduplicated"], stack)
        return {key: decode_output(value, stack) for key, value in node.items()}
    if isinstance(node, list):
        return [decode_output(value, stack) for value in node]
    return node


decoded_output = decode_output(output_raw)
translated_after = decoded_output["translated"]
rows_after = translated_after["fun_decls"]
for field, before_bytes in protected_metadata.items():
    if canonical_bytes(translated_after[field]) != before_bytes:
        raise ValueError(f"non-function metadata changed: {field}")
for row in rows_after:
    if row is not None and canonical_bytes(row.get("signature")) != protected_signatures[row["def_id"]]:
        raise ValueError(f"function signature changed: {row['def_id']}")
retained_audit = []
for row in rows_after:
    if row is None or row["def_id"] not in KEEP_BODY_IDS:
        continue
    ident = row["def_id"]
    after_sha = sha256(canonical_bytes(row))
    before_sha = sha256(retained_before[ident])
    retained_audit.append({"def_id": ident, "before_decoded_sha256": before_sha, "after_decoded_sha256": after_sha, "equal": before_sha == after_sha})
    if before_sha != after_sha:
        raise ValueError(f"retained function {ident} changed under decoded comparison")

for ident, value in output_resolved.items():
    if ident not in definitions or canonical_bytes(value) != canonical_bytes(resolve(ident)):
        raise ValueError(f"hash-cons ID/value changed in projection: {ident}")
if set(output_resolved) != set(output_definitions):
    raise ValueError("not every output hash-cons definition was decoded")

audit = {
    "script_sha256": sha256(Path(__file__).read_bytes()),
    "input": str(INPUT),
    "input_sha256": sha256(source_bytes),
    "output": str(OUTPUT),
    "output_sha256": sha256(output_bytes),
    "input_hashcons_definition_count": len(definitions),
    "output_hashcons_definition_count": len(output_definitions),
    "output_definition_ids_subset_of_input": set(output_definitions).issubset(definitions),
    "all_output_hashcons_ids_and_values_preserved": True,
    "kept_body_ids": sorted(KEEP_BODY_IDS),
    "retained_function_decoded_sha256_audit": retained_audit,
    "removed_body_ids": sorted(removed_body_ids),
    "removed_body_count_by_original_variant": original_body_kinds,
    "all_other_function_ids_marked_opaque_foreign": sorted(all_other_ids),
    "preserved_non_function_metadata": True,
    "all_function_signatures_unchanged": True,
    "note": "Diagnostic projection only. Opaque functions are not accepted as proof premises; no translation or compilation was run.",
}
(ROOT / "R210-projection-audit.json").write_text(json.dumps(audit, indent=2) + "\n")
(ROOT / "README.md").write_text(
    "# R210 diagnostic projection\n\n"
    "This projection keeps exactly function bodies 9, 49, 50, 91, and 92 from R207. Every other function body is marked `Opaque` and every other function opacity is set to `Foreign`; signatures, types, trait declarations, and trait implementations remain unchanged.\n\n"
    "The projection first decodes the complete global hash-cons table, then re-emits first surviving occurrences as `HashConsedValue` and subsequent references as `Deduplicated`, preserving IDs and decoded values. `R210-projection-audit.json` records input/output hashes, removed body IDs, and per-retained-function decoded SHA equality. This is diagnostic only: opacity is not accepted as a proof premise. No Aeneas translation or compilation was run.\n"
)
print(json.dumps({"input_sha256": audit["input_sha256"], "output_sha256": audit["output_sha256"], "kept_body_ids": audit["kept_body_ids"], "removed_body_count": len(removed_body_ids), "hashcons_in": len(definitions), "hashcons_out": len(output_definitions), "retained_equal": all(x["equal"] for x in retained_audit)}, indent=2))
