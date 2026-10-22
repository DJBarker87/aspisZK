#!/usr/bin/env python3
"""Candidate-only LLBC peephole for the scoped from_fn .len() reborrow.

This is deliberately not a general `Copy &mut` rewrite.  It accepts only one
adjacent pattern in core::array::try_from_fn_erased: a temporary mutable-ref
copy from Guard.array_mut immediately followed by a shared Ref through that
temporary, where every temporary occurrence belongs to that assignment or
that exact Ref's place/metadata.  The Ref region and all other LLBC fields are
preserved.  Any extra use, different projection, or intervening statement is
rejected.
"""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
from pathlib import Path
from typing import Any


EXPECTED_INPUT_SHA = "0186f6da6d3f44d77f49b5abd76b48507635e7a545a54ad63494a0492f1e490e"
FUNCTION_ID = 11  # core::array::try_from_fn_erased in retained v2 LLBC
GUARD_ADT_ID = 9


class NoMatch(ValueError):
    pass


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def local_id(node: Any) -> int | None:
    if not isinstance(node, dict):
        return None
    kind = node.get("kind")
    if isinstance(kind, dict) and set(kind) == {"Local"}:
        return kind["Local"]
    return None


def contains_local(node: Any, wanted: int) -> int:
    if isinstance(node, dict):
        count = int(local_id(node) == wanted)
        return count + sum(contains_local(v, wanted) for v in node.values())
    if isinstance(node, list):
        return sum(contains_local(v, wanted) for v in node)
    return 0


def collect_hashconsed(node: Any, out: dict[int, Any]) -> None:
    if isinstance(node, dict):
        pair = node.get("HashConsedValue")
        if isinstance(pair, list) and len(pair) == 2 and isinstance(pair[0], int):
            out[pair[0]] = pair[1]
        for value in node.values():
            collect_hashconsed(value, out)
    elif isinstance(node, list):
        for value in node:
            collect_hashconsed(value, out)


def resolve_type_ids(node: Any, hashconsed: dict[int, Any], seen: frozenset[int] = frozenset()) -> Any:
    """Expand hash-cons wrappers while preserving all actual type/region data."""
    if isinstance(node, dict):
        if set(node) == {"HashConsedValue"}:
            return resolve_type_ids(node["HashConsedValue"][1], hashconsed, seen)
        if set(node) == {"Deduplicated"}:
            ident = node["Deduplicated"]
            if ident in seen or ident not in hashconsed:
                return ("Deduplicated", ident)
            return resolve_type_ids(hashconsed[ident], hashconsed, seen | {ident})
        return {key: resolve_type_ids(value, hashconsed, seen) for key, value in node.items()}
    if isinstance(node, list):
        return [resolve_type_ids(value, hashconsed, seen) for value in node]
    return node


def outer_mut_ref_inner(node: Any, hashconsed: dict[int, Any]) -> Any | None:
    """Return the exact referent type, ignoring only the outer Ref region."""
    resolved = resolve_type_ids(node, hashconsed)
    if not isinstance(resolved, dict) or set(resolved) != {"Ref"}:
        return None
    ref = resolved["Ref"]
    if not isinstance(ref, list) or len(ref) != 3 or ref[2] != "Mut":
        return None
    return resolve_type_ids(ref[1], hashconsed)


def replace_local(node: Any, wanted: int, replacement: Any) -> Any:
    if local_id(node) == wanted:
        return copy.deepcopy(replacement)
    if isinstance(node, dict):
        return {k: replace_local(v, wanted, replacement) for k, v in node.items()}
    if isinstance(node, list):
        return [replace_local(v, wanted, replacement) for v in node]
    return node


def target_function(doc: dict[str, Any]) -> dict[str, Any]:
    crate = doc.get("translated")
    if not isinstance(crate, dict):
        raise NoMatch("missing translated crate")
    matches = [
        f for f in crate.get("fun_decls", [])
        if isinstance(f, dict) and f.get("def_id") == FUNCTION_ID
    ]
    if len(matches) != 1:
        raise NoMatch(f"expected one function def_id {FUNCTION_ID}, found {len(matches)}")
    fun = matches[0]
    name = fun.get("item_meta", {}).get("name", [])
    if [part.get("Ident", [None])[0] for part in name] != ["core", "array", "try_from_fn_erased"]:
        raise NoMatch("def_id 11 is not core::array::try_from_fn_erased")
    return fun


def is_guard_field_zero(place: Any) -> bool:
    if not isinstance(place, dict):
        return False
    projection = place.get("kind", {}).get("Projection")
    if not isinstance(projection, list) or len(projection) != 2:
        return False
    base, proj = projection
    return (
        local_id(base) == 3
        and isinstance(proj, dict)
        and proj.get("Field") == [{"Adt": [GUARD_ADT_ID, None]}, 0]
    )


def find_pattern(fun: dict[str, Any]) -> tuple[list[dict[str, Any]], int, dict[str, Any], int]:
    structured = fun.get("body", {}).get("Structured")
    if not isinstance(structured, dict):
        raise NoMatch("target function has no Structured body")
    locals_ = structured.get("locals", {}).get("locals", [])
    hashconsed: dict[int, Any] = {}
    collect_hashconsed(fun, hashconsed)
    body = structured.get("body", {})
    outer = body.get("statements", [])
    loops = [s for s in outer if isinstance(s.get("kind"), dict) and "Loop" in s["kind"]]
    if len(loops) != 1:
        raise NoMatch(f"expected one top-level loop, found {len(loops)}")
    statements = loops[0]["kind"]["Loop"].get("statements", [])

    hits: list[tuple[int, int, dict[str, Any], int]] = []
    for i in range(len(statements) - 1):
        lhs_stmt, ref_stmt = statements[i], statements[i + 1]
        lhs_kind = lhs_stmt.get("kind", {})
        ref_kind = ref_stmt.get("kind", {})
        if "Assign" not in lhs_kind or "Assign" not in ref_kind:
            continue
        dst, rhs = lhs_kind["Assign"]
        temp = local_id(dst)
        if temp is None:
            continue
        use = rhs.get("Use") if isinstance(rhs, dict) else None
        if not isinstance(use, list) or len(use) != 2 or use[1] != "No":
            continue
        copied = use[0].get("Copy") if isinstance(use[0], dict) else None
        if not isinstance(copied, dict) or not is_guard_field_zero(copied):
            continue

        ref_rhs = ref_kind["Assign"][1]
        ref = ref_rhs.get("Ref") if isinstance(ref_rhs, dict) else None
        if not isinstance(ref, dict) or ref.get("kind") != "Shared":
            continue
        rplace = ref.get("place", {})
        deref = rplace.get("kind", {}).get("Projection")
        if not isinstance(deref, list) or len(deref) != 2 or deref[1] != "Deref" or local_id(deref[0]) != temp:
            continue
        metadata = ref.get("ptr_metadata", {}).get("Copy", {})
        metadata_projection = metadata.get("kind", {}).get("Projection")
        if (
            not isinstance(metadata_projection, list)
            or len(metadata_projection) != 2
            or local_id(metadata_projection[0]) != temp
            or metadata_projection[1] != "PtrMetadata"
        ):
            continue
        dst_inner = outer_mut_ref_inner(dst.get("ty"), hashconsed)
        copied_inner = outer_mut_ref_inner(copied.get("ty"), hashconsed)
        local_inner = outer_mut_ref_inner(locals_[temp].get("ty"), hashconsed) if temp < len(locals_) else None
        if (
            dst_inner is None
            or copied_inner is None
            or local_inner is None
            or dst_inner != copied_inner
            or local_inner != copied_inner
        ):
            continue
        if not locals_ or temp >= len(locals_):
            continue
        # This is the exact LLBC reborrow: the field is &mut [T], while the
        # next statement creates a shorter shared Ref to the slice behind it.
        hits.append((i, temp, copied, copied["ty"]))

    if len(hits) != 1:
        raise NoMatch(f"expected one adjacent candidate pattern, found {len(hits)}")
    i, temp, original_place, _ = hits[0]
    lhs_stmt, ref_stmt = statements[i], statements[i + 1]

    # The temporary may appear as assignment destination and exactly twice in
    # the following Ref (referent and pointer metadata), and nowhere else.
    total = contains_local(body, temp)
    if total != 3:
        raise NoMatch(f"temporary local {temp} has {total} body occurrences, expected 3")
    if lhs_stmt.get("span") != ref_stmt.get("span"):
        raise NoMatch("copy and Ref source spans differ")
    if lhs_stmt.get("id") == ref_stmt.get("id"):
        raise NoMatch("statement ids are not distinct")
    return statements, i, original_place, temp


def transform_doc(doc: dict[str, Any]) -> tuple[dict[str, Any], dict[str, Any]]:
    out = copy.deepcopy(doc)
    fun = target_function(out)
    statements, i, original_place, temp = find_pattern(fun)
    ref_kind = statements[i + 1]["kind"]["Assign"][1]["Ref"]
    # Keep the existing Ref node, its Shared kind, pointer-metadata Copy, and
    # all region/span/type metadata. Only substitute the base place for the
    # temporary with the exact original projected Guard field place.
    ref_kind["place"]["kind"]["Projection"][0] = copy.deepcopy(original_place)
    ref_kind["ptr_metadata"]["Copy"]["kind"]["Projection"][0] = copy.deepcopy(original_place)
    removed = statements.pop(i)
    return out, {
        "function_def_id": FUNCTION_ID,
        "copy_stmt_id": removed.get("id"),
        "ref_stmt_id": statements[i].get("id"),
        "temporary_local": temp,
        "copy_span": removed.get("span"),
        "ref_span": statements[i].get("span"),
        "ref_region_preserved": True,
        "temporary_use_count_before": 3,
        "operation": "eliminate transient Copy<&mut> by reborrowing shared from original projected place",
    }


def add_negative_extra_use(doc: dict[str, Any]) -> dict[str, Any]:
    """Add a second harmless shared reborrow from the temp; matcher must refuse."""
    out = copy.deepcopy(doc)
    fun = target_function(out)
    statements, i, _, temp = find_pattern(fun)
    structured = fun["body"]["Structured"]
    locals_ = structured["locals"]["locals"]
    local8 = locals_[8]
    new_index = len(locals_)
    new_local = copy.deepcopy(local8)
    new_local["index"] = new_index
    new_local["name"] = "candidate_extra_shared_borrow"
    locals_.append(new_local)
    extra = copy.deepcopy(statements[i + 1])
    extra["id"] = max(s.get("id", -1) for s in statements) + 1
    extra["kind"]["Assign"][0] = {"kind": {"Local": new_index}, "ty": copy.deepcopy(local8["ty"])}
    statements.insert(i + 2, extra)
    if contains_local(fun["body"]["Structured"]["body"], temp) <= 3:
        raise AssertionError("negative fixture did not introduce an extra temp use")
    return out


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("input", type=Path)
    ap.add_argument("output", type=Path)
    ap.add_argument("--allow-nonpinned-input", action="store_true")
    args = ap.parse_args()
    digest = sha256(args.input)
    if digest != EXPECTED_INPUT_SHA and not args.allow_nonpinned_input:
        raise SystemExit(f"input SHA {digest} != pinned {EXPECTED_INPUT_SHA}")
    doc = json.loads(args.input.read_text())
    out, receipt = transform_doc(doc)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(out, separators=(",", ":")) + "\n")
    receipt.update(input_sha256=digest, output_sha256=sha256(args.output))
    print(json.dumps(receipt, indent=2))


if __name__ == "__main__":
    main()
