#!/usr/bin/env python3
"""Inventory R231 selected methods and reachable declarations from raw LLBC."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
LLBC = ROOT / "R231NormLeaves.llbc"
translated = json.loads(LLBC.read_text())["translated"]
files = {x["id"]: x["name"] for x in translated["files"]}

def name_text(items):
    out = []
    for item in items:
        if "Ident" in item:
            out.append(item["Ident"][0])
        elif "Impl" in item:
            out.append("<impl>")
        elif "Instantiated" in item:
            out.append("<inst>")
        else:
            out.append(json.dumps(item, sort_keys=True))
    return "::".join(out)

def body_kind(f):
    body = f.get("body")
    if isinstance(body, str):
        return body
    if isinstance(body, dict) and "Structured" in body:
        return "Structured"
    if isinstance(body, dict) and "Opaque" in body:
        return "Opaque"
    return type(body).__name__

def walk(obj):
    if isinstance(obj, dict):
        yield obj
        for value in obj.values():
            yield from walk(value)
    elif isinstance(obj, list):
        for value in obj:
            yield from walk(value)

def callees(f):
    out = set()
    for node in walk(f.get("body")):
        call = node.get("Call")
        if not isinstance(call, dict):
            continue
        try:
            fun = call["call"]["func"]["Regular"]["kind"]["Fun"]["Regular"]
            out.add(fun)
        except (KeyError, TypeError):
            pass
    return sorted(out)

functions = [f for f in translated["fun_decls"] if isinstance(f, dict)]
by_id = {f["def_id"]: f for f in functions}
requested = {
    "crate::circle_norm::Coeff::new": 0,
    "crate::circle_norm::Coeff::four": 1,
    "crate::circle_norm::joined_inverse::line_norm::LineCoeff::new": 2,
    "crate::circle_norm::joined_inverse::line_norm::LineCoeff::four": 3,
}
selected = {}
for path, ident in requested.items():
    f = by_id[ident]
    span = f["item_meta"].get("span", {}).get("data", {})
    selected[path] = {
        "def_id": ident,
        "llbc_name_text": name_text(f["item_meta"]["name"]),
        "llbc_name_raw": f["item_meta"]["name"],
        "opacity": f["item_meta"]["opacity"],
        "body_kind": body_kind(f),
        "source_file": files.get(span.get("file_id")),
        "source_span": span,
        "regular_callees": callees(f),
    }
    assert selected[path]["body_kind"] == "Structured"
    assert selected[path]["opacity"] == "Transparent"

reachable = set()
pending = list(requested.values())
while pending:
    ident = pending.pop()
    if ident in reachable or ident not in by_id:
        continue
    reachable.add(ident)
    pending.extend(callees(by_id[ident]))

global_ids = set()
for ident in reachable:
    for node in walk(by_id[ident].get("body")):
        glob = node.get("Global")
        if isinstance(glob, dict) and isinstance(glob.get("id"), int):
            global_ids.add(glob["id"])

global_decls = {g["def_id"]: g for g in translated["global_decls"]}
opaque_functions = [
    {"def_id": i, "name": name_text(by_id[i]["item_meta"]["name"]),
     "opacity": by_id[i]["item_meta"]["opacity"], "body_kind": body_kind(by_id[i])}
    for i in sorted(reachable) if by_id[i]["item_meta"]["opacity"] != "Transparent"
]
opaque_globals = [
    {"def_id": i, "name": name_text(global_decls[i]["item_meta"]["name"]),
     "opacity": global_decls[i]["item_meta"]["opacity"],
     "global_kind": global_decls[i].get("global_kind")}
    for i in sorted(global_ids) if i in global_decls and global_decls[i]["item_meta"]["opacity"] != "Transparent"
]

def decl_summary(f, kind):
    span = f["item_meta"].get("span", {}).get("data", {})
    return {"def_id": f["def_id"], "name": name_text(f["item_meta"]["name"]),
            "opacity": f["item_meta"]["opacity"], "body_kind": body_kind(f),
            "source_file": files.get(span.get("file_id")), "source_span": span,
            "regular_callees": callees(f), "kind": kind}

field_ops = [
    decl_summary(f, "function") for f in functions
    if name_text(f["item_meta"]["name"]).endswith("::mul_m31")
    or name_text(f["item_meta"]["name"]).endswith("::half")
]
assert field_ops and all(x["body_kind"] == "Structured" and x["opacity"] == "Transparent" for x in field_ops)
assert any(x["name"].endswith("::mul_m31") for x in field_ops)
assert sum(x["name"].endswith("::half") for x in field_ops) >= 2

summary = {
    "input_llbc_sha256": hashlib.sha256(LLBC.read_bytes()).hexdigest(),
    "crate_name": translated["crate_name"],
    "declaration_counts": {
        "types": len(translated["type_decls"]), "function_slots": len(translated["fun_decls"]),
        "globals": len(translated["global_decls"]), "traits": len(translated["trait_decls"]),
        "trait_impls": len(translated["trait_impls"]),
    },
    "requested_methods": selected,
    "reachable_function_ids": sorted(reachable),
    "reachable_functions": [decl_summary(by_id[i], "function") for i in sorted(reachable)],
    "reachable_global_ids": sorted(global_ids),
    "reachable_globals": [
        {"def_id": i, "name": name_text(global_decls[i]["item_meta"]["name"]),
         "opacity": global_decls[i]["item_meta"]["opacity"],
         "global_kind": global_decls[i].get("global_kind")}
        for i in sorted(global_ids) if i in global_decls
    ],
    "opaque_frontier_from_requested_methods": {
        "functions": opaque_functions, "globals": opaque_globals,
    },
    "field_half_and_mul_m31": field_ops,
    "all_types": [
        {"def_id": t["def_id"], "name": name_text(t["item_meta"]["name"]),
         "opacity": t["item_meta"]["opacity"]} for t in translated["type_decls"]
    ],
    "traits": [
        {"def_id": t["def_id"], "name": name_text(t["item_meta"]["name"]),
         "opacity": t["item_meta"]["opacity"]} for t in translated["trait_decls"]
    ],
    "trait_impls": [
        {"def_id": t["def_id"], "name": name_text(t["item_meta"]["name"]),
         "opacity": t["item_meta"]["opacity"]} for t in translated["trait_impls"]
    ],
    "scope": "Declaration/body inventory from LLBC only; no Aeneas translation, Lean compilation, or semantic claim.",
}
(ROOT / "llbc-summary.json").write_text(json.dumps(summary, indent=2) + "\n")
print(json.dumps({"input_llbc_sha256": summary["input_llbc_sha256"],
                  "requested_methods": {k: {"def_id": v["def_id"], "body_kind": v["body_kind"], "opacity": v["opacity"], "source_file": v["source_file"], "source_span": v["source_span"]} for k,v in selected.items()},
                  "field_half_mul_m31": field_ops,
                  "opaque_frontier": summary["opaque_frontier_from_requested_methods"]}, indent=2))
