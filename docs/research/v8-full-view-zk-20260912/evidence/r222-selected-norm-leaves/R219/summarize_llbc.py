#!/usr/bin/env python3
"""Summarize declaration inventory for the retained R219 LLBC artifact."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
LLBC = ROOT / "R219NormLeaves.llbc"
d = json.loads(LLBC.read_text())["translated"]
files = {x["id"]: x["name"] for x in d["files"]}

def name_text(items):
    out=[]
    for item in items:
        if "Ident" in item:
            out.append(item["Ident"][0])
        elif "Impl" in item:
            out.append("<impl>")
        elif "Instantiated" in item:
            out.append("<inst>")
        else:
            out.append(json.dumps(item,sort_keys=True))
    return "::".join(out)

functions=[]
for f in d["fun_decls"]:
    if not isinstance(f,dict):
        functions.append(None)
        continue
    span=f["item_meta"].get("span",{}).get("data",{})
    file=files.get(span.get("file_id"))
    body=f.get("body")
    functions.append({
        "def_id":f["def_id"],
        "name_text":name_text(f["item_meta"]["name"]),
        "name_raw":f["item_meta"]["name"],
        "opacity":f["item_meta"]["opacity"],
        "body_kind":body if isinstance(body,str) else "Structured" if isinstance(body,dict) else type(body).__name__,
        "source_file":file,
        "source_span":span,
        "signature":f["signature"],
        "generic_parameters":f["generics"],
    })
roots={
    "crate::circle_norm::norm":0,
    "crate::circle_norm::polar":1,
    "crate::circle_norm::times_r":3,
}
for path, ident in roots.items():
    assert any(isinstance(f,dict) and f["def_id"]==ident for f in d["fun_decls"]),path

summary={
    "input_llbc_sha256":hashlib.sha256(LLBC.read_bytes()).hexdigest(),
    "crate_name":d["crate_name"],
    "counts":{"types":len(d["type_decls"]),"function_slots":len(d["fun_decls"]),"globals":len(d["global_decls"]),"traits":len(d["trait_decls"]),"trait_impls":len(d["trait_impls"])},
    "requested_roots_and_ids":roots,
    "functions":functions,
    "types":[{"def_id":t["def_id"],"name_text":name_text(t["item_meta"]["name"]),"name_raw":t["item_meta"]["name"],"opacity":t["item_meta"]["opacity"],"generic_parameters":t["generics"],"source_file":files.get(t["item_meta"]["span"]["data"]["file_id"]),"source_span":t["item_meta"]["span"]["data"]} for t in d["type_decls"]],
    "scope":"Extraction and declaration inventory only. No Aeneas translation, Lean compilation, or semantic claim.",
}
(ROOT/"llbc-summary.json").write_text(json.dumps(summary,indent=2)+"\n")
