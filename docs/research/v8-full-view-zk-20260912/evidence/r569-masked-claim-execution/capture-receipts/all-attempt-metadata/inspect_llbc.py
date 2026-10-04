#!/usr/bin/env python3
"""Mechanical compact inventory of captured R569 LLBC declarations."""
import hashlib, json, pathlib

HERE = pathlib.Path(__file__).resolve().parent
llbc_path = HERE / "R569MaskedClaim.llbc"
raw = llbc_path.read_bytes()
tree = json.loads(raw)
assert tree["has_errors"] is False
translated = tree["translated"]

def path_name(fun):
    meta = fun.get("item_meta") or {}
    parts=[]
    for comp in meta.get("name") or []:
        if isinstance(comp,dict) and "Ident" in comp:
            parts.append(comp["Ident"][0])
    return "::".join(parts) or "<trait/associated item>"

def body_kind(fun):
    body=fun.get("body")
    if body == "Opaque": return "Opaque"
    if isinstance(body,dict) and "Structured" in body: return "Structured"
    return repr(body)

def call_targets(value, out):
    if isinstance(value,dict):
        if "Call" in value:
            call=value["Call"].get("call",{})
            reg=call.get("func",{}).get("Regular",{})
            kind=reg.get("kind",{}).get("Fun")
            if kind is not None:
                if isinstance(kind,dict) and "Regular" in kind:
                    out.append({"kind":"Regular","id":kind["Regular"],"argc":len(call.get("args",[]))})
                else: out.append({"kind":"Builtin","name":kind,"argc":len(call.get("args",[]))})
        for child in value.values(): call_targets(child,out)
    elif isinstance(value,list):
        for child in value: call_targets(child,out)

funcs=[]
for i,fun in enumerate(translated["fun_decls"]):
    if fun is None:
        funcs.append({"id":i,"name":"<null slot>","source_kind":None,"body":"None","body_span":None,"direct_and_nested_call_targets":[]})
        continue
    refs=[]; call_targets(fun.get("body"),refs)
    span=None
    body=fun.get("body")
    if isinstance(body,dict) and "Structured" in body:
        span=body["Structured"].get("span")
    funcs.append({"id":i,"name":path_name(fun),"source_kind":fun.get("src"),"body":body_kind(fun),"body_span":span,"direct_and_nested_call_targets":refs})

result={"llbc_sha256":hashlib.sha256(raw).hexdigest(),"bytes":len(raw),"has_errors":False,"charon_version":tree.get("charon_version"),"target_information":translated.get("target_information"),"options":translated.get("options"),"function_declarations":funcs}
(HERE/"llbc-inventory.json").write_text(json.dumps(result,indent=2)+"\n")
print(json.dumps({"llbc_sha256":result["llbc_sha256"],"function_count":len(funcs),"root":funcs[0],"target":funcs[1]},indent=2))
