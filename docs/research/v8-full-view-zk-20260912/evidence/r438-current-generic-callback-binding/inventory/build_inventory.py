#!/usr/bin/env python3
"""Deterministically inventory R437 source descriptors and one selected callsite."""
import hashlib, json, collections
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
LLBC = ROOT / ".r21-scratch/r437-pointer-source-boundary/root-launch-a/saved-output/R437PointerWrapperLayout.llbc"
OUT = Path(__file__).resolve().parent

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def walk(v, path=()):
    if isinstance(v, dict):
        yield path, v
        for k,x in v.items(): yield from walk(x, path+(k,))
    elif isinstance(v, list):
        for i,x in enumerate(v): yield from walk(x, path+(i,))

raw=json.loads(LLBC.read_text())
t=raw["translated"]
# Build the serialized hash-cons table without modifying its source forms.
hc={}
for path,node in walk(t):
    val=node.get("HashConsedValue") if isinstance(node,dict) else None
    if isinstance(val,list) and len(val)==2:
        i,v=val
        if i in hc and hc[i] != v: raise ValueError(f"inconsistent hashcons id {i}")
        hc[i]=v

def decode(v):
    if isinstance(v,dict):
        if set(v)=={"HashConsedValue"}:
            return decode(v["HashConsedValue"][1])
        if set(v)=={"Deduplicated"}:
            i=v["Deduplicated"]
            if i not in hc: raise KeyError(f"unresolved hashcons id {i}")
            return decode(hc[i])
        return {k:decode(x) for k,x in v.items()}
    if isinstance(v,list): return [decode(x) for x in v]
    return v

def get_name(kind,i):
    for row in t["item_names"]:
        if row["key"] == {kind:i}: return row["value"]
    return None

sources=[]
exact_matches=[]
fun_slots=[]
for slot_index,f in enumerate(t["fun_decls"]):
    if f is None:
        fun_slots.append({"slot_index":slot_index,"fun_id":None,"name":None,"src":None,"absent_slot":True})
        continue
    src=f.get("src")
    row={"slot_index":slot_index,"fun_id":f["def_id"],"name":f["item_meta"]["name"],"span":f["item_meta"].get("span"),"src":src}
    sources.append(row)
    fun_slots.append({**row,"absent_slot":False})
    if not isinstance(src,dict) or "TraitImpl" not in src: continue
    x=src["TraitImpl"]
    if (x.get("impl_ref",{}).get("id")==35 and x.get("trait_ref",{}).get("id")==3
        and x.get("item_id")=={"Method":0} and x.get("reuses_default") is False):
        exact_matches.append(row)

# Find the exact selected trait call node in specialized Iterator::fold body 70.
f70=next(f for f in t["fun_decls"] if f is not None and f["def_id"]==70)
call_matches=[]
for path,node in walk(f70["body"], ("fun_decls",70,"body")):
    if not isinstance(node,dict) or "Call" not in node: continue
    call=node["Call"].get("call",{})
    reg=call.get("func",{}).get("Regular",{})
    trait=reg.get("kind",{}).get("Trait")
    if not isinstance(trait,list) or len(trait)!=2: continue
    traitref=decode(trait[0])
    methodid=trait[1]
    if (traitref.get("kind",{}).get("TraitImpl",{}).get("id")==35 and methodid==0):
        # Record containing source statement identity, call expression, and
        # opaque result/unwind context separately from the expression itself.
        stmt_index=next((x for x in reversed(path) if isinstance(x,int)),None)
        call_matches.append({"path":list(path),"statement_index":stmt_index,
                             "call":call,"trait_ref_resolved":traitref,
                             "call_kind_method_index":methodid})

f112=next(f for f in t["fun_decls"] if f is not None and f["def_id"]==112)
trait3=t["trait_decls"][3]
impl35=t["trait_impls"][35]
# Resolve type occurrences in the call, closure signature and implemented FnMut ref.
resolved_f112={
 "def_id":f112["def_id"],"name":f112["item_meta"]["name"],"span":f112["item_meta"]["span"],
 "source_text":f112["item_meta"].get("source_text"),"src":f112["src"],
 "generics":decode(f112["generics"]),"signature_raw":f112["signature"],
 "signature_resolved":decode(f112["signature"]),"body_kind":list(f112["body"].keys())}

report={
 "llbc_path":str(LLBC),"llbc_sha256":sha(LLBC),"charon_version":raw.get("charon_version"),
 "declaration_counts":{"fun_decl_slots":len(t["fun_decls"]),"non_null_fun_decls":sum(f is not None for f in t["fun_decls"]),"function_source_descriptor_count":len(sources),"absent_fun_decl_slots":sum(x["absent_slot"] for x in fun_slots),"type_decls":len(t["type_decls"]),"trait_decls":len(t["trait_decls"]),"trait_impls":len(t["trait_impls"]),"item_names":len(t["item_names"]),"assoc_item_names":len(t["assoc_item_names"]),"hashcons_ids":len(hc)},
 "source_variant_counts":dict(sorted(collections.Counter(row["src"] if isinstance(row["src"],str) else (next(iter(row["src"])) if isinstance(row["src"],dict) and row["src"] else "Unknown_source") for row in sources).items())),
 "absent_fun_decl_slot_indices":[x["slot_index"] for x in fun_slots if x["absent_slot"]],
 "all_fun_decl_slots":fun_slots,
 "selector":{"impl_ref_id":35,"trait_ref_id":3,"item_id":{"Method":0},"reuses_default":False,
   "matched_count":len(exact_matches),"matched_fun_ids":[x["fun_id"] for x in exact_matches],"matching_source_descriptors":exact_matches},
 "all_function_source_descriptors":sources,
 "callsite":{"parent_fun_id":70,"parent_name":f70["item_meta"]["name"],"parent_span":f70["item_meta"]["span"],"match_count":len(call_matches),"matches":call_matches},
 "selected_method_function_112":resolved_f112,
 "trait_decl_3":{"def_id":trait3["def_id"],"name":trait3["item_meta"]["name"],"lang_item":trait3["item_meta"].get("lang_item"),"opacity":trait3["item_meta"].get("opacity"),"generics":trait3["generics"],"assoc_item_names":t["assoc_item_names"][3],"methods":trait3["methods"],"method_slot_0_present":len(trait3["methods"])>0},
 "trait_impl_35":{"def_id":impl35["def_id"],"name":impl35["item_meta"]["name"],"source_text":impl35["item_meta"].get("source_text"),"impl_trait":decode(impl35["impl_trait"]),"generics":impl35["generics"],"methods":impl35["methods"],"method_slot_0_present":len(impl35["methods"])>0},
 "interpretation_boundary":"Serialized source-descriptor/call-node facts only. This inventory does not infer execution lookup, dispatch completion, or Rust semantics."
}
if len(exact_matches)!=1 or exact_matches[0]["fun_id"]!=112: raise SystemExit(f"selector was not unique as expected: {report['selector']}")
if len(call_matches)!=1: raise SystemExit(f"expected one Fun70 call node, found {len(call_matches)}")
(OUT/"function-source-descriptors.json").write_text(json.dumps(sources,indent=2,sort_keys=True)+"\n")
(OUT/"function-source-slots.json").write_text(json.dumps(fun_slots,indent=2,sort_keys=True)+"\n")
(OUT/"selector-inventory.json").write_text(json.dumps(report,indent=2,sort_keys=True)+"\n")
print(json.dumps({"status":"PASS","llbc_sha256":report["llbc_sha256"],"declaration_counts":report["declaration_counts"],"matched_function_ids":report["selector"]["matched_fun_ids"],"callsite_match_count":len(call_matches),"trait_decl_3_method_count":len(trait3["methods"]),"trait_impl_35_method_count":len(impl35["methods"])},indent=2))
