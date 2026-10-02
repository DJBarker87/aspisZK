#!/usr/bin/env python3
"""Read-only structural audit of the original R283 Charon ordered_decls."""
import collections, hashlib, json, pathlib
ROOT = pathlib.Path(__file__).resolve().parent
INPUT = ROOT.parent / "r283-private-norm-batch-extract/R283PrivateNormBatch.llbc"
PINNED = ROOT.parent / "r267-private-inverse-leaf-ordering/pinned-reorder_decls.rs"
EXPECTED_INPUT_SHA256 = "999fdb4f5a034faf9d4aa11c7a44851b9c79f471d76ae6afb3b92aed0767c8d5"
EXPECTED_PINNED_SHA256 = "8a1176e29a51a83c82ff5a7df2aa11021e3e0c254e9fd6c656c0a92314ba2632"
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(INPUT) == EXPECTED_INPUT_SHA256
assert sha(PINNED) == EXPECTED_PINNED_SHA256
raw = json.loads(INPUT.read_text())
t = raw["translated"]
assert raw["has_errors"] is False
row_keys = {"Type":"type_decls", "Fun":"fun_decls", "Global":"global_decls",
            "TraitDecl":"trait_decls", "TraitImpl":"trait_impls"}
rows = {kind:{row["def_id"]:row for row in t[key] if isinstance(row,dict) and isinstance(row.get("def_id"),int)}
        for kind,key in row_keys.items()}
counts = collections.Counter()
seen = collections.defaultdict(list)
groups = []
for pos, group in enumerate(t["ordered_decls"]):
    assert isinstance(group,dict) and len(group)==1, (pos,group)
    kind,payload = next(iter(group.items()))
    assert kind in row_keys, (pos,kind)
    assert isinstance(payload,dict) and len(payload)==1, (pos,payload)
    variant, value = next(iter(payload.items()))
    assert variant in ("NonRec","Rec"), (pos,variant)
    ids = [value] if variant=="NonRec" and isinstance(value,int) else value if variant=="Rec" and isinstance(value,list) else None
    assert ids and all(isinstance(i,int) for i in ids), (pos,variant,value)
    if variant=="NonRec": assert len(ids)==1, (pos,ids)
    if variant=="Rec": assert len(ids)>=1, (pos,ids)
    assert len(set(ids))==len(ids), (pos,ids)
    for ident in ids:
        assert ident in rows[kind], (pos,kind,ident,"missing/null row")
        seen[(kind,ident)].append(pos)
    counts[kind]+=1
    groups.append({"position":pos,"kind":kind,"variant":variant,"ids":ids})
assert all(len(poss)==1 for poss in seen.values())
assert len(t["ordered_decls"])==109
assert seen[("Fun",0)]==[107]
assert groups[107]=={"position":107,"kind":"Fun","variant":"NonRec","ids":[0]}
rec_groups=[g for g in groups if g["variant"]=="Rec"]
assert rec_groups==[
 {"position":18,"kind":"TraitDecl","variant":"Rec","ids":[1,7,0]},
 {"position":23,"kind":"TraitImpl","variant":"Rec","ids":[4]},
 {"position":25,"kind":"TraitImpl","variant":"Rec","ids":[15]},
 {"position":33,"kind":"TraitImpl","variant":"Rec","ids":[11]},
 {"position":64,"kind":"TraitImpl","variant":"Rec","ids":[2]},
]
def name_path(row):
    parts=[]
    for part in row["item_meta"]["name"]:
        if "Ident" in part: parts.append(part["Ident"][0])
        elif "Impl" in part: parts.append("Impl(Trait "+str(part["Impl"].get("Trait"))+ ")")
        else: parts.append(str(part))
    return "::".join(parts)
rec_self_items=[]
for g in rec_groups:
    if g["kind"]=="TraitImpl" and len(g["ids"])==1:
        i=g["ids"][0]; row=rows["TraitImpl"][i]
        rec_self_items.append({"id":i,"name":name_path(row),"span":row["item_meta"]["span"],
                               "existing_group":{"TraitImpl":{"Rec":[i]}}})
root_row=rows["Fun"][0]
root_name=name_path(root_row)
assert root_row["item_meta"]["is_local"] is True
assert root_row.get("body") not in (None,"Opaque")
report={
 "input_path":str(INPUT),"input_sha256":sha(INPUT),"pinned_reorder_path":str(PINNED),"pinned_reorder_sha256":sha(PINNED),
 "has_errors":raw["has_errors"],"ordered_decls_count":len(groups),"group_counts":dict(counts),
 "listed_declarations":len(seen),"duplicate_ids":[],"missing_or_null_row_ids":[],
 "root_fun0":{"group_index":107,"encoding":{"Fun":{"NonRec":0}},"name":root_name,"local":True,"body_present":True},
 "rec_groups":rec_groups,"singleton_recursive_trait_impls":rec_self_items,
 "all_group_ids_resolve_to_nonnull_rows":True,"all_listed_declarations_unique":True,
 "complete_group_inventory":groups,
 "row_table_slot_counts":{kind:len(t[key]) for kind,key in row_keys.items()},
 "nonnull_row_counts":{kind:len(rows[kind]) for kind in row_keys},
 "same_input_sha256_in_R288_and_R290":{
  "R288":sha(ROOT.parent/"r288-private-batch-ordering/R283PrivateNormBatch.input.llbc"),
  "R290":sha(ROOT.parent/"r290-private-batch-ordering/R283PrivateNormBatch.input.llbc")},
 "manual_subset_order_diagnostics_are_distinct_and_unneeded_for_original_order":True,
 "scope":"Structural audit of original serialized declaration-group metadata and ID resolution; no graph recomputation, translation, or source theorem."
}
for key,h in report["same_input_sha256_in_R288_and_R290"].items(): assert h==report["input_sha256"], (key,h)
(ROOT/"audit.json").write_text(json.dumps(report,indent=2)+"\n")
print(json.dumps({k:report[k] for k in ("has_errors","ordered_decls_count","group_counts","listed_declarations","root_fun0","rec_groups","singleton_recursive_trait_impls","all_group_ids_resolve_to_nonnull_rows","same_input_sha256_in_R288_and_R290")},indent=2))
