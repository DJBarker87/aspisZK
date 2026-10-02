#!/usr/bin/env python3
"""Build an explicitly typed declaration-closure projection of decoded R210 LLBC."""
import copy
import hashlib
import json
from collections import defaultdict, deque
from pathlib import Path

ROOT = Path(__file__).resolve().parent
INPUT = ROOT.parent / "r210-vector-leaf-diagnostic" / "R210VectorLeafDiagnostic.llbc"
RAW_DOC = json.loads(INPUT.read_text())
ORIGINAL = RAW_DOC["translated"]
ROOT_FUNS = {9, 49, 50, 91, 92}
GROUPS = {
    "Type": "type_decls",
    "Fun": "fun_decls",
    "Global": "global_decls",
    "TraitDecl": "trait_decls",
    "TraitImpl": "trait_impls",
}

def digest(data):
    return hashlib.sha256(data).hexdigest()

def json_sha(x):
    return digest(json.dumps(x, sort_keys=True, separators=(",", ":")).encode())

def collect_hashcons(x, table):
    if isinstance(x, dict):
        if "HashConsedValue" in x:
            ident, value = x["HashConsedValue"]
            if ident in table and table[ident] != value:
                raise ValueError(f"conflicting HashConsedValue id {ident}")
            table[ident] = value
            collect_hashcons(value, table)
        elif "Deduplicated" not in x:
            for value in x.values():
                collect_hashcons(value, table)
    elif isinstance(x, list):
        for value in x:
            collect_hashcons(value, table)

HASHCONS = {}
collect_hashcons(RAW_DOC, HASHCONS)

def decode(x, seen=()):
    if isinstance(x, dict):
        if "HashConsedValue" in x:
            ident, value = x["HashConsedValue"]
            if ident in seen:
                return {"cycle_hashcons_id": ident}
            return decode(value, seen + (ident,))
        if "Deduplicated" in x:
            ident = x["Deduplicated"]
            if ident in seen:
                return {"cycle_hashcons_id": ident}
            if ident not in HASHCONS:
                raise ValueError(f"unresolved source hashcons id {ident}")
            return decode(HASHCONS[ident], seen + (ident,))
        return {key: decode(value, seen) for key, value in x.items()}
    if isinstance(x, list):
        return [decode(value, seen) for value in x]
    return x

DECLS = {kind: {row["def_id"]: row for row in ORIGINAL[key] if isinstance(row, dict)} for kind, key in GROUPS.items()}
for ident in ROOT_FUNS:
    if ident not in DECLS["Fun"]:
        raise ValueError(f"missing root function declaration {ident}")

# Source association indexes let the closure retain actual function rows
# belonging to a reachable trait/impl. This uses the explicit `fun.src`
# relationship, not a reverse guess from every trait's possible impls.
IMPL_FUNS = defaultdict(set)
TRAIT_FUNS = defaultdict(set)
for f_id, raw in DECLS["Fun"].items():
    src = decode(raw.get("src"))
    if isinstance(src, dict) and "TraitImpl" in src:
        payload = src["TraitImpl"]
        impl_ref = payload.get("impl_ref", {}) if isinstance(payload, dict) else {}
        if isinstance(impl_ref, dict) and isinstance(impl_ref.get("id"), int):
            IMPL_FUNS[impl_ref["id"]].add(f_id)
    if isinstance(src, dict) and "TraitDecl" in src:
        payload = src["TraitDecl"]
        trait_ref = payload.get("trait_ref", {}) if isinstance(payload, dict) else {}
        if isinstance(trait_ref, dict) and isinstance(trait_ref.get("id"), int):
            TRAIT_FUNS[trait_ref["id"]].add(f_id)

def references(x, path="$", refs=None, unknown=None):
    """Collect only schema-shaped declaration references, never arbitrary ints."""
    refs = [] if refs is None else refs
    unknown = [] if unknown is None else unknown
    if isinstance(x, dict):
        # LLBC type references are carried by an Adt id (or a direct Adt tag).
        if isinstance(x.get("id"), dict) and set(x["id"]) == {"Adt"} and isinstance(x["id"]["Adt"], int):
            refs.append(("Type", x["id"]["Adt"], path + ".id.Adt"))
        # Aggregate/type forms may carry an Adt declaration ID directly.
        if set(x) == {"Adt"} and isinstance(x["Adt"], int):
            refs.append(("Type", x["Adt"], path + ".Adt"))
        # The `Impl::Trait(id)` name variant is a TraitImpl ID in Charon names.
        impl_name = x.get("Impl")
        if isinstance(impl_name, dict) and set(impl_name) == {"Trait"} and isinstance(impl_name["Trait"], int):
            refs.append(("TraitImpl", impl_name["Trait"], path + ".Impl.Trait"))
        # Regular function operands identify concrete function declarations.
        if isinstance(x.get("Fun"), dict):
            fun_variant = x["Fun"]
            if set(fun_variant) == {"Regular"} and isinstance(fun_variant["Regular"], int):
                refs.append(("Fun", fun_variant["Regular"], path + ".Fun.Regular"))
            elif set(fun_variant) == {"Builtin"}:
                pass
            elif "TraitMethod" in fun_variant:
                # A trait method reference selects a declaration but not a
                # concrete implementation. Record it as an unresolved dispatch
                # frontier unless the LLBC form carries an explicit impl ID.
                unknown.append({"path": path + ".Fun.TraitMethod", "value": fun_variant["TraitMethod"], "reason": "trait method dispatch does not name a concrete function row"})
            else:
                unknown.append({"path": path + ".Fun", "value": fun_variant, "reason": "unclassified function-reference variant"})
        if set(x) == {"Global"} and isinstance(x["Global"], int):
            refs.append(("Global", x["Global"], path + ".Global"))
        if set(x) == {"TraitDecl"} and isinstance(x["TraitDecl"], int):
            refs.append(("TraitDecl", x["TraitDecl"], path + ".TraitDecl"))
        if set(x) == {"TraitImpl"} and isinstance(x["TraitImpl"], int):
            refs.append(("TraitImpl", x["TraitImpl"], path + ".TraitImpl"))
        if set(x) == {"TraitMethod"} and isinstance(x["TraitMethod"], list) and len(x["TraitMethod"]) == 2 and isinstance(x["TraitMethod"][0], int):
            refs.append(("TraitDecl", x["TraitMethod"][0], path + ".TraitMethod[0]"))
        # Trait implementation/reference records carry declaration IDs here.
        for key, kind in (("impl_ref", "TraitImpl"), ("trait_ref", "TraitDecl"), ("impl_trait", "TraitDecl")):
            value = x.get(key)
            if isinstance(value, dict) and isinstance(value.get("id"), int):
                refs.append((kind, value["id"], path + f".{key}.id"))
        # Charon's standalone trait reference tag occurs in a small set of
        # explicit declaration-reference positions (not every integer named id).
        if "TraitDecl" in x and isinstance(x["TraitDecl"], dict):
            payload = x["TraitDecl"]
            tr = payload.get("trait_ref")
            if isinstance(tr, dict) and isinstance(tr.get("id"), int):
                refs.append(("TraitDecl", tr["id"], path + ".TraitDecl.trait_ref.id"))
        for key, value in x.items():
            references(value, path + "." + key, refs, unknown)
    elif isinstance(x, list):
        for i, value in enumerate(x):
            references(value, f"{path}[{i}]", refs, unknown)
    return refs, unknown

def item_key(row):
    key = row["key"]
    if isinstance(key, dict) and len(key) == 1:
        kind, ident = next(iter(key.items()))
        if kind in GROUPS and isinstance(ident, int):
            return kind, ident
    return None

def metadata_for(kind, ident):
    result=[]
    for row in ORIGINAL.get("item_names", []):
        if item_key(row) == (kind, ident):
            result.append(("item_names", row["value"]))
    for row in ORIGINAL.get("short_names", []):
        if item_key(row) == (kind, ident):
            result.append(("short_names", row["value"]))
    return result

closure = {k: set() for k in GROUPS}
queue = deque()
edges=[]
unknown_frontiers=[]

def enqueue(kind, ident, source, path):
    if kind not in DECLS or ident not in DECLS[kind]:
        raise ValueError(f"unresolved {kind} reference {ident} from {source} at {path}")
    edges.append({"from":source,"to":{"kind":kind,"id":ident},"path":path})
    if ident not in closure[kind]:
        closure[kind].add(ident)
        queue.append((kind,ident))

for ident in sorted(ROOT_FUNS):
    enqueue("Fun", ident, "root", "R210 root set")

processed=set()
while queue:
    kind, ident = queue.popleft()
    node=(kind,ident)
    if node in processed:
        continue
    processed.add(node)
    raw=DECLS[kind][ident]
    decoded=decode(raw)
    refs, unknown=references(decoded, f"{kind}[{ident}]")
    unknown_frontiers.extend(unknown)
    for target_kind,target_id,path in refs:
        enqueue(target_kind,target_id,f"{kind}[{ident}]",path)
    # Preserve declaration-name metadata that can contain instantiated type or
    # trait references, but only for the currently reachable declaration.
    for table_name, value in metadata_for(kind, ident):
        refs, unknown=references(decode(value), f"{table_name}[{kind}:{ident}]")
        unknown_frontiers.extend(unknown)
        for target_kind,target_id,path in refs:
            enqueue(target_kind,target_id,f"{table_name}[{kind}:{ident}]",path)
    if kind == "TraitImpl":
        for f_id in sorted(IMPL_FUNS.get(ident, ())):
            enqueue("Fun",f_id,f"TraitImpl[{ident}]","associated fun.src TraitImpl reverse index")
    elif kind == "TraitDecl":
        for f_id in sorted(TRAIT_FUNS.get(ident, ())):
            enqueue("Fun",f_id,f"TraitDecl[{ident}]","associated fun.src TraitDecl reverse index")

def rows_with_nulls(category):
    keep=closure[category]
    return [row if isinstance(row,dict) and row["def_id"] in keep else None for row in ORIGINAL[GROUPS[category]]]

projected_doc=copy.deepcopy(RAW_DOC)
P=projected_doc["translated"]
for kind, key in GROUPS.items():
    P[key]=rows_with_nulls(kind)
P["item_names"]=[row for row in ORIGINAL["item_names"] if item_key(row) and item_key(row)[1] in closure[item_key(row)[0]]]
P["short_names"]=[row for row in ORIGINAL["short_names"] if item_key(row) and item_key(row)[1] in closure[item_key(row)[0]]]
# This side table is indexed by TraitDecl ID and contains only associated-item
# names, not declaration references. Preserve it whole to keep index metadata.
P["assoc_item_names"]=copy.deepcopy(ORIGINAL["assoc_item_names"])
def ordered_key(row):
    if isinstance(row,dict) and len(row)==1:
        outer, inner=next(iter(row.items()))
        if outer in GROUPS and isinstance(inner,dict) and len(inner)==1:
            _,ident=next(iter(inner.items()))
            if isinstance(ident,int): return outer,ident
    return None
P["ordered_decls"]=[row for row in ORIGINAL["ordered_decls"] if ordered_key(row) and ordered_key(row)[1] in closure[ordered_key(row)[0]]]

# Re-emit every referenced hash-cons ID using its original number/value. The
# first kept occurrence defines the original ID; subsequent occurrences dedup.
emitted=set()
def rehashcons(x):
    if isinstance(x,dict):
        if "HashConsedValue" in x:
            ident=x["HashConsedValue"][0]
            if ident not in HASHCONS: raise ValueError(f"missing original hashcons {ident}")
            if ident in emitted: return {"Deduplicated":ident}
            emitted.add(ident)
            return {"HashConsedValue":[ident,rehashcons(HASHCONS[ident])]}
        if "Deduplicated" in x:
            ident=x["Deduplicated"]
            if ident not in HASHCONS: raise ValueError(f"missing original hashcons {ident}")
            if ident in emitted: return {"Deduplicated":ident}
            emitted.add(ident)
            return {"HashConsedValue":[ident,rehashcons(HASHCONS[ident])]}
        return {key:rehashcons(value) for key,value in x.items()}
    if isinstance(x,list): return [rehashcons(value) for value in x]
    return x

serialized=rehashcons(projected_doc)
output=ROOT/"R220ReachableProjection.llbc"
output.write_text(json.dumps(serialized,indent=2)+"\n")

OUT=json.loads(output.read_text())["translated"]
OUT_TABLE={}
collect_hashcons(json.loads(output.read_text()),OUT_TABLE)

def decode_with(table,x,seen=()):
    if isinstance(x,dict):
        if "HashConsedValue" in x:
            i,v=x["HashConsedValue"]
            return decode_with(table,v,seen+(i,))
        if "Deduplicated" in x:
            i=x["Deduplicated"]
            if i in seen: return {"cycle_hashcons_id":i}
            if i not in table: raise ValueError(f"output dangling HashConsed id {i}")
            return decode_with(table,table[i],seen+(i,))
        return {k:decode_with(table,v,seen) for k,v in x.items()}
    if isinstance(x,list): return [decode_with(table,v,seen) for v in x]
    return x

row_equality=[]
for kind,key in GROUPS.items():
    for ident in sorted(closure[kind]):
        original_row=DECLS[kind][ident]
        projected_row=next(row for row in OUT[key] if isinstance(row,dict) and row["def_id"]==ident)
        equal=decode(original_row)==decode_with(OUT_TABLE,projected_row)
        row_equality.append({"kind":kind,"id":ident,"decoded_equal":equal,"decoded_sha256":json_sha(decode(original_row))})
        if not equal: raise ValueError(f"retained decoded row changed: {kind}[{ident}]")

# Verify typed references in each retained declaration and selected keyed name
# row all point into the retained closure and still exist in the original.
unresolved=[]
for kind,key in GROUPS.items():
    for row in OUT[key]:
        if not isinstance(row,dict):continue
        refs,unknown=references(decode_with(OUT_TABLE,row),f"{kind}[{row['def_id']}]")
        unknown_frontiers.extend(unknown)
        for target_kind,target_id,path in refs:
            if target_id not in closure[target_kind] or target_id not in DECLS[target_kind]:
                unresolved.append({"from":{"kind":kind,"id":row['def_id']},"target":{"kind":target_kind,"id":target_id},"path":path})
for key in ("item_names","short_names"):
    for row in OUT[key]:
        kind,ident=item_key(row)
        refs,unknown=references(decode_with(OUT_TABLE,row["value"]),f"{key}[{kind}:{ident}]")
        unknown_frontiers.extend(unknown)
        for target_kind,target_id,path in refs:
            if target_id not in closure[target_kind] or target_id not in DECLS[target_kind]:
                unresolved.append({"from":{"kind":kind,"id":ident,"table":key},"target":{"kind":target_kind,"id":target_id},"path":path})
if unresolved: raise ValueError(f"unresolved projection references: {unresolved[:10]}")

# Verify typed metadata indices after projection.
for key,rows in (("item_names",OUT["item_names"]),("short_names",OUT["short_names"])):
    for row in rows:
        k,i=item_key(row)
        if k not in closure or i not in closure[k]: raise ValueError(f"bad {key} key {row['key']}")
for row in OUT["ordered_decls"]:
    k,i=ordered_key(row)
    if k not in closure or i not in closure[k]: raise ValueError(f"bad ordered declaration {row}")

def count_copy(x):
    if isinstance(x,dict):
        return (1 if "CopyNonOverlapping" in x else 0)+sum(count_copy(v) for v in x.values())
    if isinstance(x,list):return sum(count_copy(v) for v in x)
    return 0
copy_nodes=sum(count_copy(decode_with(OUT_TABLE,row)) for row in OUT["fun_decls"] if isinstance(row,dict))
if not copy_nodes: raise ValueError("CopyNonOverlapping statement was erased from kept bodies")

original_ordered=set()
for row in ORIGINAL["ordered_decls"]:
    k,i=ordered_key(row)
    if k:original_ordered.add((k,i))
output_ordered={(ordered_key(row)[0],ordered_key(row)[1]) for row in OUT["ordered_decls"]}
if output_ordered != {(k,i) for k,ids in closure.items() for i in ids if (k,i) in original_ordered}:
    raise ValueError("ordered declarations do not match retained closure rows")

report={
    "input_path":str(INPUT),
    "input_sha256":digest(INPUT.read_bytes()),
    "output_path":str(output),
    "output_sha256":digest(output.read_bytes()),
    "root_functions":sorted(ROOT_FUNS),
    "closure_ids":{kind:sorted(ids) for kind,ids in closure.items()},
    "kept_counts":{kind:len(ids) for kind,ids in closure.items()},
    "original_counts":{kind:len(DECLS[kind]) for kind in GROUPS},
    "removed_ids":{kind:sorted(set(DECLS[kind])-closure[kind]) for kind in GROUPS},
    "type_53_reachable":53 in closure["Type"],
    "fun_78_reachable":78 in closure["Fun"],
    "trait_impl_40_reachable":40 in closure["TraitImpl"],
    "decoded_retained_row_equalities":row_equality,
    "all_retained_rows_equal_original":all(x["decoded_equal"] for x in row_equality),
    "typed_references_unresolved":unresolved,
    "unknown_reference_frontiers":unknown_frontiers,
    "hashcons":{
        "original_definition_count":len(HASHCONS),
        "output_definition_count":len(OUT_TABLE),
        "output_ids_subset_of_original":set(OUT_TABLE)<=set(HASHCONS),
        "output_values_equal_original_for_every_retained_id":all(decode(HASHCONS[i])==decode_with(OUT_TABLE,OUT_TABLE[i]) for i in OUT_TABLE),
        "retained_ids":sorted(OUT_TABLE),
        "dropped_unreferenced_original_ids":sorted(set(HASHCONS)-set(OUT_TABLE)),
    },
    "metadata":{
        "source_file_table_preserved":OUT["files"]==ORIGINAL["files"],
        "assoc_item_names_length_original":len(ORIGINAL["assoc_item_names"]),
        "assoc_item_names_length_projected":len(OUT["assoc_item_names"]),
        "assoc_item_names_values_preserved":OUT["assoc_item_names"]==ORIGINAL["assoc_item_names"],
        "declaration_list_lengths_original":{GROUPS[k]:len(ORIGINAL[GROUPS[k]]) for k in GROUPS},
        "declaration_list_lengths_projected":{GROUPS[k]:len(OUT[GROUPS[k]]) for k in GROUPS},
        "ordered_declarations_filtered":len(OUT["ordered_decls"]),
    },
    "preserved_copy_nonoverlapping_node_count":copy_nodes,
    "schema_reference_kinds": ["Type via Adt", "Fun via Fun.Regular", "Global via Global", "TraitDecl via TraitDecl/TraitMethod/trait_ref/impl_trait", "TraitImpl via TraitImpl/impl_ref/Impl.Trait", "source associations via fun.src"],
    "scope":"Diagnostic projection only; no compiler/translator run and no semantic premise adopted.",
}
(ROOT/"projection-audit.json").write_text(json.dumps(report,indent=2)+"\n")
(ROOT/"dependency-edges.json").write_text(json.dumps(edges,indent=2)+"\n")
