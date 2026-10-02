#!/usr/bin/env python3
"""Extract the R210 Option<&mut M31> declaration provenance without translation."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
R207 = ROOT.parent / "r207-vector-copy" / "R207VectorCopy.llbc"
R210 = ROOT.parent / "r210-vector-leaf-diagnostic" / "R210VectorLeafDiagnostic.llbc"

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def read(path):
    return json.loads(path.read_text())["translated"]

def hashcons_table(obj):
    table = {}
    def visit(x):
        if isinstance(x, dict):
            if "HashConsedValue" in x:
                ident, value = x["HashConsedValue"]
                table[ident] = value
                visit(value)
            elif "Deduplicated" not in x:
                for value in x.values():
                    visit(value)
        elif isinstance(x, list):
            for value in x:
                visit(value)
    visit(obj)
    return table

def expand(x, table, seen=()):
    if isinstance(x, dict):
        if "Deduplicated" in x:
            ident = x["Deduplicated"]
            if ident in seen:
                return {"cycle": ident}
            return expand(table.get(ident, {"missing_hashcons_id": ident}), table, seen + (ident,))
        if "HashConsedValue" in x:
            ident, value = x["HashConsedValue"]
            return expand(value, table, seen + (ident,))
        return {key: expand(value, table, seen) for key, value in x.items()}
    if isinstance(x, list):
        return [expand(value, table, seen) for value in x]
    return x

def decl_map(items):
    return {item["def_id"]: item for item in items if isinstance(item, dict)}

def find_adts(x, target, path="$", hits=None):
    if hits is None:
        hits = []
    if isinstance(x, dict):
        if x.get("id") == {"Adt": target}:
            hits.append(path)
        for key, value in x.items():
            find_adts(value, target, f"{path}.{key}", hits)
    elif isinstance(x, list):
        for i, value in enumerate(x):
            find_adts(value, target, f"{path}[{i}]", hits)
    return hits

src207 = read(R207)
src210 = read(R210)
t207, t210 = decl_map(src207["type_decls"]), decl_map(src210["type_decls"])
f207, f210 = decl_map(src207["fun_decls"]), decl_map(src210["fun_decls"])
trt210 = decl_map(src210["trait_decls"])
impl210 = decl_map(src210["trait_impls"])
table = hashcons_table(src210)
table207 = hashcons_table(src207)

option_ids = []
option_summaries = []
for ident, decl in sorted(t210.items()):
    name = decl["item_meta"]["name"]
    if len(name) >= 4 and name[0] == {"Ident": ["core", 0]} and name[1] == {"Ident": ["option", 0]} and name[2] == {"Ident": ["Option", 0]}:
        option_ids.append(ident)
        type_arg_ref = name[3]["Instantiated"]["skip_binder"]["types"][0]
        option_summaries.append({
            "def_id": ident,
            "instantiated_type_argument_ref": type_arg_ref,
            "decoded_type_argument": expand(type_arg_ref, table),
            "generic_region_parameter_count": len(decl["generics"]["regions"]),
            "generic_type_parameter_count": len(decl["generics"]["types"]),
            "generic_const_parameter_count": len(decl["generics"]["const_generics"]),
            "generic_trait_clause_count": len(decl["generics"]["trait_clauses"]),
            "source": decl["item_meta"]["span"],
        })

target_type_ids = {48, 52, 53}
raw_declarations = {
    "types": {str(i): t210[i] for i in sorted(target_type_ids)},
    "function_78": f210[78],
    "trait_10": trt210[10],
    "trait_impl_40": impl210[40],
    "option_type_decls": {str(i): t210[i] for i in option_ids},
}
decoded = {
    "types": {str(i): expand(t210[i], table) for i in sorted(target_type_ids)},
    "function_78_signature": expand(f210[78]["signature"], table),
    "function_78_generics": f210[78]["generics"],
    "function_78_source": f210[78]["src"],
    "function_78_body_status": f210[78]["body"],
    "trait_10_name": trt210[10]["item_meta"]["name"],
    "trait_10_generics": trt210[10]["generics"],
    "trait_impl_40": expand(impl210[40], table),
    "option_instantiations": option_summaries,
    "direct_type_53_occurrences": {
        "type_decls": {str(i): hits for i, d in t210.items() if (hits := find_adts(d, 53))},
        "fun_decls": {str(i): hits for i, d in f210.items() if (hits := find_adts(d, 53))},
    },
}

assert 53 in option_ids and f210[78]["signature"]["output"]["HashConsedValue"][1]["Adt"]["id"] == {"Adt": 53}
assert t207[53] == t210[53], "R210 projection changed Option declaration 53"
assert expand(f207[78]["signature"], table207) == expand(f210[78]["signature"], table), "R210 projection changed decoded function 78 signature"
assert f210[78]["body"] == "Opaque"
assert all(d["generic_trait_clause_count"] == 0 for d in option_summaries)

report = {
    "input_files": {
        "r207": {"path": str(R207), "sha256": sha(R207)},
        "r210": {"path": str(R210), "sha256": sha(R210)},
    },
    "inventory_counts": {
        "R207_type_declarations": len(src207["type_decls"]),
        "R207_function_declaration_slots": len(src207["fun_decls"]),
        "R210_type_declarations": len(src210["type_decls"]),
        "R210_function_declaration_slots": len(src210["fun_decls"]),
        "R210_function_declarations_non_null": len(f210),
        "R210_option_concrete_type_declarations": len(option_ids),
    },
    "option_type_ids": option_ids,
    "option_instantiations": option_summaries,
    "selected_declarations": {
        "type_48": "AspisV8PerformanceHost::aspis_core::field::M31",
        "type_52": "core::slice::iter::IterMut instantiated with erased region and M31",
        "type_53": "core::option::Option instantiated with erased mutable reference to M31",
        "function_78": "core::slice::iter::IterMut::next",
        "trait_10": "core::iter::traits::iterator::Iterator",
        "trait_impl_40": "Iterator implementation for the IterMut instantiation",
    },
    "raw_relevant_declarations": raw_declarations,
    "decoded_relevant_declarations": decoded,
    "projection_comparison": {
        "type_53_identical_in_R207_and_R210": True,
        "function_78_decoded_signature_identical_in_R207_and_R210": True,
        "function_78_body_in_R210": f210[78]["body"],
        "preserved_body_ids": [9, 49, 50, 91, 92],
        "function_78_is_preserved_body": 78 in {9, 49, 50, 91, 92},
    },
    "interpretation_scope": "Mechanical declaration inventory only. It identifies serialized types and their references; it does not choose a preprocessing repair or assign source semantics.",
}
(ROOT / "option-type-inventory.json").write_text(json.dumps(report, indent=2) + "\n")
