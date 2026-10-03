#!/usr/bin/env python3
"""Read-only strict structural audit of saved R440 baseline/candidate LLBC."""
import copy, hashlib, json
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
BASE = ROOT / "baseline-saved"
CAND = ROOT / "candidate-saved"
OUT = Path(__file__).resolve().parent

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def load(p):
    return json.loads(p.read_text())

def digest(obj):
    return hashlib.sha256(json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode()).hexdigest()

def canonical_short_names(xs):
    rows = [(json.dumps(x["key"], sort_keys=True, separators=(",", ":")), x["value"]) for x in xs]
    assert len({k for k, _ in rows}) == len(rows), "duplicate short-name key"
    return sorted(rows, key=lambda x: x[0])

def flatten_groups(groups):
    flat = []
    group_rows = []
    for g in groups:
        assert isinstance(g, dict) and len(g) == 1
        kind, group = next(iter(g.items()))
        assert isinstance(group, dict) and len(group) == 1
        group_kind, members = next(iter(group.items()))
        if group_kind == "NonRec": members = [members]
        else:
            assert group_kind == "Rec" and isinstance(members, list)
        group_rows.append((kind, group_kind, tuple(members)))
        flat.extend((kind, member) for member in members)
    return group_rows, Counter(flat)

def call_at(crate, fun_id, stmt_index):
    fun = next(x for x in crate["fun_decls"] if x["def_id"] == fun_id)
    stmt = fun["body"]["Structured"]["body"]["statements"][stmt_index]
    assert "Call" in stmt["kind"], (fun_id, stmt_index, stmt["kind"])
    return fun, stmt, stmt["kind"]["Call"]["call"]

baseline_path = BASE / "baseline.llbc"
candidate_path = CAND / "baseline.llbc"
bh, ch = sha(baseline_path), sha(candidate_path)
assert bh == "331b2a1fdcbb21279a4e3f92d995bac93ffa05c78d847a3576a2f6e912e93445"
assert ch == "6bb4254faef4498b51ebe7d97213a457da740391799562302501e9a701240eb7"
b, c = load(baseline_path), load(candidate_path)
assert b["charon_version"] == c["charon_version"]
assert b["has_errors"] is False and c["has_errors"] is False
bt, ct = b["translated"], c["translated"]

# The source/declaration tables that should be unchanged are compared directly, preserving
# every serialized body, binder, method map, destructor, and callback row.
unchanged_tables = {}
for key in ("type_decls", "global_decls", "trait_decls", "trait_impls"):
    assert bt[key] == ct[key], f"changed declaration table: {key}"
    unchanged_tables[key] = {"count": len(bt[key]), "sha256": digest(bt[key])}
assert len(bt["fun_decls"]) == len(ct["fun_decls"])
fun_ids = [f["def_id"] for f in bt["fun_decls"]]
assert fun_ids == [f["def_id"] for f in ct["fun_decls"]]

# The sole executable AST differences permitted by this audit are the two call.func nodes.
expected_sites = {1: 9, 2: 3}
site_report = {}
for fid, stmt_i in expected_sites.items():
    bf, bs, bcall = call_at(bt, fid, stmt_i)
    cf, cs, ccall = call_at(ct, fid, stmt_i)
    assert bf["def_id"] == cf["def_id"] == fid
    assert bs["id"] == cs["id"] and bs["span"] == cs["span"]
    assert {k: v for k, v in bcall.items() if k != "func"} == {k: v for k, v in ccall.items() if k != "func"}, f"non-func call fields changed at Fun{fid} stmt{stmt_i}"
    old = bcall["func"]["Regular"]
    new = ccall["func"]["Regular"]
    assert "Trait" in old["kind"]
    tref, method_id = old["kind"]["Trait"]
    assert method_id == 0
    impl_ref = tref["kind"]["TraitImpl"]
    assert impl_ref["id"] == 1
    assert new["kind"] == {"Fun": {"Regular": 3}}
    # Preserve and check each generic namespace exactly: impl args followed by the original
    # direct-call method args, as represented in the saved source call.
    arg_fields = ("regions", "types", "const_generics", "trait_refs")
    for field in arg_fields:
        expected = impl_ref["generics"][field] + old["generics"][field]
        assert new["generics"][field] == expected, f"unexpected {field} transport at Fun{fid}"
    target = next(x for x in ct["fun_decls"] if x["def_id"] == 3)
    target_params = target["generics"]
    assert len(new["generics"]["regions"]) == len(target_params["regions"])
    assert len(new["generics"]["types"]) == len(target_params["types"])
    assert len(new["generics"]["const_generics"]) == len(target_params["const_generics"])
    assert len(new["generics"]["trait_refs"]) == len(target_params["trait_clauses"])
    # Fun3 itself, including its source, signature, body, and callback operations, is unchanged.
    assert next(x for x in bt["fun_decls"] if x["def_id"] == 3) == target
    site_report[str(fid)] = {
        "statement_index": stmt_i,
        "statement_id": bs["id"],
        "old_impl_id": impl_ref["id"],
        "old_method_id": method_id,
        "new_fun_id": 3,
        "old_impl_region_args": impl_ref["generics"]["regions"],
        "old_method_region_args": old["generics"]["regions"],
        "new_region_args": new["generics"]["regions"],
        "other_generic_namespaces_exact_concat": True,
        "args_destination_target_unwind_exact": True,
    }

# Whole-input strict comparison after excising exactly those two function-pointer subtrees,
# with no other body/signature/type normalization.
b2, c2 = copy.deepcopy(b), copy.deepcopy(c)
for fld in ("type_decls", "global_decls", "trait_decls", "trait_impls"):
    pass
for fid, stmt_i in expected_sites.items():
    _, _, call_b = call_at(b2["translated"], fid, stmt_i)
    _, _, call_c = call_at(c2["translated"], fid, stmt_i)
    del call_b["func"]
    del call_c["func"]
# The destination differs only because runs wrote into different fresh roots.
dest_b = b2["translated"]["options"].pop("dest_file")
dest_c = c2["translated"]["options"].pop("dest_file")
# Names are an indexed map; compare contents keyed by the exact serialized ItemId, not vector order.
b2["translated"]["short_names"] = canonical_short_names(b2["translated"]["short_names"])
c2["translated"]["short_names"] = canonical_short_names(c2["translated"]["short_names"])
short_names_same = b2["translated"]["short_names"] == c2["translated"]["short_names"]
assert short_names_same
bgroups, bflat = flatten_groups(b2["translated"]["ordered_decls"])
cgroups, cflat = flatten_groups(c2["translated"]["ordered_decls"])
assert bflat == cflat, "ordered_decls membership changed"
assert all(group_kind == "NonRec" for _, group_kind, _ in bgroups + cgroups)
# Keep order itself; prove the new direct target precedes each function caller.
cgroup_pos = {row[2][0]: i for i, row in enumerate(cgroups) if row[1] == "NonRec" and row[0] == "Fun"}
for caller in (1, 2):
    assert cgroup_pos[3] < cgroup_pos[caller], f"Fun3 not before new caller Fun{caller}"
assert b2["translated"]["ordered_decls"] != c2["translated"]["ordered_decls"], "expected reorder did not occur"
# No other serialized LLBC field may differ.
assert b2 == c2, "unexpected differences remain after only the two call.func nodes, output path, map ordering, and ordered-decl ordering are accounted for"

# Verify fixture/run custody from saved receipts (no process is rerun).
br, cr = load(BASE / "result.json"), load(CAND / "result.json")
bcmd, ccmd = load(BASE / "command.json"), load(CAND / "command.json")
assert br["exit_status"] == 0 and cr["exit_status"] == 0
assert bcmd["fixture_sha256"] == ccmd["fixture_sha256"] == "86f696b86419a99bc2a9da74fb99b47694bca8d66f67c7bf6b6bf2d263075554"
assert bcmd["pinned_tool_revision"] == ccmd["pinned_tool_revision"] == "cb50ff16b9f1066b8a97dc06da704de2da2fa41c"
assert bcmd["wrapper_sha256"] == ccmd["wrapper_sha256"] == "b2b0961a3c55aca64752b2fa4a4701ba0c06b860236979e5727c07de8ac2310c"
assert bcmd["driver_sha256"] == "4cb603ad51132f298a63a9c2a8cc8c629c73edeff22516fbf56ba5decee70938"
assert ccmd["original_driver_sha256"] == bcmd["driver_sha256"]
assert ccmd["driver_sha256"] != bcmd["driver_sha256"]

report = {
    "classification": "independent saved-artifact structural audit only; no semantic/correctness/security decision",
    "pass": True,
    "raw_llbc": {"baseline_sha256": bh, "candidate_sha256": ch, "baseline_has_errors": b["has_errors"], "candidate_has_errors": c["has_errors"]},
    "unchanged_declaration_tables": unchanged_tables,
    "fun_decl_count": len(fun_ids),
    "fun_ids_except_two_call_func_sites_exact": True,
    "only_call_func_sites": site_report,
    "ordered_decls": {
        "baseline_group_count": len(bgroups), "candidate_group_count": len(cgroups),
        "all_groups_nonrecursive": True,
        "item_membership_multiset_same": True,
        "baseline_fun_order": [m[0] for m in bgroups if m[0] == "Fun" for _ in [0]],
        "candidate_fun_order": [m[2][0] for m in cgroups if m[0] == "Fun"],
        "candidate_fun3_precedes_callers_1_2": True,
        "ordered_sequences_changed": True,
    },
    "short_names": {"same_key_value_contents": True, "vector_order_ignored": True},
    "output_path_allowance": {"baseline": dest_b, "candidate": dest_c, "only_translated_option_difference": "dest_file"},
    "run_receipts": {
        "baseline_exit_status": br["exit_status"], "candidate_exit_status": cr["exit_status"],
        "fixture_sha256_same": True, "pinned_charon_revision_same": True,
        "wrapper_sha256_same": True, "driver_changed_to_candidate": True,
    },
    "whole_tree_equality_after_exact_exclusions": True,
}
(OUT / "audit.json").write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
print(json.dumps(report, indent=2, sort_keys=True))
