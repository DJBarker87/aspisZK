"""Metadata-only root-Fun0 ordering generator following pinned Charon DepsForItem.

It preserves the complete R283 LLBC declaration rows and changes only
translated.ordered_decls. It is not a translator or a source-semantics proof.
"""
import copy, hashlib, json, pathlib

ROOT = pathlib.Path(__file__).resolve().parent
SRC = ROOT / "R283PrivateNormBatch.input.llbc"
EXPECTED = "999fdb4f5a034faf9d4aa11c7a44851b9c79f471d76ae6afb3b92aed0767c8d5"
PINNED = ROOT / "pinned-reorder_decls.rs"
PINNED_SHA = "8a1176e29a51a83c82ff5a7df2aa11021e3e0c254e9fd6c656c0a92314ba2632"
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(SRC) == EXPECTED
assert sha(PINNED) == PINNED_SHA, (sha(PINNED), PINNED_SHA)
raw = json.loads(SRC.read_text())
d = raw["translated"]
assert raw["has_errors"] is False and isinstance(d.get("ordered_decls"), list)

GROUPS = {"Type": "type_decls", "Fun": "fun_decls", "Global": "global_decls",
          "TraitDecl": "trait_decls", "TraitImpl": "trait_impls"}
rows = {(kind, row["def_id"]): row for kind, key in GROUPS.items()
        for row in d[key] if isinstance(row, dict)}
ROOTS = [("Fun", 0)]
item_labels = {}
for entry in d.get("item_names", []):
    key = entry.get("key", {})
    if len(key) == 1:
        kind, ident = next(iter(key.items()))
        name = "::".join(part.get("Ident", ["?"])[0] if "Ident" in part else str(part) for part in entry.get("value", []))
        item_labels[(kind, ident)] = name

for root in ROOTS:
    assert root in rows and rows[root].get("body") not in (None, "Opaque")
    assert rows[root]["item_meta"]["is_local"]

# Expand Charon's hash-consed wrappers without changing input/output values.
hashcons = {}
def collect(x):
    if isinstance(x, dict):
        if "HashConsedValue" in x:
            i, value = x["HashConsedValue"]
            assert i not in hashcons or hashcons[i] == value
            hashcons[i] = value
        for value in x.values(): collect(value)
    elif isinstance(x, list):
        for value in x: collect(value)
collect(raw)
def decode(x, seen=()):
    if isinstance(x, dict):
        if "HashConsedValue" in x:
            i, value = x["HashConsedValue"]
            assert i not in seen
            return decode(value, seen + (i,))
        if "Deduplicated" in x:
            i = x["Deduplicated"]
            assert i in hashcons and i not in seen
            return decode(hashcons[i], seen + (i,))
        return {k: decode(v, seen) for k, v in x.items()}
    if isinstance(x, list): return [decode(v, seen) for v in x]
    return x

def src_parent(row):
    """Return parent suppression identity from ItemSource, if applicable."""
    src = decode(row.get("src"))
    if not isinstance(src, dict): return None
    if "TraitImpl" in src:
        impl = src["TraitImpl"].get("impl_ref", {}).get("id")
        return ("TraitImpl", impl) if isinstance(impl, int) else None
    if "TraitDecl" in src:
        trait = src["TraitDecl"].get("trait_ref", {}).get("id")
        return ("TraitDecl", trait) if isinstance(trait, int) else None
    return None

edges = set()
typed_ref_census = []
reachable_defaults = []
reachability_only_children = {}
unknown_shapes = []
skipped_absent_vtable_refs = []
non_declaration_index_census = []

def edge(src, target, path):
    if target not in rows:
        # Pinned Charon insert_edge uses get_item and does not enqueue absent items.
        # The lead has authorized this behavior only for absent references found in
        # TraitDecl/TraitImpl vtable metadata. Do not apply it to executable/signature refs.
        item_label = item_labels.get(("Type", target[1])) if target[0] == "Type" else None
        if (src[0] in ("TraitDecl", "TraitImpl") and target[0] == "Type"
                and ".vtable.id" in path
                and path.startswith(f"{src[0]}[{src[1]}].vtable.")
                and isinstance(item_label, str) and item_label.endswith("::{vtable}")):
            skipped_absent_vtable_refs.append({
                "source": list(src), "path": path, "target": list(target),
                "item_names_label": item_label,
                "absent_row_status": "no translated declaration row in R283",
                "rule": "lead-authorized mirror of pinned get_item filtering for vtable metadata only"
            })
            return
        raise ValueError(("missing declaration reference", src, target, path))
    edges.add((src, target))

def walk(x, src, path, suppressed):
    """Walk AST fields; recognize typed references by their serialized constructors."""
    if isinstance(x, list):
        for i, value in enumerate(x): walk(value, src, f"{path}[{i}]", suppressed)
        return
    if not isinstance(x, dict): return

    # LLBC AdtId (including the nested {"id":{"Adt": n}} spelling).
    if set(x) == {"Adt"}:
        if isinstance(x["Adt"], dict) and set(x["Adt"]) == {"id", "generics"}:
            walk(x["Adt"]["id"], src, path+".Adt.id", suppressed)
            walk(x["Adt"]["generics"], src, path+".Adt.generics", suppressed)
        elif isinstance(x["Adt"], int):
            target = ("Type", x["Adt"]); typed_ref_census.append([path, *target]); edge(src, target, path)
        elif isinstance(x["Adt"], list):
            value = x["Adt"]
            if path.endswith(".Aggregate[0]") and len(value) == 3:
                # AggregateKind::Adt payload begins with its AdtId; remaining values
                # are variant/field metadata, not declaration references.
                walk(value[0], src, path+".Adt[0]", suppressed)
                non_declaration_index_census.append({"path":path,"shape":"AggregateKind::Adt payload","non_reference_tail":value[1:]})
            elif ".Projection[" in path and ".Field[0]" in path and len(value) == 2 and isinstance(value[0], int):
                non_declaration_index_census.append({"path":path,"shape":"field projection index plus optional variant","values":value})
            elif ".ptr_metadata." in path and value == [None, []]:
                non_declaration_index_census.append({"path":path,"shape":"constant pointer metadata tag with no declaration ID","values":value})
            else:
                unknown_shapes.append([path, "Adt-payload-list", value])
        elif x["Adt"] != "Builtin":
            unknown_shapes.append([path, "Adt", x["Adt"]])
        return

    # FunId: regular declarations are graph dependencies; compiler builtins are not.
    if "Fun" in x:
        f = x["Fun"]
        if isinstance(f, dict) and set(f) == {"Regular"} and isinstance(f["Regular"], int):
            target = ("Fun", f["Regular"]); typed_ref_census.append([path+".Fun.Regular", *target]); edge(src, target, path)
        elif isinstance(f, dict) and set(f) == {"Builtin"}:
            pass
        else:
            unknown_shapes.append([path, "Fun", f])

    # GlobalDeclRef and direct GlobalDeclId references.
    if "Global" in x:
        g = x["Global"]
        if isinstance(g, int):
            target = ("Global", g); typed_ref_census.append([path+".Global", *target]); edge(src, target, path)
        elif isinstance(g, dict) and isinstance(g.get("id"), int) and "generics" in g:
            target = ("Global", g["id"]); typed_ref_census.append([path+".Global.id", *target]); edge(src, target, path)
            walk(g["generics"], src, path+".Global.generics", suppressed)
        else: unknown_shapes.append([path, "Global", g])

    # TraitDeclRef and TraitImplRef have distinct syntactic forms in LLBC.
    if "trait_decl_ref" in x:
        tr = x["trait_decl_ref"]
        try: i = tr["skip_binder"]["id"]
        except (KeyError, TypeError): i = None
        if isinstance(i, int):
            target = ("TraitDecl", i)
            typed_ref_census.append([path+".trait_decl_ref", *target])
            if target != suppressed: edge(src, target, path)
            walk(tr.get("regions", []), src, path+".trait_decl_ref.regions", suppressed)
            walk(tr["skip_binder"].get("generics", {}), src, path+".trait_decl_ref.generics", suppressed)
        else: unknown_shapes.append([path, "trait_decl_ref", tr])
    if "impl_ref" in x:
        ir = x["impl_ref"]
        if isinstance(ir, dict) and isinstance(ir.get("id"), int):
            target = ("TraitImpl", ir["id"]); typed_ref_census.append([path+".impl_ref", *target])
            if target != suppressed: edge(src, target, path)
            walk(ir.get("generics", {}), src, path+".impl_ref.generics", suppressed)
        else: unknown_shapes.append([path, "impl_ref", ir])
    # TraitImplId appears as a tagged kind or as an impl_trait id (TraitDeclId).
    if "TraitImpl" in x:
        tr = x["TraitImpl"]
        if isinstance(tr, dict) and isinstance(tr.get("id"), int):
            target = ("TraitImpl", tr["id"]); typed_ref_census.append([path+".TraitImpl", *target])
            if target != suppressed: edge(src, target, path)
            walk(tr.get("generics", {}), src, path+".TraitImpl.generics", suppressed)
        else: unknown_shapes.append([path, "TraitImpl", tr])
    if "impl_trait" in x:
        it = x["impl_trait"]
        if isinstance(it, dict) and isinstance(it.get("id"), int):
            target = ("TraitDecl", it["id"]); typed_ref_census.append([path+".impl_trait", *target])
            if target != suppressed: edge(src, target, path)
            walk(it.get("generics", {}), src, path+".impl_trait.generics", suppressed)
        else: unknown_shapes.append([path, "impl_trait", it])

    # Trait method IDs encode the trait owner, while its index is not a declaration ID.
    if "TraitMethod" in x:
        tm = x["TraitMethod"]
        if isinstance(tm, list) and len(tm) == 2 and all(isinstance(v, int) for v in tm):
            target = ("TraitDecl", tm[0]); typed_ref_census.append([path+".TraitMethod", *target])
            if target != suppressed: edge(src, target, path)
        else: unknown_shapes.append([path, "TraitMethod", tm])

    # Do not infer dependencies from arbitrary integer-valued `id` fields. Recurse into
    # non-reference fields, but avoid processing the same typed-reference payload twice.
    for k, v in x.items():
        if k in ("Adt", "Fun", "Global", "trait_decl_ref", "impl_ref", "TraitImpl", "impl_trait", "TraitMethod"):
            continue
        if k == "id" and isinstance(v, int):
            continue
        walk(v, src, path+"."+k, suppressed)

def row_payload(kind, row):
    value = decode(row)
    if kind == "Fun":
        # Charon visits def_id (only to suppress self-edge), generics, signature, body;
        # it skips item_meta, src, and is_global_initializer. TraitDecl source is the
        # one explicit source edge in compute_declarations_graph.
        fields = {k: value[k] for k in ("generics", "signature", "body")}
        srcv = value.get("src")
        if isinstance(srcv, dict) and "TraitDecl" in srcv:
            tr = srcv["TraitDecl"].get("trait_ref", {}).get("id")
            if isinstance(tr, int):
                target = ("TraitDecl", tr); typed_ref_census.append([f"Fun[{row['def_id']}].src.TraitDecl.trait_ref", *target]); edge((kind,row["def_id"]), target, "Fun TraitDecl source edge")
        return fields
    if kind == "TraitDecl":
        # Match pinned explicit visitor: generics, implied clauses, types, vtable,
        # const type/default generics, and method params/signatures/default generics.
        out = {k: value[k] for k in ("generics", "implied_clauses", "types", "vtable")}
        for i, c in enumerate(value["consts"]):
            out[f"const[{i}].ty"] = c["ty"]
            if c.get("default") is not None:
                g = c["default"]
                target = ("Global", g["id"])
                reachable_defaults.append({"source":[kind,row["def_id"]],"kind":"const","index":i,"target":list(target),"dependency_edge":False})
                typed_ref_census.append([f"TraitDecl[{row['def_id']}].const[{i}].default",*target])
                if target not in rows: raise ValueError(("missing default const declaration",(kind,row["def_id"]),target))
                reachability_only_children.setdefault((kind,row["def_id"]),[]).append(target)
                out[f"const[{i}].default.generics"] = g.get("generics",{})
        for i, m in enumerate(value["methods"]):
            if m is None: continue
            out[f"method[{i}].params"] = m["params"]
            out[f"method[{i}].signature"] = m["skip_binder"]["signature"]
            if m["skip_binder"].get("default") is not None:
                f = m["skip_binder"]["default"]
                target = ("Fun", f["id"])
                reachable_defaults.append({"source":[kind,row["def_id"]],"kind":"method","index":i,"target":list(target),"dependency_edge":False})
                typed_ref_census.append([f"TraitDecl[{row['def_id']}].method[{i}].default",*target])
                if target not in rows: raise ValueError(("missing default method declaration",(kind,row["def_id"]),target))
                reachability_only_children.setdefault((kind,row["def_id"]),[]).append(target)
                out[f"method[{i}].default.generics"] = f.get("generics",{})
        return out
    return {k:v for k,v in value.items() if k not in ("def_id", "item_meta", "src", "is_global_initializer")}

graph = {}; visited = set(); active = []
def visit(node):
    if node not in rows: raise ValueError(("missing declaration", node))
    if node in active:
        cycle = active[active.index(node):] + [node]
        raise ValueError(("cycle; SCC ordering intentionally unsupported", cycle))
    if node in visited: return
    active.append(node)
    refs_before = set(edges)
    walk(row_payload(node[0], rows[node]), node, f"{node[0]}[{node[1]}]", src_parent(rows[node]))
    deps = {b for a,b in edges if a == node}
    graph[node] = deps
    for dep in sorted(deps): visit(dep)
    # Pinned Charon uses insert_node for defaults: keep them reachable, but do not
    # add a dependency edge from the trait declaration to the default item.
    for child in reachability_only_children.get(node, []): visit(child)
    active.pop(); visited.add(node)

try:
    for root in ROOTS: visit(root)
except ValueError as exc:
    diag = {"input_sha256": EXPECTED, "pinned_reorder_sha256": sha(PINNED), "roots": [list(x) for x in ROOTS],
            "status": "failed_closed", "diagnostic": repr(exc), "reachable_before_failure": [list(x) for x in visited],
            "edge_count_before_failure": len(edges), "skipped_absent_vtable_refs": skipped_absent_vtable_refs,
            "scope": "No output LLBC written; cycle or unclassified/missing reference requires lead review."}
    (ROOT/"failure-diagnostic.json").write_text(json.dumps(diag,indent=2)+"\n")
    raise
if unknown_shapes:
    raise ValueError(("unclassified typed-reference shapes", unknown_shapes[:20]))

ordered = []
def postorder(node):
    if node in ordered: return
    for dep in sorted(graph[node]): postorder(dep)
    ordered.append(node)
for root in ROOTS: postorder(root)
position = {node:i for i,node in enumerate(ordered)}
assert all(position[dep] < position[src] for src,deps in graph.items() for dep in deps)

out = copy.deepcopy(raw)
out["translated"]["ordered_decls"] = [{kind:{"NonRec":i}} for kind,i in ordered]
before = copy.deepcopy(raw); after = copy.deepcopy(out)
before["translated"].pop("ordered_decls"); after["translated"].pop("ordered_decls")
assert before == after
dest = ROOT / "R288PrivateNormBatchOrdered.llbc"
dest.write_text(json.dumps(out,indent=2)+"\n")
for key in GROUPS.values(): assert raw["translated"][key] == out["translated"][key]
report = {
    "input_sha256": EXPECTED, "output_sha256": sha(dest), "pinned_reorder_sha256": sha(PINNED),
    "root_ids": [list(x) for x in ROOTS], "ordered_ids": [list(x) for x in ordered],
    "counts": {kind:sum(n[0]==kind for n in ordered) for kind in GROUPS},
    "all_declaration_tables_identical": True, "only_changed_path": "translated.ordered_decls",
    "input_ordered_decls_count": len(raw["translated"].get("ordered_decls", [])),
    "dependency_edges": [{"from":list(a),"to":list(b)} for a,b in sorted(edges)],
    "typed_reference_census": typed_ref_census, "reachable_trait_defaults": reachable_defaults,
    "skipped_absent_vtable_refs": skipped_absent_vtable_refs,
    "non_declaration_index_census": non_declaration_index_census,
    "cycles": [], "unknown_reference_shapes": unknown_shapes, "all_refs_present": True,
    "scope": "Metadata-only graph/order inventory following pinned Charon rules; no source execution or semantic theorem is established."
}
(ROOT/"audit.json").write_text(json.dumps(report,indent=2)+"\n")
print(json.dumps({"counts":report["counts"],"output_sha256":report["output_sha256"]},indent=2))
