#!/usr/bin/env python3
"""Fail-closed extraction of the two selected Aspis V8 shared-read AST nodes."""
from __future__ import annotations
import hashlib
import json
import re
from pathlib import Path

ROOT = next(p for p in Path(__file__).resolve().parents if (p / ".git").exists())
SOURCE = ROOT / "docs/research/v8-full-view-zk-20260912/evidence/r440-current-monomorphic-callback-binding/actual-source-preflight/aeneas-plan/fun29/R440GammaExecutionSelection.llbc"
OUT = Path(__file__).resolve().parent
LEAN_SOURCE = ROOT / "docs/research/v8-full-view-zk-20260912/lean/AspisV8R19/R485SelectedSharedRead.lean"
EXPECTED_SOURCE_SHA256 = "96135e91c71f93dcd3aeec7b693eb737e7cf05027456ca973242cf2586088c48"


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit("FAIL CLOSED: " + message)


def walk(o):
    if isinstance(o, dict):
        yield o
        for v in o.values():
            yield from walk(v)
    elif isinstance(o, list):
        for v in o:
            yield from walk(v)


def expected_assign(dst: int, dst_ty: int, rhs: dict) -> dict:
    return {"Assign": [
        {"kind": {"Local": dst}, "ty": {"Deduplicated": dst_ty}},
        rhs,
    ]}

# Full operand trees pin every nested place/type/ref-kind/metadata/copy field.
CREATE_RHS = {"Ref": {
    "place": {
        "kind": {"Projection": [
            {"kind": {"Local": 21}, "ty": {"Deduplicated": 4603}},
            "Deref",
        ]},
        "ty": {"Deduplicated": 544},
    },
    "kind": "Shared",
    "ptr_metadata": {"Const": {
        "kind": {"Adt": [None, []]},
        "ty": {"Deduplicated": 891},
    }},
}}
COPY_RHS = {"Use": [
    {"Copy": {
        "kind": {"Projection": [
            {"kind": {"Local": 4}, "ty": {"Deduplicated": 5448}},
            "Deref",
        ]},
        "ty": {"Deduplicated": 544},
    }},
    "Yes",
]}
EXPECTED_KINDS = {
    (70, 10438): expected_assign(20, 4329, CREATE_RHS),
    (112, 11909): expected_assign(9, 544, COPY_RHS),
}

raw = SOURCE.read_bytes()
source_sha = sha256(raw)
require(source_sha == EXPECTED_SOURCE_SHA256,
        f"pinned source SHA changed: expected {EXPECTED_SOURCE_SHA256}, got {source_sha}")
doc = json.loads(raw)
require(set(doc) == {"charon_version", "translated", "has_errors"},
        "top-level source fields changed")
require(isinstance(doc["translated"], dict), "translated is not an object")
functions = doc["translated"].get("fun_decls")
require(isinstance(functions, list), "translated.fun_decls is not a list")

extracted = []
for fid, sid in EXPECTED_KINDS:
    fs = [f for f in functions if isinstance(f, dict) and f.get("def_id") == fid]
    require(len(fs) == 1, f"expected exactly one function def_id={fid}, found {len(fs)}")
    f = fs[0]
    require(isinstance(f.get("body"), dict) and "Structured" in f["body"],
            f"function {fid} no longer has Structured body")
    matches = [n for n in walk(f["body"]) if n.get("id") == sid]
    require(len(matches) == 1,
            f"expected exactly one statement id={sid} in function {fid}, found {len(matches)}")
    node = matches[0]
    require(set(node) == {"span", "id", "kind", "comments_before"},
            f"statement {sid} fields changed; refusing partial selection")
    require(node["id"] == sid and node["kind"] == EXPECTED_KINDS[(fid, sid)],
            f"function {fid} statement {sid} assignment/operand/type structure changed")
    # The selection record names the enclosing function while retaining the entire raw node.
    extracted.append({"function_def_id": fid, "statement_id": sid, "node": node})

# Bind the Lean literals to this exact checked syntax projection. This remains
# an external reproducible association, not a kernel proof of JSON decoding.
def lean_place(place):
    kind, ty = place["kind"], place["ty"]["Deduplicated"]
    if "Local" in kind:
        return f".local {kind['Local']} {ty}"
    base, projection = kind["Projection"]
    require(projection == "Deref", "unsupported place projection")
    return f".deref ({lean_place(base)}) {ty}"

lean = LEAN_SOURCE.read_text()
for selected, name in zip(extracted, ("selectedAcquire", "selectedCopy")):
    dst, rhs = selected["node"]["kind"]["Assign"]
    if "Ref" in rhs:
        ref = rhs["Ref"]
        metadata_ty = ref["ptr_metadata"]["Const"]["ty"]["Deduplicated"]
        value = f".sharedRef ({lean_place(ref['place'])}) (.unitAdt {metadata_ty})"
    else:
        operand, flag = rhs["Use"]
        require(flag == "Yes", "unsupported copy flag")
        value = f".useCopy ({lean_place(operand['Copy'])}) true"
    expected = f"⟨{lean_place(dst)}, {value}⟩"
    match = re.search(rf"def {name} : Assignment :=\s*(.+)", lean)
    require(match is not None and match.group(1) == expected,
            f"Lean {name} literal differs from exact checked source projection")

payload = {
    "source": str(SOURCE.relative_to(ROOT)),
    "source_sha256": source_sha,
    "charon_version": doc["charon_version"],
    "selected_nodes": extracted,
}
node_bytes = (json.dumps(payload, indent=2, sort_keys=True) + "\n").encode()
(OUT / "selected-nodes.json").write_bytes(node_bytes)
manifest = {
    "checker": str(Path(__file__).resolve().relative_to(ROOT)),
    "checker_sha256": sha256(Path(__file__).read_bytes()),
    "source": payload["source"],
    "source_sha256": source_sha,
    "selected_nodes": [
        {"function_def_id": x["function_def_id"], "statement_id": x["statement_id"],
         "node_sha256": sha256((json.dumps(x["node"], sort_keys=True, separators=(",", ":"))).encode())}
        for x in extracted
    ],
    "selected_nodes_file": "selected-nodes.json",
    "selected_nodes_file_sha256": sha256(node_bytes),
    "selection": "exact function and statement IDs, exact Assign/RHS trees, all nested local/type/ref-kind/metadata/copy fields, full raw node retained",
    "lean_source": str(LEAN_SOURCE.relative_to(ROOT)),
    "lean_source_sha256": sha256(LEAN_SOURCE.read_bytes()),
    "lean_binding_boundary": "external exact typed-literal association; not a kernel JSON interpretation or native semantic adequacy proof",
}
(OUT / "manifest.json").write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
print(json.dumps(manifest, indent=2, sort_keys=True))
