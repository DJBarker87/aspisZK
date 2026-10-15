#!/usr/bin/env python3
"""Import the pinned leaf ULLBC graph, preserving every statement and both exits.

This is a source-pinned executable importer, NOT a proved Rust/Charon semantics
preservation theorem. Zero labels mean no dispatch at the one designated site;
they do not assert zero SHA effects. Unknown statement/edge forms fail closed.
"""
import argparse
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
EVIDENCE = ROOT / "evidence/j1e-private-leaf-extraction-20261015"
INPUT_SHA = "bf0964a73ae5ba10b4337d781050ac31a99b822153de3a2fa579690b952c1d5e"
SOURCE_SHA = "f0edc31d07d30f5b19fcaf872fba18678d13d1ba5fac1199f1f4d2be74c74f9b"
LEAN = ROOT / "lean/PrivateLeafDispatch.lean"


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":")).encode()


def singleton(value):
    require(isinstance(value, dict) and len(value) == 1, "expected singleton AST variant")
    return next(iter(value.items()))


def statement_tag(statement):
    require(set(statement) == {"span", "kind", "comments_before"}, "unknown statement fields")
    tag, value = singleton(statement["kind"])
    if tag in {"StorageLive", "StorageDead"}:
        require(type(value) is int and value >= 0, "bad storage local")
        return tag
    require(tag == "Assign", "unclassified statement: " + tag)
    require(isinstance(value, list) and len(value) == 2, "bad assignment")
    require(set(value[0]) == {"kind", "ty"}, "unknown destination fields")
    lhs, local = singleton(value[0]["kind"])
    require(lhs == "Local" and type(local) is int, "nonlocal assignment")
    rtag, rhs = singleton(value[1])
    require(rtag in {"Use", "Aggregate", "Ref", "UnaryOp"}, "unclassified rvalue: " + rtag)
    if rtag == "UnaryOp":
        require(isinstance(rhs, list) and len(rhs) == 2, "bad unary operation")
        outer, cast = singleton(rhs[0])
        inner, _ = singleton(cast)
        require(outer == "Cast" and inner == "Unsize", "unclassified unary effect")
    if rtag == "Aggregate":
        require(isinstance(rhs, list) and len(rhs) == 2 and set(rhs[0]) == {"Array"},
                "unclassified aggregate")
    return "Assign." + rtag


def import_graph(document, source):
    require(document.get("charon_version") == "0.1.223", "unexpected Charon schema")
    require(document.get("has_errors") is False, "extraction reported errors")
    crate = document["translated"]
    options = crate["options"]
    require(options["ullbc"] and options["precise_drops"] and options["mir"] == "Elaborated",
            "wrong extraction configuration")
    functions = crate["fun_decls"]
    require(len(functions) == 2 and not crate["type_decls"] and not crate["trait_decls"]
            and not crate["trait_impls"], "unexpected declaration cone")
    leaf = functions[0]
    names = [component["Ident"][0] for component in leaf["item_meta"]["name"]]
    require(names == ["r1_leaf_hash_extraction", "state_only_private_merkle", "private_leaf_hash"],
            "wrong target")
    require(leaf["def_id"] == 0 and set(leaf["body"]) == {"Unstructured"}, "wrong body")
    require(leaf["item_meta"]["source_text"] == "\n".join(source.splitlines()[27:35]),
            "source text differs from exact source snapshot")
    body = leaf["body"]["Unstructured"]
    require(body["locals"]["arg_count"] == 4, "argument layout changed")
    require(body["locals"]["locals"][1]["name"] == "hash", "callback argument changed")
    blocks = body["body"]
    require(len(blocks) == 3, "unexpected blocks")
    lengths = [len(block["statements"]) for block in blocks]
    require(lengths == [34, 4, 10], "statement positions changed")
    starts = []
    total = 0
    for length in lengths:
        starts.append(total)
        total += length + 1
    pending = total
    edges, trace = [], []
    for block_id, block in enumerate(blocks):
        require(set(block) == {"statements", "terminator"}, "unknown block fields")
        for offset, statement in enumerate(block["statements"]):
            tag = statement_tag(statement)
            src = starts[block_id] + offset
            edges.append([src, 0, src + 1])
            trace.append({"node": src, "pointer": f"/translated/fun_decls/0/body/Unstructured/body/{block_id}/statements/{offset}",
                          "tag": tag, "ast_sha256": sha(canonical(statement)), "outgoing": [[src, 0, src + 1]]})
        term = block["terminator"]
        require(set(term) == {"span", "kind", "comments_before"}, "unknown terminator fields")
        kind = term["kind"]
        node = starts[block_id] + lengths[block_id]
        outgoing = []
        if block_id == 0:
            require(isinstance(kind, dict) and set(kind) == {"Call"}, "designated call missing")
            callterm = kind["Call"]
            require(set(callterm) == {"call", "target", "on_unwind"}, "unknown call edge fields")
            require(callterm["target"] == 2 and callterm["on_unwind"] == 1, "callback exits changed")
            call = callterm["call"]
            require(set(call) == {"func", "args", "dest"}, "unknown call fields")
            operand = call["func"].get("Dynamic", {}).get("Move", {})
            require(operand.get("kind") == {"Local": 5}, "wrong dynamic callback")
            require(len(call["args"]) == 1 and call["dest"]["kind"] == {"Local": 0}, "call shape changed")
            first_assignment = blocks[0]["statements"][2]["kind"].get("Assign")
            require(first_assignment[0]["kind"] == {"Local": 5}
                    and first_assignment[1]["Use"][0]["Copy"]["kind"] == {"Local": 1},
                    "callback not copied from hash argument")
            for statement in blocks[0]["statements"][3:]:
                require(statement["kind"].get("Assign", [{"kind": None}])[0]["kind"] != {"Local": 5},
                        "callback local overwritten")
            outgoing = [[node, 1, pending]]
            tag = "Call.Dynamic.hash_argument"
        elif block_id == 1:
            require(kind == {"Abort": "UndefinedBehavior"}, "unclassified cleanup terminator")
            tag = "Abort.UndefinedBehavior"
        else:
            require(kind == "Return", "unclassified normal terminator")
            tag = "Return"
        edges.extend(outgoing)
        trace.append({"node": node, "pointer": f"/translated/fun_decls/0/body/Unstructured/body/{block_id}/terminator",
                      "tag": tag, "ast_sha256": sha(canonical(term)), "outgoing": outgoing})
    pending_edges = [[pending, 0, starts[2]], [pending, 0, starts[1]]]
    edges.extend(pending_edges)
    trace.append({"node": pending, "pointer": None, "tag": "Synthetic.callback_pending",
                  "purpose": "Count entry before callback completion; retain both original normal/unwind targets.",
                  "outgoing": pending_edges})
    # Constant initializer is retained separately and has no dynamic call AST.
    constant = functions[1]
    require(constant["is_global_initializer"] == 0 and constant["def_id"] == 1, "unknown global initializer")
    cblocks = constant["body"]["Unstructured"]["body"]
    require(len(cblocks) == 1 and cblocks[0]["terminator"]["kind"] == "Return", "initializer edges changed")
    for statement in cblocks[0]["statements"]:
        statement_tag(statement)
    potential = [1 if node < starts[1] else 0 for node in range(total + 1)]
    require(all(cost + potential[dst] <= potential[src] for src, cost, dst in edges),
            "potential certificate failed")
    return {"entry": 0, "pending_callback": pending, "abort": starts[1] + lengths[1],
            "return": starts[2] + lengths[2], "node_count": total + 1,
            "statement_counts": lengths, "edges": edges, "potential": potential,
            "import_trace": trace, "constant_initializer_ast_sha256": sha(canonical(constant)),
            "scope": "Count designated callback dispatches in this retained extracted CFG only.",
            "open": ["Rust/compiler/Charon trace preservation", "Importer semantic preservation",
                     "Actual callback binding and callback-internal SHA effects",
                     "All other statement/runtime SHA effects", "Full admitted verifier all-prefix count"]}


def emit_lean(graph):
    edges = ",\n  ".join(f"⟨{s}, {n}, {d}⟩" for s, n, d in graph["edges"])
    threshold = graph["statement_counts"][0] + 1
    return f'''import Std

/-! Generated by docs/research/100bit-spend-path-20261013/tools/j1e-private-leaf-cfg.py.
Retained ULLBC dispatch graph only.
Input SHA256: {INPUT_SHA}
All 48 statement positions, the cleanup abort and both callback continuations
are retained. The synthetic pending node permits stopping inside the callback.
Zero labels assert only absence of this ONE designated dispatch, not zero SHA.
Rust/Charon/importer preservation and callback/runtime effects remain OPEN.
No source-to-graph axiom or total SHA-count premise is declared here. -/
set_option autoImplicit false
namespace AspisR1.PrivateLeafDispatch

structure Edge where
  src : Nat
  cost : Nat
  dst : Nat
  deriving DecidableEq, Repr

def edges : List Edge := [
  {edges}]

def entry : Nat := {graph['entry']}
def pendingCallback : Nat := {graph['pending_callback']}
def abortNode : Nat := {graph['abort']}
def returnNode : Nat := {graph['return']}
def potential (node : Nat) : Nat := if node < {threshold} then 1 else 0

def Step (src cost dst : Nat) : Prop := ⟨src, cost, dst⟩ ∈ edges

private theorem edgePotential (edge : Edge) (h : edge ∈ edges) :
    edge.cost + potential edge.dst ≤ potential edge.src := by
  have checked : edges.all (fun e => decide
      (e.cost + potential e.dst ≤ potential e.src)) = true := by decide
  exact of_decide_eq_true ((List.all_eq_true.mp checked) edge h)

/-- Any finite prefix, with no requirement to reach a return or abort. -/
inductive FinitePrefix : Nat → Nat → Nat → Prop where
  | refl (node : Nat) : FinitePrefix node 0 node
  | snoc {{start mid finish count cost : Nat}} :
      FinitePrefix start count mid → Step mid cost finish →
      FinitePrefix start (count + cost) finish

theorem prefix_potential {{start count finish : Nat}}
    (h : FinitePrefix start count finish) :
    count + potential finish ≤ potential start := by
  induction h with
  | refl => simp
  | @snoc mid finish count cost _ step ih =>
      have localBound := edgePotential ⟨mid, cost, finish⟩ step
      calc
        (count + cost) + potential finish =
            count + (cost + potential finish) := Nat.add_assoc _ _ _
        _ ≤ count + potential mid := Nat.add_le_add_left localBound count
        _ ≤ potential start := ih

theorem finitePrefix_dispatch_le_one {{count finish : Nat}}
    (h : FinitePrefix entry count finish) : count ≤ 1 := by
  have bounded := prefix_potential h
  have initial : count + potential finish ≤ 1 := by
    simpa [entry, potential] using bounded
  exact Nat.le_trans (Nat.le_add_right count (potential finish)) initial

inductive Stop where
  | running | returned | aborted

def StopsAt (node : Nat) (stop : Stop) : Prop :=
  match stop with
  | .running => True
  | .returned => node = returnNode
  | .aborted => node = abortNode

theorem stoppedPrefix_dispatch_le_one {{count finish : Nat}} {{stop : Stop}}
    (h : FinitePrefix entry count finish) (_ : StopsAt finish stop) : count ≤ 1 :=
  finitePrefix_dispatch_le_one h

#print axioms prefix_potential
#print axioms finitePrefix_dispatch_le_one
#print axioms stoppedPrefix_dispatch_le_one
end AspisR1.PrivateLeafDispatch
'''


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    raw = (EVIDENCE / "PrivateLeaf.ullbc").read_bytes()
    require(sha(raw) == INPUT_SHA, "pinned ULLBC changed")
    source = (EVIDENCE / "source/state_only_private_merkle.rs").read_bytes()
    require(sha(source) == SOURCE_SHA, "pinned Rust source changed")
    graph = import_graph(json.loads(raw), source.decode())
    graph["ullbc_sha256"] = sha(raw)
    graph["source_sha256"] = sha(source)
    graph["generator_sha256"] = sha(Path(__file__).read_bytes())
    outputs = {EVIDENCE / "dispatch-graph.json": json.dumps(graph, indent=2, sort_keys=True) + "\n",
               LEAN: emit_lean(graph)}
    for path, text in outputs.items():
        if args.check:
            require(path.read_text() == text, "generated output differs: " + str(path))
        else:
            path.write_text(text)
    print(json.dumps({"status": "PASS", "nodes": graph["node_count"], "edges": len(graph["edges"]),
                      "designated_dispatch_sites": 1, "all_source_effects_closed": False,
                      "source_preservation": "OPEN", "lean_validation": "separate coordinator receipt"}))


if __name__ == "__main__":
    main()
