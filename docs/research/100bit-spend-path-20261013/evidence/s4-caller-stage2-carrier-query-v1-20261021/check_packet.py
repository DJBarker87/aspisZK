#!/usr/bin/env python3
"""Verify source-only S4 carrier/query/start-zero packet pins."""
import hashlib, json, pathlib, sys
root = pathlib.Path(__file__).resolve().parent

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def require(ok, msg):
    if not ok:
        raise SystemExit(f"FAIL: {msg}")

m = json.loads((root / "manifest.json").read_text())
require(m["schema"] == "aspis-s4-caller-stage2-carrier-query-v1", "manifest schema")
for item in m["claims"]:
    src = root / item["source"]
    require(src.is_file(), f"missing source {src}")
    require(sha(src) == item["source_sha256"], f"source hash {src}")
    ev = root / item["run"]
    receipt = json.loads((ev / "receipt.json").read_text())
    require(receipt["exit_code"] == 0, f"nonzero accepted run {item['name']}")
    require(receipt["source_sha256"] == item["source_sha256"], f"receipt source hash {item['name']}")
    require(receipt["object_sha256"] == item["object_sha256"], f"receipt object hash {item['name']}")
    require(item["axioms"] == ["propext", "Classical.choice", "Quot.sound"], f"unexpected axiom list {item['name']}")
    log = (ev / "lean.log").read_text()
    require(item["name"] in log, f"missing theorem axiom audit {item['name']}")
    require("sorryAx" not in log and "core.fmt.Formatter" not in log, f"rejected axiom in {item['name']}")
    tlog = (ev / "time.log").read_text()
    require("swaps" in tlog and "maximum resident set size" in tlog, f"missing resource fields {item['name']}")
    require(any(line.strip().endswith("swaps") and line.strip().split()[0] == "0" for line in tlog.splitlines()), f"nonzero compiler swap {item['name']}")
# Verify the copied direct adapter and source provenance records.
adapter = root / "sources/Stage2ContinuationTypes.lean"
require(sha(adapter) == m["direct_owner_pins"]["stage2_types_adapter_source_sha256"], "Stage2 adapter source pin")
for rel, expected in [("provenance/formatter-repair-manifest.json", ""), ("provenance/tx1-parent-owner-manifest.json", "")]:
    require((root / rel).is_file(), f"missing provenance {rel}")
fmt = json.loads((root / "provenance/formatter-repair-manifest.json").read_text())
found = any(x.get("module") == "Aeneas" and x.get("object_sha256") == "d3bfce818c2409992274bc1852aa00280cb7a8139465ef0bab674498e4cdc69d" for x in fmt.get("modules", []))
require(found, "accepted repaired Aeneas/Fmt owner pin")
parent = json.loads((root / "provenance/tx1-parent-owner-manifest.json").read_text())
require(parent["generated_caller"]["funs_source_sha256"] == "a0e806d4f28840dffde1fd436b208e2fbf717157b74432bcc5c4721445f50a25", "caller Funs source provenance")
require(sha(root / "provenance/current-caller/Funs.lean") == m["direct_owner_pins"]["current_caller_funs_snapshot_sha256"], "caller Funs snapshot pin")
require(sha(root / "provenance/current-caller/Tx1OpsCut.lean") == m["direct_owner_pins"]["current_tx1_ops_cut_snapshot_sha256"], "caller Ops cut snapshot pin")
trans = json.loads((root / "provenance/current-caller/translation.json").read_text())
def walk(x):
    if isinstance(x, dict):
        yield x
        for v in x.values(): yield from walk(v)
    elif isinstance(x, list):
        for v in x: yield from walk(v)
entries = list(walk(trans))
opaque_acc = [x for x in entries if x.get("lean_name") == "AspisR1CurrentCaller.verifier.Accumulator.new"]
require(len(opaque_acc) == 1 and opaque_acc[0].get("is_opaque") is True, "Accumulator.new opaque translation metadata")
repo = root.parents[4]
rust = repo / "crates/aspis-r1-cost-probe/src/verifier.rs"
require(rust.is_file() and sha(rust) == m["direct_owner_pins"]["current_frozen_verifier_source_sha256"], "current frozen Rust source pin")
tracked_adapter = repo / m["direct_owner_pins"]["tracked_source"]
require(tracked_adapter.is_file() and sha(tracked_adapter) == m["direct_owner_pins"]["stage2_types_adapter_source_sha256"], "tracked Stage2 adapter source pin")
require("Ops.accumulatorNew slot" in " ".join(m["open_boundaries"]), "constructor slot boundary disclosed")
# Check the source excerpt came from the exact frozen file hash and includes literal next=0.
ex = (root / "provenance/accumulator-new-current-rust-excerpt.txt").read_text()
require("next:0" in ex.replace(" ", ""), "literal next=0 source excerpt")
# Check inventory list; SHA256SUMS deliberately excludes itself.
for line in (root / "SHA256SUMS").read_text().splitlines():
    expected, rel = line.split("  ", 1)
    f = root / rel
    require(f.is_file() and sha(f) == expected, f"SHA256SUMS mismatch {rel}")
print("PASS s4 caller/Stage2 carrier and constructor source-cut packet")
