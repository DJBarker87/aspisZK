#!/usr/bin/env python3
"""Audit final focused leaves, their exact source bytes, axioms and resources."""
import hashlib
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
EX = ROOT / "experiments"
BASE = "f021007879dcd9e2bca795b4758e187fa1c3b302"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
LEAVES = [
    ("CommonFibreGaoRecovery", "common-fibre-gao-v*.log"),
    ("SelectedPaymentRecovery", "selected-payment-lean-v*.log"),
    ("OptimizedRelationRefinement", "optimized-relation-lean-v*.log"),
    ("EarlyC1Support", "early-c1-generic-v*.log"),
    ("EarlyC1Arithmetic", "early-c1-arithmetic-v*.log"),
    ("EarlyC1Projection", "early-c1-leaf-final*.log"),
]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def final_leaf(name, pattern):
    source = EX / (name + ".lean")
    source_hash = sha(source)
    found = []
    for path in EX.glob(pattern):
        log = path.read_text()
        if f"{source_hash}  {source}" not in log:
            continue
        if re.search(r"sorryAx|: error:|^error:|memory_exception|AGGREGATE_RSS_STOP", log, re.M):
            continue
        if "LEAN_EXIT=" in log and "LEAN_EXIT=0" not in log:
            continue
        olean = re.findall(r"^([a-f0-9]{64})  .*?/" + re.escape(name) + r"\.olean$", log, re.M)
        axioms = re.findall(r"'([^']+)' depends on axioms: \[(.*?)\]", log, re.S)
        if not olean or not axioms:
            continue
        audits = []
        for decl, raw in axioms:
            used = {x.strip() for x in raw.split(",") if x.strip()}
            assert used <= ALLOWED, (path, decl, used)
            audits.append({"declaration": decl, "axioms": sorted(used)})
        times = re.findall(r"^\s*([0-9.]+) real", log, re.M)
        rss = re.findall(r"^\s*(\d+)\s+maximum resident set size", log, re.M)
        swaps = re.findall(r"^\s*(\d+)\s+swaps$", log, re.M)
        assert len(times) == len(rss) == len(swaps) == 1, path
        assert BASE in log and int(swaps[0]) == 0
        # A cached local output, when present, must match the executed log.
        cache = EX / (name + ".olean")
        if cache.exists():
            assert sha(cache) == olean[-1]
        found.append({"target": source.name, "source_sha256": source_hash,
                      "olean_sha256": olean[-1], "log": str(path.relative_to(ROOT)),
                      "log_sha256": sha(path), "exit": 0,
                      "wall_seconds": float(times[0]), "peak_rss_bytes": int(rss[0]),
                      "swaps": int(swaps[0]), "axiom_audits": audits})
    assert found, f"No successful current-source evidence for {name}"
    assert len(found) == 1, (name, "ambiguous final evidence")
    return found[0]


def result():
    return {"base_revision": BASE,
            "environment": "Lean4.32.0; Mathlib81a5d257c8e410db227a6665ed08f64fea08e997; focused serialized cached leaves",
            "scope": "kernel-checked source-shaped mathematics, not Rust-to-SBF refinement or global security",
            "leaves": [final_leaf(name, pattern) for name, pattern in LEAVES],
            "production_or_verifier_changes": False,
            "global_accepted_extraction_bound": None}


if __name__ == "__main__":
    out = result()
    if sys.argv[1:] == ["--check-recorded"]:
        assert json.loads((ROOT / "soundness-resume-evidence.json").read_text()) == out
        print("Focused current-source proof evidence and standard-axiom audits match.")
    else:
        assert not sys.argv[1:]
        print(json.dumps(out, indent=2))
