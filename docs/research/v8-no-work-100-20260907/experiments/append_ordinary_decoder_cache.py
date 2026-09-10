#!/usr/bin/env python3
"""Reserved-state append of one verified local decoder bridge; no compiler."""
import json
import os
from pathlib import Path
import re
import sys
import append_ordinary_raw_cache as base

BASE_SHA = "7881b518c94f594a25674ad83e74b22298bcf547567df53b21b6efc5802144cc"
MODULE = "AspisFormal.K1.V7Tag73EightRetryDecoderBridge"
SOURCE = "027dc6b1a91fe9b21bdd7db6929fb70da4aa204745e8cc39bbc4cd5fb48673e4"
OUTPUT = "1039d5af8c2991fd6d16c3d5fa7a86d8804c29abfaa79c9084300a867c47c94d"
TRACE = "9d7760d12b7eec78692f7e120e3bff0d4be26bad814d8869712a0408301ca1d4"
BOUNDARY = (
    ("AspisFormal.K1.V7Tag73EightRetrySamplerLaw", base.PAIRS[1][1], base.PAIRS[1][2]),
    base.BOUNDARY[3],
    ("AspisFormal.K1.V7Tag73SamplerExactValue",
     "06e04a340d5efe599dfca7f9cb4292b1f00df71ac07ce9cf8f6d22c46326f5e9",
     "f3ac7cec9316f83d6ed441a247b826c347efe451adc0900253adae981df349af"),
)


def main():
    base.require(len(sys.argv) == 4 and sys.argv[1] == "--apply-reserved", "explicit reserved apply required")
    task, stage = Path(sys.argv[2]), Path(sys.argv[3])
    base.require(str(task) == "/home/dombarker/project-offloads/aspis-higher-y.fMoMeX", "wrong task")
    base.require(stage.parent == Path("/home/dombarker/project-offloads") and
                 stage.name.startswith("aspis-ordinary-decoder-cache."), "wrong fresh staging scope")
    plan = json.loads((stage / "plan.json").read_text())
    base.require(plan["source_parent"] == base.SOURCE_PARENT and
                 plan["base_manifest_sha256"] == BASE_SHA, "plan pins changed")
    run_name = plan["run_manifest_name"]
    base.require(re.fullmatch(r"[a-z0-9-]+-manifest.json", run_name), "unsafe run manifest")
    manifest_path, state_path = task / "manifest.json", task / "green-outputs.json"
    raw, state_raw, run_raw = manifest_path.read_bytes(), state_path.read_bytes(), (task / run_name).read_bytes()
    base.require(base.digest(raw) == BASE_SHA and base.digest(state_raw) == plan["green_state_sha256"] and
                 base.digest(run_raw) == plan["run_manifest_sha256"], "reserved manifest/state advanced")
    manifest, state, run = json.loads(raw), json.loads(state_raw), json.loads(run_raw)
    base.require(len(manifest["files"]) == 798 and len(state) == plan["green_targets"] and
                 len(run["files"]) == plan["run_entries"] and "OrdinaryRawMass" in state,
                 "raw mass not green or reservation census changed")
    base.require(manifest["research"] == base.RUN_PARENT and manifest["borrowed"] == base.BORROWED,
                 "inherited pins changed")
    base.verify_entries(task, run["files"])
    for module, value in state.items():
        base.require(base.sha(task / "overlay" / (module + ".lean")) == value["source"], "green source changed")
        for suffix, expected in value["outputs"].items():
            base.require(base.sha(task / "overlay" / (module + suffix)) == expected, "green output changed")
    indexed = {(e["module"], e["kind"]): e for e in run["files"]}
    for module, source, output in BOUNDARY:
        base.require(indexed[(module, "source")]["sha256"] == source and
                     indexed[(module, "olean")]["sha256"] == output, "boundary changed")
    base.require(MODULE not in {e["module"] for e in manifest["files"]} | set(state), "module already registered")
    stem, rel = MODULE.split(".")[-1], MODULE.replace(".", "/")
    trace_path = stage / (stem + ".trace")
    base.require(base.sha(trace_path) == TRACE, "retained local trace mismatch")
    trace = json.loads(trace_path.read_text())
    messages = "\n".join(row["message"] for row in trace["log"])
    audits = re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", messages, re.S)
    base.require(len(audits) == 2 and all(set(a.strip() for a in used.split(",") if a.strip()) <=
                 {"propext", "Classical.choice", "Quot.sound"} for _, used in audits), "trace axioms changed")
    base.require(not any(row["level"] == "error" for row in trace["log"]) and
                 "/Users/dominic/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean " in messages,
                 "local compile origin missing or trace has errors")
    additions, copies = [], []
    for suffix, expected, kind in ((".lean", SOURCE, "source"), (".olean", OUTPUT, "olean")):
        src, dest = stage / (stem + suffix), task / "overlay" / (rel + suffix)
        base.require(base.sha(src) == expected and not dest.exists(), "new artifact differs or target exists")
        if suffix == ".olean":
            header = src.open("rb").read(64)
            base.require(b"4.32.0" in header and b"8c9756b28d64dab099da31a4" in header, "compiler header mismatch")
        local = "/Users/dominic/ZK/AspisFormal/" + (
            "" if kind == "source" else ".lake/build/lib/lean/") + rel + suffix
        additions.append({"module": MODULE, "category": "borrowed", "kind": kind, "package": None,
                          "local": local, "overlay": rel + suffix, "remote_cache": None,
                          "sha256": expected, "bytes": src.stat().st_size})
        copies.append((src, dest))
    base.exclusive(stage / "before-manifest.json", raw)
    base.exclusive(stage / "before-green-outputs.json", state_raw)
    base.exclusive(stage / "before-run-manifest.json", run_raw)
    for src, dest in copies:
        base.require(dest.parent.is_dir(), "module directory missing")
        base.exclusive(dest, src.read_bytes())
    updated = dict(manifest)
    updated["files"] = manifest["files"] + additions
    updated["counts"] = {"pinned_source_blobs": 400, "compiled_artifacts": 400}
    after = (json.dumps(updated, indent=2) + "\n").encode()
    base.exclusive(stage / "after-manifest.json", after)
    temporary = task / "ordinary-decoder-append-manifest.json"
    base.exclusive(temporary, after)
    base.require(base.sha(manifest_path) == BASE_SHA and base.sha(state_path) == plan["green_state_sha256"] and
                 base.sha(task / run_name) == plan["run_manifest_sha256"], "state advanced before publication")
    os.replace(temporary, manifest_path)
    base.require(updated["files"][:798] == manifest["files"] and len(updated["files"]) == 800,
                 "old base entries changed")
    base.verify_entries(task, updated["files"])
    base.verify_entries(task, run["files"])
    base.require(base.sha(state_path) == plan["green_state_sha256"] and
                 base.sha(task / run_name) == plan["run_manifest_sha256"], "old state/run changed")
    receipt = {"schema": "aspis-ordinary-decoder-cache-append-v1", "status": "metadata_append_verified",
               "source_parent": base.SOURCE_PARENT, "borrowed": base.BORROWED, "overlay_parent": base.RUN_PARENT,
               "task": str(task), "staging": str(stage), "plan": plan,
               "helper_sha256": base.sha(Path(__file__)),
               "shared_helper_sha256": base.sha(Path(base.__file__)),
               "before_manifest_sha256": BASE_SHA, "after_manifest_sha256": base.sha(manifest_path),
               "unchanged_green_state_sha256": plan["green_state_sha256"],
               "unchanged_run_manifest_sha256": plan["run_manifest_sha256"],
               "before_base_entries": 798, "after_base_entries": 800,
               "unchanged_run_entries_verified": plan["run_entries"],
               "unchanged_green_targets_verified": plan["green_targets"], "added": additions,
               "retained_trace": {"path": str(trace_path), "sha256": TRACE,
                                  "recorded_standard_axiom_audits": 2, "new_axiom_credit": 0},
               "boundary": [{"module": m, "source_sha256": s, "olean_sha256": o} for m, s, o in BOUNDARY],
               "network": {"endpoint": "dombarker@100.108.41.90", "transport": "Tailscale",
                           "host_key_alias": "nuc.local", "alias_is_network_endpoint": False},
               "compiler_launched": False, "native_variant_replacements": 0,
               "scope": "One missing local DecoderBridge pair; SamplerExactValue was already pinned. First changed-prefix leaf checks NUC import compatibility. No large gamma/semantic closure or old-suite replay."}
    base.exclusive(stage / "receipt.json", (json.dumps(receipt, indent=2) + "\n").encode())
    print(json.dumps(receipt, indent=2))
    print("ORDINARY_DECODER_CACHE_APPEND_PASS=2")


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, KeyError, AssertionError) as error:
        print("ORDINARY_DECODER_CACHE_APPEND_REJECTED: " + str(error), file=sys.stderr)
        sys.exit(1)
