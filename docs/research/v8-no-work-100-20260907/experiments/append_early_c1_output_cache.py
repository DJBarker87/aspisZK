#!/usr/bin/env python3
"""Copy-only retained V7 cache repair for one selected output endpoint.

No compiler, no existing artifact replacement. prepare emits a temporary upload
directory; apply checks the reserved state and preserves its before/after bytes.
"""
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

TASK = "/home/dombarker/project-offloads/aspis-higher-y.fMoMeX"
BORROWED = "26a9cd4718aae9f9de7ef1c3394fb74a229085d5"
BASE = "001f1020072a53448a455d85eeb1568a1c8cb09125bc025b5d4188d230882fec"
STATE = "3588abfb39c20c9b30364863cb9aee3c844e0047d8322b4e195695af8fa665a6"
RUN = "selected-early-c1-outputs-nuc-v1-manifest.json"
RUN_SHA = "6d52c1d98073ae4f264a983b01415c6b0926727d3522967bfd42ce71d74ffc3c"
NAMES = ["HashMerkleModel", "V5AcceptedSpendRelation", "V5SelectedGoodVerifierRelation",
         "V5SelectionHidingAbort", "SoundnessWorkNormalizedEndpoint",
         "V7PairForestGatedMerkle", "Pool/V7PairLeafOccupancy",
         "ArithmetizationCore", "ValueConservation"]
BOUNDARY = ["CoreHidingPMF", "CoreHiding", "SoundnessLedger", "CircleFibreRoots", "CircleGroupOrder"]


def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def exclusive(p, data):
    with Path(p).open("xb") as stream:
        stream.write(data)


def prepare():
    ex = Path(__file__).resolve().parent
    root = ex.parents[3]
    main = Path("/Users/dominic/ZK/AspisFormal")
    stage = Path(tempfile.mkdtemp(prefix="aspis-early-c1-output-cache."))
    forest = (ex / "selected-forest-cache-v2.log").read_text()
    occupancy = (ex / "selected-pair-cache-v1.log").read_text()
    assert "LEAN_EXIT=0" in forest and "LEAN_EXIT=0" in occupancy
    plan = {"source_parent": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=root, text=True).strip(),
            "borrowed": BORROWED, "base": BASE, "state": STATE, "run": RUN, "run_sha": RUN_SHA,
            "artifacts": [], "provenance": [], "boundary": []}
    for name in NAMES + BOUNDARY:
        rel = "AspisFormal/" + name
        source = root / "AspisFormal" / (rel + ".lean")
        output = main / ".lake/build/lib/lean" / (rel + ".olean")
        if name == "V7PairForestGatedMerkle":
            output = ex / ".selected-forest-cache" / (rel + ".olean")
        if name == "Pool/V7PairLeafOccupancy":
            output = ex / ".selected-pair-cache" / (rel + ".olean")
        pinned = subprocess.check_output(["git", "show", BORROWED + ":" + str(source.relative_to(root))], cwd=root)
        assert pinned == source.read_bytes(), name
        assert sha(source) in forest + occupancy and sha(output) in forest + occupancy, name
        header = output.open("rb").read(64)
        assert b"4.32.0" in header and b"8c9756b28d64dab099da31a4" in header
        pair = []
        for p, kind, suffix in [(source, "source", ".lean"), (output, "olean", ".olean")]:
            entry = {"module": rel.replace("/", "."), "category": "borrowed", "kind": kind,
                     "package": None, "local": str(p), "overlay": rel + suffix,
                     "remote_cache": None, "sha256": sha(p), "bytes": p.stat().st_size}
            pair.append(entry)
            if name in NAMES:
                target = stage / (rel + suffix)
                target.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(p, target)
                plan["artifacts"].append(entry)
        if name in BOUNDARY:
            plan["boundary"].extend(pair)
        trace = output.with_suffix(".trace")
        if name in NAMES and trace.exists():
            data = json.loads(trace.read_text())
            assert not any(row.get("level") == "error" for row in data["log"])
            dest = stage / (name.replace("/", "-") + ".trace")
            shutil.copyfile(trace, dest)
            plan["provenance"].append({"local": str(trace), "staged": dest.name, "sha256": sha(trace)})
    for name in ["selected-forest-cache-v2.log", "selected-pair-cache-v1.log"]:
        shutil.copyfile(ex / name, stage / name)
        plan["provenance"].append({"local": str(ex / name), "staged": name, "sha256": sha(ex / name)})
    exclusive(stage / "plan.json", (json.dumps(plan, indent=2) + "\n").encode())
    shutil.copyfile(__file__, stage / Path(__file__).name)
    print(stage)


def apply(stage):
    task = Path(TASK)
    assert stage.parent == task.parent and stage.name.startswith("aspis-early-c1-output-cache.")
    plan = json.loads((stage / "plan.json").read_text())
    assert (plan["base"], plan["state"], plan["run_sha"], plan["borrowed"]) == (BASE, STATE, RUN_SHA, BORROWED)
    manifest_path = task / "manifest.json"
    assert sha(manifest_path) == BASE and sha(task / "green-outputs.json") == STATE and sha(task / RUN) == RUN_SHA
    manifest = json.loads(manifest_path.read_text())
    run = json.loads((task / RUN).read_text())
    state = json.loads((task / "green-outputs.json").read_text())
    for entry in manifest["files"] + run["files"] + plan["boundary"]:
        assert sha(task / "overlay" / entry["overlay"]) == entry["sha256"], entry["overlay"]
    for name, entry in state.items():
        assert sha(task / "overlay" / (name + ".lean")) == entry["source"]
        for suffix, digest in entry["outputs"].items():
            assert sha(task / "overlay" / (name + suffix)) == digest
    for evidence in plan["provenance"]:
        assert sha(stage / evidence["staged"]) == evidence["sha256"]
    indexed = {e["overlay"]: e for e in manifest["files"]}
    additions, copies = [], []
    for entry in plan["artifacts"]:
        src, dest = stage / entry["overlay"], task / "overlay" / entry["overlay"]
        assert sha(src) == entry["sha256"]
        if dest.exists():
            assert sha(dest) == entry["sha256"], "Refuse existing variant replacement: " + str(dest)
        else:
            copies.append((src, dest))
        if entry["overlay"] in indexed:
            assert indexed[entry["overlay"]]["sha256"] == entry["sha256"]
        else:
            additions.append(entry)
    for name in ["manifest.json", "green-outputs.json", RUN]:
        exclusive(stage / ("before-" + name), (task / name).read_bytes())
    for src, dest in copies:
        dest.parent.mkdir(parents=True, exist_ok=True)
        exclusive(dest, src.read_bytes())
    manifest["files"].extend(additions)
    manifest["counts"] = {"pinned_source_blobs": sum(e["kind"] == "source" for e in manifest["files"]),
                          "compiled_artifacts": sum(e["kind"] == "olean" for e in manifest["files"])}
    after = (json.dumps(manifest, indent=2) + "\n").encode()
    exclusive(stage / "after-manifest.json", after)
    temporary = task / "early-c1-output-append-manifest.json"
    exclusive(temporary, after)
    assert sha(manifest_path) == BASE and sha(task / "green-outputs.json") == STATE
    temporary.replace(manifest_path)
    for entry in manifest["files"]:
        assert sha(task / "overlay" / entry["overlay"]) == entry["sha256"]
    assert sha(task / "green-outputs.json") == STATE and sha(task / RUN) == RUN_SHA
    receipt = {"status": "verified_copy_only_cache_append", "plan": plan, "task": TASK,
               "helper_sha256": sha(__file__), "base_before": BASE, "base_after": sha(manifest_path),
               "green_state_unchanged": STATE, "failed_run_unchanged": RUN_SHA,
               "copied": [str(dest.relative_to(task / "overlay")) for _, dest in copies],
               "registered": additions, "after_entries": len(manifest["files"]),
               "compiler_launched": False, "existing_artifact_replacements": 0,
               "boundary": "Retained local Lean 4.32 outputs; native package revision cache is not rebuilt. V5 soundness closure gives no new security credit."}
    exclusive(stage / "receipt.json", (json.dumps(receipt, indent=2) + "\n").encode())
    print(json.dumps({k: v for k, v in receipt.items() if k not in ["plan", "registered"]}, indent=2))


if __name__ == "__main__":
    if sys.argv[1:] == ["--prepare"]:
        prepare()
    elif len(sys.argv) == 3 and sys.argv[1] == "--apply-reserved":
        apply(Path(sys.argv[2]))
    else:
        raise SystemExit("Use --prepare locally or --apply-reserved STAGE under the parent reservation")
