#!/usr/bin/env python3
"""Append exactly two verified local V7 cache pairs; never run a compiler."""
import hashlib
import json
import os
from pathlib import Path
import re
import sys

SOURCE_PARENT = "15700387af1d52af4b7ddff8de92541ec2891ff2"
BORROWED = "26a9cd4718aae9f9de7ef1c3394fb74a229085d5"
RUN_PARENT = "289d7356c78a4cd493fe61a54f9548f2a0c11298"
BASE_SHA = "46c0485b661719d093fa8392783e36f42f5f446fa95d54525f3e0438ff232ab1"
STATE_SHA = "979f1f2d26543b494a62876235b73ee44133da3354c631a88a9ea99feb6a9ecd"
RUN_NAME = "finite-option-mass-nuc-v1-manifest.json"
RUN_SHA = "d3a5a4d89c41f017deaee039f799d65dbff84e6d94b81e1dbe2803cb90d8f6e9"
PAIRS = (
    ("AspisFormal.V5ComponentCStoppingTimeSampler",
     "5ebfb82a9187f1f32ba9579677f47e553cc3040cd93d90f809c6472b6389b3fb",
     "e0185f92a37fac9d175144fced2e629298b0bf95bd3b01c85e5f4177025a08ae",
     "f4021d4c0bae77f7c8daa86fb1bab840d724415e09a531651488c13818c620e9", 10),
    ("AspisFormal.K1.V7Tag73EightRetrySamplerLaw",
     "dfb490b1bfbce4abe894e1809ec8d933acb55dbc5f6e5eb1de5b6942e5b5941e",
     "6a662071ccbf95c37771fc4d49c512ecc29b8335e52112fd164fc5de63ec053f",
     "e98c7636fce12560a948e076b946b2e724a82ce18c0be0c9267935e2be96bf41", 4),
)
BOUNDARY = (
    ("AspisFormal.V5ComponentCRejectionSampler",
     "3605064a7da5267b2b1ba347f84663f57136adf07a4f8e1a3bacfe46ca72901e",
     "9956a145ac168248f7407c279de45bfd6a4b0512b970c5dd9b67b224c5ed8d11"),
    ("AspisFormal.V5ComponentCQM31TowerExact",
     "75404d16b5a71f67146b91ca35739b111f81bb730beb77432267f2b5385cebe5",
     "5d0e1ba16ff7cc29fca900249aa75b0011402cd4b84b8766aaf8346d854d04e9"),
    ("AspisFormal.K1.V7Tag73DeployedDecoderFiberCap",
     "c6ccdaf7284edccbac0cce77088f547f33bc7568a2ddea8bd00041e315468c53",
     "cdada5008486bf4d58ef1f4ca777dd8de99513d5fccb455606dc95c994bc275a"),
    ("AspisFormal.K1.V7Tag73SamplerDecoderExact",
     "b4bfdf70bf94fec863454edf05e0d31342c0a83db2a123f9ecd5aaa961ee1db8",
     "1134465da320635cb21479c3e0dd3daae7cff534b8b143bcd03daba06eeed41c"),
)


def require(ok, message):
    if not ok:
        raise ValueError(message)


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def sha(path):
    return digest(path.read_bytes())


def exclusive(path, raw):
    with path.open("xb") as output:
        output.write(raw)


def verify_entries(task, entries):
    for entry in entries:
        rel = Path(entry["overlay"])
        require(not rel.is_absolute() and ".." not in rel.parts, "unsafe overlay path")
        require(sha(task / "overlay" / rel) == entry["sha256"],
                "existing import bytes changed: " + str(rel))


def main():
    require(len(sys.argv) == 3, "expected TASK STAGING")
    task, stage = map(Path, sys.argv[1:])
    require(str(task) == "/home/dombarker/project-offloads/aspis-higher-y.fMoMeX", "wrong task")
    require(stage.parent == Path("/home/dombarker/project-offloads") and
            stage.name.startswith("aspis-ordinary-raw-cache."), "wrong fresh staging scope")
    manifest_path, state_path = task / "manifest.json", task / "green-outputs.json"
    raw, state_raw, run_raw = manifest_path.read_bytes(), state_path.read_bytes(), (task / RUN_NAME).read_bytes()
    require(digest(raw) == BASE_SHA and digest(state_raw) == STATE_SHA and digest(run_raw) == RUN_SHA,
            "manifest or green state advanced; obtain a new reservation")
    manifest, state, run = json.loads(raw), json.loads(state_raw), json.loads(run_raw)
    require(len(manifest["files"]) == 794 and len(run["files"]) == 859 and len(state) == 33,
            "pre-append census changed")
    require(manifest["research"] == RUN_PARENT and manifest["borrowed"] == BORROWED,
            "inherited pins changed")
    verify_entries(task, run["files"])
    for module, value in state.items():
        require(sha(task / "overlay" / (module + ".lean")) == value["source"], "green source changed")
        for suffix, expected in value["outputs"].items():
            require(sha(task / "overlay" / (module + suffix)) == expected, "green output changed")
    indexed = {(e["module"], e["kind"]): e for e in run["files"]}
    for module, source, output in BOUNDARY:
        require(indexed[(module, "source")]["sha256"] == source and
                indexed[(module, "olean")]["sha256"] == output, "boundary manifest changed")
    additions, traces, copies = [], [], []
    known = {e["module"] for e in manifest["files"]} | set(state)
    for module, source, output, trace_sha, audits in PAIRS:
        require(module not in known, "module already registered")
        stem, rel = module.split(".")[-1], module.replace(".", "/")
        trace_file = stage / (stem + ".trace")
        require(sha(trace_file) == trace_sha, "retained local trace mismatch")
        trace = json.loads(trace_file.read_text())
        messages = "\n".join(row["message"] for row in trace["log"])
        found = re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", messages, re.S)
        require(len(found) == audits and all(set(a.strip() for a in used.split(",") if a.strip()) <=
                {"propext", "Classical.choice", "Quot.sound"} for _, used in found), "trace axiom mismatch")
        require(not any(row["level"] == "error" for row in trace["log"]), "retained trace has errors")
        require("/Users/dominic/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean " in messages,
                "expected local cache build origin absent")
        traces.append({"module": module, "path": str(trace_file), "sha256": trace_sha,
                       "recorded_standard_axiom_audits": audits, "new_axiom_credit": 0})
        for suffix, expected, kind in ((".lean", source, "source"), (".olean", output, "olean")):
            src, dest = stage / (stem + suffix), task / "overlay" / (rel + suffix)
            require(sha(src) == expected and not dest.exists(), "new import mismatch or destination exists")
            if suffix == ".olean":
                header = src.open("rb").read(64)
                require(b"4.32.0" in header and b"8c9756b28d64dab099da31a4" in header, "compiler header mismatch")
            local = "/Users/dominic/ZK/AspisFormal/" + (
                "" if kind == "source" else ".lake/build/lib/lean/") + rel + suffix
            additions.append({"module": module, "category": "borrowed", "kind": kind,
                              "package": None, "local": local, "overlay": rel + suffix,
                              "remote_cache": None, "sha256": expected, "bytes": src.stat().st_size})
            copies.append((src, dest))
    # All guards precede mutations. Old attempt manifests and green state are never written.
    exclusive(stage / "before-manifest.json", raw)
    exclusive(stage / "before-green-outputs.json", state_raw)
    exclusive(stage / "before-run-manifest.json", run_raw)
    for src, dest in copies:
        require(dest.parent.is_dir(), "existing module directory absent")
        exclusive(dest, src.read_bytes())
    updated = dict(manifest)
    updated["files"] = manifest["files"] + additions
    updated["counts"] = {"pinned_source_blobs": 399, "compiled_artifacts": 399}
    after = (json.dumps(updated, indent=2) + "\n").encode()
    exclusive(stage / "after-manifest.json", after)
    temporary = task / "ordinary-raw-append-manifest.json"
    exclusive(temporary, after)
    require(sha(manifest_path) == BASE_SHA and sha(state_path) == STATE_SHA and
            sha(task / RUN_NAME) == RUN_SHA, "state advanced before atomic publish")
    os.replace(temporary, manifest_path)
    require(updated["files"][:794] == manifest["files"] and len(updated["files"]) == 798,
            "old base entries changed")
    verify_entries(task, updated["files"])
    verify_entries(task, run["files"])
    require(sha(state_path) == STATE_SHA and sha(task / RUN_NAME) == RUN_SHA,
            "old state or attempt manifest changed")
    receipt = {"schema": "aspis-ordinary-raw-cache-append-v1", "status": "metadata_append_verified",
               "source_parent": SOURCE_PARENT, "borrowed": BORROWED, "overlay_parent": RUN_PARENT,
               "task": str(task), "staging": str(stage), "helper_sha256": sha(Path(__file__)),
               "network": {"endpoint": "dombarker@100.108.41.90", "transport": "Tailscale",
                           "host_key_alias": "nuc.local", "alias_is_network_endpoint": False},
               "before_manifest_sha256": BASE_SHA, "after_manifest_sha256": sha(manifest_path),
               "unchanged_green_state_sha256": STATE_SHA, "unchanged_run_manifest_sha256": RUN_SHA,
               "before_base_entries": 794, "after_base_entries": 798,
               "unchanged_run_entries_verified": 859, "unchanged_green_targets_verified": 33,
               "added": additions, "retained_local_traces": traces,
               "boundary": [{"module": m, "source_sha256": s, "olean_sha256": o} for m, s, o in BOUNDARY],
               "compiler_launched": False, "native_variant_replacements": 0,
               "scope": "Two missing local cached V7 pairs only; first changed-leaf NUC import remains the environment-compatibility check. No package or unchanged theorem-suite replay."}
    exclusive(stage / "receipt.json", (json.dumps(receipt, indent=2) + "\n").encode())
    print(json.dumps(receipt, indent=2))
    print("ORDINARY_RAW_CACHE_APPEND_PASS=4")


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, KeyError, AssertionError) as error:
        print("ORDINARY_RAW_CACHE_APPEND_REJECTED: " + str(error), file=sys.stderr)
        sys.exit(1)
