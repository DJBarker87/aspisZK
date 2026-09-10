#!/usr/bin/env python3
"""Register an existing prior-green pair; never compile, copy or replace it.

The only mutation is the authorized mechanical JSON manifest append and its
exclusive before/after receipt files. Run remotely only under the parent slot.
"""
import hashlib
import json
from pathlib import Path
import subprocess
import sys

TASK = Path("/home/dombarker/project-offloads/aspis-higher-y.fMoMeX")
CACHE = Path("/home/dombarker/project-offloads/ZK-v7-clean-k16-20260831/AspisFormal")
MODULE = "SelectedPairDecoder"
SOURCE = "3f670127e035a4ea7f532decb2127386975d2a39e188761dcc9c3eaad55c249e"
OLEAN = "abb67f4a8ec702e4a605a7048081122e5c9ad4462a7449063761ab6aa715c6f8"
LOG = "60da5a18ae5d01e608c70c82011ce9177d388e3dceb3a2e7ef32860a77111fd6"
PREFIX = "early-c1-input-pair-cache"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def exclusive(path, data):
    with path.open("xb") as stream:
        stream.write(data)


def verify_pair(folder, log):
    assert sha(log) == LOG
    text = log.read_text()
    assert "LEAN_EXIT=0" in text and "sorryAx" not in text
    assert text.count("depends on axioms:") == 10
    for suffix, digest in [(".lean", SOURCE), (".olean", OLEAN)]:
        path = folder / (MODULE + suffix)
        assert sha(path) == digest and digest in text
    source = (folder / (MODULE + ".lean")).read_text()
    assert [line for line in source.splitlines() if line.startswith("import ")] == [
        "import AspisFormal.Pool.V7PairLeafOccupancy"]
    with (folder / (MODULE + ".olean")).open("rb") as stream:
        header = stream.read(64)
    assert b"4.32.0" in header and b"8c9756b28d64dab099da31a4" in header


def append_reserved():
    processes = subprocess.check_output(["ps", "-eo", "pid=,stat=,comm=,args="], text=True).splitlines()
    live = [line for line in processes if len(line.split()) >= 3
            and line.split()[2] in {"lean", "lake"} and not line.split()[1].startswith("Z")]
    assert not live, "Compiler live: " + repr(live)
    log = TASK / (PREFIX + "-prior.log")
    verify_pair(TASK / "overlay", log)
    path = TASK / "manifest.json"
    state_path = TASK / "green-outputs.json"
    before = path.read_bytes()
    state_bytes = state_path.read_bytes()
    manifest = json.loads(before)
    state = json.loads(state_bytes)
    assert MODULE not in state
    assert MODULE not in {entry["module"] for entry in manifest["files"]}
    for module, entry in state.items():
        assert sha(TASK / "overlay" / (module + ".lean")) == entry["source"]
        for suffix, digest in entry["outputs"].items():
            assert sha(TASK / "overlay" / (module + suffix)) == digest
    subprocess.run([sys.executable, str(TASK / "verify_masked_nuc.py"), str(TASK), str(CACHE)], check=True)
    boundary = [entry for entry in manifest["files"]
                if entry["module"] == "AspisFormal.Pool.V7PairLeafOccupancy"]
    assert {entry["kind"] for entry in boundary} == {"source", "olean"}
    assert next(entry["sha256"] for entry in boundary if entry["kind"] == "source") == \
        "eaf609988c11ce5feceac03a7771a143eaccbad8f1025cee0cf0be89c3b350c1"
    assert next(entry["sha256"] for entry in boundary if entry["kind"] == "olean") == \
        "a483f5baa7101d3c3a3ca6ceb86b7f40993f3fa4f68bfb20d372c05aa5437e6a"
    additions = []
    for suffix, kind, digest in [(".lean", "source", SOURCE), (".olean", "olean", OLEAN)]:
        artifact = TASK / "overlay" / (MODULE + suffix)
        additions.append({"module": MODULE, "category": "research_retained",
                          "kind": kind, "package": None, "local": None,
                          "overlay": artifact.name, "remote_cache": None,
                          "sha256": digest, "bytes": artifact.stat().st_size})
    manifest["files"].extend(additions)
    manifest["counts"] = {
        "pinned_source_blobs": sum(entry["kind"] == "source" for entry in manifest["files"]),
        "compiled_artifacts": sum(entry["kind"] == "olean" for entry in manifest["files"])}
    after = (json.dumps(manifest, indent=2) + "\n").encode()
    exclusive(TASK / (PREFIX + "-before.json"), before)
    exclusive(TASK / (PREFIX + "-after.json"), after)
    temporary = TASK / (PREFIX + "-append.json")
    exclusive(temporary, after)
    assert path.read_bytes() == before and state_path.read_bytes() == state_bytes
    temporary.replace(path)
    subprocess.run([sys.executable, str(TASK / "verify_masked_nuc.py"), str(TASK), str(CACHE)], check=True)
    verify_pair(TASK / "overlay", log)
    assert state_path.read_bytes() == state_bytes
    receipt = {"status": "verified_existing_pair_manifest_append", "module": MODULE,
               "task": str(TASK), "source_parent": "b2557a4b77212c77e44d29eea1b94e820bf939f8",
               "helper_sha256": sha(Path(__file__)), "prior_log_sha256": LOG,
               "base_before": hashlib.sha256(before).hexdigest(), "base_after": sha(path),
               "green_state_unchanged": hashlib.sha256(state_bytes).hexdigest(),
               "registered": additions, "direct_import_boundary": boundary,
               "after_entries": len(manifest["files"]), "compiler_launched": False,
               "copied_artifacts": 0, "existing_artifact_replacements": 0,
               "boundary": "Exact retained Lean 4.32 source/output/log; native packages revision-pinned, not replayed."}
    exclusive(TASK / (PREFIX + "-receipt.json"), (json.dumps(receipt, indent=2) + "\n").encode())
    print(json.dumps(receipt, indent=2))


if __name__ == "__main__":
    if sys.argv[1:] == ["--verify-local"]:
        folder = Path(__file__).resolve().parent
        verify_pair(folder, folder / "selected-pair-leaf-v4.log")
        print("LOCAL_EXISTING_PAIR_PASS=true")
    elif sys.argv[1:] == ["--append-reserved"]:
        append_reserved()
    else:
        raise SystemExit("Use --verify-local or --append-reserved")
