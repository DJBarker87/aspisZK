#!/usr/bin/env python3
"""Verify retained candidate evidence only; no extraction, compilation or replay."""
from pathlib import Path
import hashlib
import io
import json
import re
import subprocess
import tarfile

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[4]
sha = lambda b: hashlib.sha256(b).hexdigest()
summary = json.loads((HERE / "SUMMARY.json").read_text())
members = json.loads((HERE / "archive-members.json").read_text())
assert sha((HERE / "archive-members.json").read_bytes()) == summary["member_manifest_sha256"]
assert sha((HERE / "evidence.tar.gz").read_bytes()) == summary["archive_sha256"]
with tarfile.open(HERE / "evidence.tar.gz") as t:
    entries = t.getmembers()
    assert len(entries) == len({x.name for x in entries}) == summary["archive_member_count"]
    assert all(x.isfile() and not x.name.startswith("/") and ".." not in Path(x.name).parts for x in entries)
    data = {x.name: t.extractfile(x).read() for x in entries}
assert set(data) == set(members)
for name, payload in data.items():
    assert members[name] == {"sha256": sha(payload), "bytes": len(payload)}, name

source_path = "crates/aspis-r1-cost-probe/src/r1_wire.rs"
original = subprocess.check_output(["git", "show", summary["original_source_revision"] + ":" + source_path], cwd=REPO)
for attempt in ["candidate-a", "candidate-b"]:
    prefix = "runs/" + attempt + "/"
    pins = json.loads(data[prefix + "candidate-source/source-pins.json"])
    assert pins["source_revision"] == summary["original_source_revision"]
    assert pins["source_path"] == source_path and pins["source_sha256"] == sha(original)
    assert data[prefix + "candidate-source/original/r1_wire.rs"] == original
    for name, digest in pins["kit_files"].items():
        assert sha(data[prefix + "candidate-source/" + name]) == digest
    assert sha(data[prefix + "candidate-source/prepare.py"]) == pins["prepare_script_sha256"]
    candidate_parts = {}
    for name, cut in pins["cuts"].items():
        a, b = cut["lines"]
        exact = b"".join(original.splitlines(keepends=True)[a-1:b])
        assert sha(exact) == cut["original_sha256"]
        assert data[prefix + "candidate-source/original/" + name + ".rs"] == exact
        candidate = exact.decode()
        for old, new, count in cut["substitutions"]:
            assert candidate.count(old) == count
            candidate = candidate.replace(old, new)
        assert sha(candidate.encode()) == cut["candidate_sha256"]
        restored = candidate
        for old, new, count in reversed(cut["substitutions"]):
            assert restored.count(new) == count
            restored = restored.replace(new, old)
        assert restored.encode() == exact and cut["inverse_restores_exact_span"]
        candidate_parts[name] = candidate
    lib = ("// CANDIDATE SOURCE: interface feasibility only; not unchanged release Rust.\n#![no_std]\n#![allow(dead_code)]\n"
           + "pub mod digest {\n" + pins["candidate_trait"] + "}\n\npub mod r1_wire {\n"
           + "use crate::digest::Digest32;\n" + candidate_parts["error"] + "\n"
           + candidate_parts["transcript"] + "\n" + candidate_parts["impl"] + candidate_parts["method"] + "}\n"
           + pins.get("candidate_entry_wrapper", "") + "}\n")
    assert data[prefix + "candidate-source/lib.rs"] == lib.encode()
    artifact_pins = json.loads(data[prefix + "artifact-pins.json"])
    for name, digest in artifact_pins.items():
        assert sha(data[prefix + name]) == digest, (attempt, name)
    preflight = json.loads(data[prefix + "preflight.json"])
    assert preflight["limits"] == {"memory.high": "6442450944", "memory.max": "8589934592", "memory.swap.max": "0"}
    assert preflight["runner_sha256"] == sha(data[prefix + "runner.py"])
    for command in json.loads(data[prefix + "commands.json"]):
        assert command["exit"] == 0 and command["swap_current_bytes"] == 0 and not command["timed_out"]
        assert all(int(line.split()[1]) == 0 for line in command["events_after"].splitlines())
    llbc = json.loads(data[prefix + "DigestInterfaceCandidate.llbc"])
    assert not llbc["has_errors"]
    functions = [f for f in llbc["translated"]["fun_decls"] if f is not None]
    method = next(f for f in functions if f["item_meta"]["name"][-1].get("Ident", [None])[0] == "sample_block_validated")
    assert method["item_meta"]["opacity"] == "Transparent" and "Structured" in method["body"]
    translation = json.loads(data[prefix + "generated/translation.json"])
    ordered = llbc["translated"]["ordered_decls"]
    if attempt == "candidate-a":
        assert translation["functions"] == [] and all("TraitDecl" in x for x in ordered)
    else:
        ordered_ids = [x["Fun"]["NonRec"] for x in ordered if "Fun" in x]
        assert set(ordered_ids) == {0, 1}
        assert {f["def_id"] for f in translation["functions"]} == {0, 1}
        assert all(not f["is_opaque"] for f in translation["functions"])
        assert len(translation["trait_decls"]) == 1 and not translation["trait_impls"]
        assert sha(lib.encode()) == summary["candidate_source_sha256"]
        files = [name for name in data if name.startswith(prefix + "generated/")]
        assert len(files) == 3
        for name in files:
            if name.endswith(".lean"):
                assert not re.search(r"\b(axiom|opaque|sorry|admit)\b", data[name].decode())
        funs = data[prefix + "generated/AspisR1DigestInterfaceCandidate/Funs.lean"].decode()
        assert funs.count("← digestDigest32Inst.digest") == 3

# Exact source evidence for the root-selection diagnosis, not a compiler patch.
diagnosis = json.loads(data["root-selection-diagnosis.json"])
native = HERE.parent / "native-r18-tools-20261016"
with tarfile.open(native / "native-tools-evidence.tar.gz") as t:
    source_archive = t.extractfile("inputs/charon-exact-source.tar.gz").read()
assert sha(source_archive) == diagnosis["exact_source_archive_sha256"]
with tarfile.open(fileobj=io.BytesIO(source_archive)) as t:
    for pin in diagnosis["source_spans"]:
        payload = t.extractfile(pin["archive_member"]).read()
        assert sha(payload) == pin["file_sha256"]
        a, b = pin["lines"]
        span = b"".join(payload.splitlines(keepends=True)[a-1:b])
        assert span.decode() == pin["text"] and sha(span) == pin["span_sha256"]

backend = json.loads(data["lean/backend-object-pins.json"])
assert len(backend) == 237
for attempt in ["types-a", "funs-a", "axioms-a"]:
    prefix = "lean/runs/" + attempt + "/"
    receipt = json.loads(data[prefix + "receipt.json"])
    assert receipt == summary["lean_targets"][attempt]
    assert receipt["exit_status"] == 0 and receipt["process_swaps"] == 0 and receipt["cgroup_swap_current"] == "0"
    assert all(int(line.split()[1]) == 0 for line in receipt["memory_events_after"].splitlines())
    assert receipt["limits"] == {"memory.high": "6442450944", "memory.max": "8589934592", "memory.swap.max": "0"}
    assert "-j1" in receipt["command"] and "-M0" in receipt["command"]
    assert receipt["source_sha256"] == sha(data[prefix + "source.lean"])
    assert receipt["runner_sha256"] == sha(data[prefix + "runner.py"])
    module = receipt["target"].replace(".", "/")
    assert receipt["olean_sha256"] == sha(data["lean/objects/" + module + ".olean"])
    assert data[prefix + "source.lean"] == data["lean/sources/" + module + ".lean"]
    manifest_bytes = data["lean/input-manifest-" + attempt + ".json"]
    assert sha(manifest_bytes) == receipt["input_manifest_sha256"]
    manifest = json.loads(manifest_bytes)
    for key, name in [("backend_source_manifest_sha256", "backend-final-manifest.json"), ("backend_object_pins_sha256", "backend-object-pins.json"), ("dependency_cache_pins_sha256", "dependency-cache-pins.json")]:
        assert manifest[key] == sha(data["lean/" + name])
    for name, digest in manifest["new_sources"].items():
        assert sha(data["lean/sources/" + name]) == digest
    for name, digest in manifest["new_import_objects"].items():
        assert sha(data["lean/objects/" + name]) == digest
for name in ["Types.lean", "Funs.lean"]:
    assert data["lean/sources/AspisR1DigestInterfaceCandidate/" + name] == data["runs/candidate-b/generated/AspisR1DigestInterfaceCandidate/" + name]
log = data["lean/runs/axioms-a/lean.log"].decode()
reports = re.findall(r"depends on axioms: \[(.*?)\]", log, re.S)
assert len(reports) == 2
for report in reports:
    assert set(x.strip() for x in report.split(",")) == {"propext", "Classical.choice", "Quot.sound"}
print("PASS: candidate-only source inverses, rejected empty attempt, full method emission, three exact Lean targets and two standard audits; no production/effect claim")
