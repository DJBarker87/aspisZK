#!/usr/bin/env python3
"""Authorized copy-only five-module closure for SelectedV7SemanticProjection.

No compiler; no existing path replacement. Sources match borrowed26a9.
The four existing native/overlay olean variants are recorded, not equated.
"""
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

TASK = Path("/home/dombarker/project-offloads/aspis-higher-y.fMoMeX")
CACHE = Path("/home/dombarker/project-offloads/ZK-v7-clean-k16-20260831/AspisFormal")
PIN = "26a9cd4718aae9f9de7ef1c3394fb74a229085d5"
PREFIX = "v7-atomic-projection-cache"
DATA = [
    ("Pool/V7AtomicSemanticRowsFromTrace", "9b6dec4c38031c839b556af1b6cef935d743ad649be23ba299c3b004218076f7", "b77c39df140b97046e957736fa8cd989d22b897a3f1becf48aa197d6a22a512b", "6b5407605bb9b5b901cd9f77dfb462838c3e4f773362b1d81b84fbe647d31482", 6),
    ("Pool/V7OpenedColumnsFromTrace", "2b3847a3aebe348b6d146b7c9088f530cb93a0fead833aa9d37eca9d8ffdb87d", "9e30a11f386017877072ec81ae300662aa3a11476881e834c7ab0b91639e391f", "da3a7e85b9ee63878697ba0d9ae1b0f8e14758c9235782c5bf574f90d75da449", 6),
    ("V5ProductionPublicResidualBinding", "ef80dfa0fa34567305b53a4560c79a8c4e05a2f84637839142201e5684fac75b", "b55b55806987829eb0e298385798013d3759005b867194e992b942cef72fc4fa", "8ba658314adfb81b2731dfcc3e32af462cff67baa087679c818b74b3ab532555", 25),
    ("V5TowerPackedResidualExtraction", "b61aa03c19f0217a2878e0a59ad1e4d8f390ebb7ed94fb96475fa285b0f667eb", "e2a9b45258a9d7a075d9e731d60e739e8f25107e6c9f76d296d0d1c1b858d904", "8b9291b176fc48bc6544e709b65a188854c453a879fe54d8af174a35b0903a99", 5),
    ("V5ConstraintLaneBatching", "1fb412d5430943e0061227231d208cd91799deacb5829ad517695b9eb26f53c6", "521664ad6c5ce50c026d555cb0cc369ad7e8c2178d3eec4bc4973205ed8976f7", "94dd6ccecd97cb4787f52a4afe9434347d63c2446bc444c48a2efb6398570c4d", 6),
]
BOUNDARY = ["ArithmetizationCore", "SoundnessLedger", "V5AcceptedSpendRelation", "V5FriConcreteEncoderApplicability"]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def exclusive(path, data):
    with path.open("xb") as stream:
        stream.write(data)


def no_compiler():
    rows = subprocess.check_output(["ps", "-eo", "pid=,stat=,comm=,args="], text=True).splitlines()
    live = [r for r in rows if len(r.split()) >= 3 and r.split()[2] in {"lean", "lake"}
            and not r.split()[1].startswith("Z")]
    assert not live, live


def verify_local():
    root = Path(__file__).resolve().parents[4]
    for name, source_hash, *_ in DATA:
        path = Path("AspisFormal/AspisFormal") / (name + ".lean")
        pinned = subprocess.check_output(["git", "show", PIN + ":" + str(path)], cwd=root)
        assert pinned == (root / path).read_bytes()
        assert hashlib.sha256(pinned).hexdigest() == source_hash
    print("BORROWED_FIVE_SOURCE_PIN_PASS=true")


def append_reserved():
    no_compiler()
    manifest_path = TASK / "manifest.json"
    state_path = TASK / "green-outputs.json"
    before, state_before = manifest_path.read_bytes(), state_path.read_bytes()
    manifest, state = json.loads(before), json.loads(state_before)
    indexed = {e["overlay"]: e for e in manifest["files"]}
    known = {e["module"] for e in manifest["files"]}
    assert not any("AspisFormal." + name.replace("/", ".") in known for name, *_ in DATA)
    subprocess.run([sys.executable, str(TASK / "verify_masked_nuc.py"), str(TASK), str(CACHE)], check=True)
    for name, entry in state.items():
        assert sha(TASK / "overlay" / (name + ".lean")) == entry["source"]
        for suffix, digest in entry["outputs"].items():
            assert sha(TASK / "overlay" / (name + suffix)) == digest
    boundary = []
    for name in BOUNDARY:
        rel = "AspisFormal/" + name
        native_source, native_olean = CACHE / (rel + ".lean"), CACHE / ".lake/build/lib/lean" / (rel + ".olean")
        assert indexed[rel + ".lean"]["sha256"] == sha(native_source)
        boundary.append({"module": rel.replace("/", "."), "source_sha256": sha(native_source),
                         "native_olean_sha256": sha(native_olean),
                         "frozen_overlay_olean_sha256": indexed[rel + ".olean"]["sha256"]})
    entries, copies, traces = [], [], []
    allowed = {"AspisFormal." + name.replace("/", ".") for name, *_ in DATA} | {
        "AspisFormal." + name for name in BOUNDARY}
    for name, source_hash, olean_hash, trace_hash, count in DATA:
        rel = "AspisFormal/" + name
        source, output = CACHE / (rel + ".lean"), CACHE / ".lake/build/lib/lean" / (rel + ".olean")
        trace = output.with_suffix(".trace")
        assert sha(source) == source_hash and sha(output) == olean_hash and sha(trace) == trace_hash
        imports = [line[7:].strip() for line in source.read_text().splitlines() if line.startswith("import ")]
        assert set(imports) <= allowed, (name, imports)
        with output.open("rb") as stream:
            header = stream.read(64)
        assert b"4.32.0" in header and b"8c9756b28d64dab099da31a4" in header
        data = json.loads(trace.read_text())
        assert data["synthetic"] is False and not any(row["level"] == "error" for row in data["log"])
        audit = re.findall(r"depends on axioms:\s*\[([^]]*)\]", "\n".join(row["message"] for row in data["log"]))
        assert len(audit) == count
        assert all({a.strip() for a in axioms.split(",")} <= {"propext", "Classical.choice", "Quot.sound"} for axioms in audit)
        traces.append((trace, PREFIX + "-" + name.replace("/", "-") + "-trace.json", trace_hash, count))
        for suffix, kind, path, digest in [(".lean", "source", source, source_hash), (".olean", "olean", output, olean_hash)]:
            target = TASK / "overlay" / (rel + suffix)
            if target.exists():
                assert sha(target) == digest, "Refuse existing overlay variant replacement"
            else:
                copies.append((path, target))
            entries.append({"module": rel.replace("/", "."), "category": "borrowed", "kind": kind,
                            "package": None, "local": None, "overlay": rel + suffix,
                            "remote_cache": str(path), "sha256": digest, "bytes": path.stat().st_size})
    no_compiler()
    exclusive(TASK / (PREFIX + "-before.json"), before)
    for path, target in copies:
        target.parent.mkdir(parents=True, exist_ok=True)
        exclusive(target, path.read_bytes())
    for path, name, *_ in traces:
        exclusive(TASK / name, path.read_bytes())
    manifest["files"].extend(entries)
    manifest["counts"] = {"pinned_source_blobs": sum(e["kind"] == "source" for e in manifest["files"]),
                          "compiled_artifacts": sum(e["kind"] == "olean" for e in manifest["files"])}
    after = (json.dumps(manifest, indent=2) + "\n").encode()
    exclusive(TASK / (PREFIX + "-after.json"), after)
    temporary = TASK / (PREFIX + "-append.json")
    exclusive(temporary, after)
    assert manifest_path.read_bytes() == before and state_path.read_bytes() == state_before
    temporary.replace(manifest_path)
    subprocess.run([sys.executable, str(TASK / "verify_masked_nuc.py"), str(TASK), str(CACHE)], check=True)
    assert state_path.read_bytes() == state_before
    receipt = {"status": "verified_copy_only_five_module_append", "source_pin": PIN,
               "source_parent": "5cadd01c7af31a8ebe1a00e4bfed77c1e9c77b59", "task": str(TASK),
               "helper_sha256": sha(Path(__file__)), "before_sha256": hashlib.sha256(before).hexdigest(),
               "after_sha256": sha(manifest_path), "green_state_unchanged": hashlib.sha256(state_before).hexdigest(),
               "entries": entries, "after_entries": len(manifest["files"]),
               "trace_evidence": [{"file": name, "sha256": digest, "standard_audits": count} for _, name, digest, count in traces],
               "mixed_cache_boundaries": boundary, "compiler_launched": False,
               "copied_files": len(copies), "existing_path_replacements": 0,
               "boundary": "Five native retained Lean4.32 pairs with borrowed source pin; four same-source/different-olean frozen boundary pairs preserved. Focused consumer check required; no prior mixed-cache replay claimed."}
    exclusive(TASK / (PREFIX + "-receipt.json"), (json.dumps(receipt, indent=2) + "\n").encode())
    print(json.dumps(receipt, indent=2))


if __name__ == "__main__":
    if sys.argv[1:] == ["--verify-local"]:
        verify_local()
    elif sys.argv[1:] == ["--append-reserved"]:
        append_reserved()
    else:
        raise SystemExit("Use --verify-local or --append-reserved")
