#!/usr/bin/env python3
import hashlib
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent
manifest = json.loads((ROOT / "manifest.json").read_text())
assert manifest["schema"] == "focused-extractor-proof-packet-v1"
assert manifest["packet"] == ROOT.name
assert manifest["compiled_objects_included"] is False
assert manifest["artifacts_policy"].endswith("no compiled Lean objects included")
assert manifest["owned_pair_field_funs_sha256"] == "fb5a57c6532f2a016f380a063eb03211548b8d427ea54b4666c7a92575c8a8f8"
assert manifest["candidate_helper_funs_sha256"] == "3ddd2dae0b066aaddcb80cf88f5fc9dc7103d868894cedc0d508f054006cb775"

# The base revision is a commit; generated Lean owners are separately pinned overlays.
revision = manifest["source_revision"]
assert re.fullmatch(r"[0-9a-f]{40}", revision["source_base_revision"])
assert revision["source_base_revision"] == "8faec0c3bac2944980a732b242b323325a759f2c"
assert len(revision["owned_source_overrides"]) == 2
for override in revision["owned_source_overrides"]:
    assert re.fullmatch(r"[0-9a-f]{40}", override["source_revision_at_compile"])
    assert re.fullmatch(r"[0-9a-f]{64}", override["source_sha256"])
    assert re.fullmatch(r"[0-9a-f]{64}", override["object_sha256"])
    source_manifest = json.loads((ROOT / override["evidence_manifest"]).read_text())
    assert source_manifest["compiled_objects_included"] is False
    if override["name"] == "owned-backed Pair caller Funs":
        owner = source_manifest["entries"]["funs"]
    elif override["name"] == "candidate helper Funs":
        owner = next(e for e in source_manifest["entries"] if e["module"] == "AspisR1S9CandidateHelperV1/Funs")
    else:
        raise AssertionError(override["name"])
    assert owner["source_sha256"] == override["source_sha256"]
    owner_object = owner.get("object_sha256", owner.get("launch_metrics", {}).get("object_sha256"))
    assert owner_object == override["object_sha256"]

allow = set(manifest["accepted_axiom_allowlist"])
assert allow == {"propext", "Classical.choice", "Quot.sound"}
report_pattern = re.compile(r"depends on axioms:\s*\[([^]]*)\]", re.S)
def reports(log_text):
    out = []
    for match in report_pattern.finditer(log_text):
        names = set(re.findall(r"[A-Za-z_][A-Za-z0-9_.]*", match.group(1)))
        out.append(names)
    return out

for name, entry in manifest["modules"].items():
    source = ROOT / entry["source"]
    assert source.is_file(), (name, source)
    actual = hashlib.sha256(source.read_bytes()).hexdigest()
    assert actual == entry["source_sha256"], (name, actual, entry["source_sha256"])
    module_dir = ROOT / "modules" / name
    receipt = json.loads((module_dir / "receipt.json").read_text())
    preflight = json.loads((module_dir / "preflight.json").read_text())
    log_text = (module_dir / "lean.log").read_text()
    assert receipt["exit_status"] == 0, name
    assert receipt["source_sha256"] == actual, name
    assert receipt["object_sha256"] == entry["object_sha256"], name
    assert preflight["source_sha256"] == actual, name
    assert preflight["limits"] == {"memory.high": "3221225472", "memory.max": "4294967296", "memory.swap.max": "0"}, name
    assert receipt["scope_swap_peak_bytes"] == 0, name
    assert receipt["wall_seconds"] > 0 and receipt["peak_process_rss_kib"] > 0, name
    assert receipt["scope_memory_peak_bytes"] >= 0, name
    assert (module_dir / "command.json").is_file()
    if name != "scalar-candidate-map":
        module_reports = reports(log_text)
        assert module_reports, f"no #print axioms output in {name}"
        assert all(names <= allow for names in module_reports), (name, module_reports)
    for imported, sha in entry["direct_imports"].items():
        if imported == "AspisR1S9PairCallerStepV1.Funs":
            assert sha == manifest["owned_pair_field_funs_sha256"], (name, imported, sha)
        if imported == "AspisR1S9CandidateHelperV1.Funs":
            assert sha == manifest["candidate_helper_funs_sha256"], (name, imported, sha)

# The scalar-to-candidate theorem's original compile omitted #print axioms. Its
# focused follow-up is complete, is tied to that exact theorem, and is required.
audit = ROOT / manifest["additional_source_only_audit"]
assert audit.is_file()
assert hashlib.sha256(audit.read_bytes()).hexdigest() == manifest["audit_source_sha256"]
assert manifest["axiom_audit"]["status"] == "completed"
assert manifest["axiom_audit"]["compiled_objects_included"] is False
assert manifest["axiom_audit"]["covers_module"] == "scalar-candidate-map"
assert manifest["axiom_audit"]["covers_theorem"] == "AspisR1S9PairCallerScalarFactorCandidateMapV1.pair_scalar_factor_maps_to_candidate"
audit_ev = ROOT / "modules/scalar-candidate-map/axiom-audit-evidence"
audit_receipt = json.loads((audit_ev / "receipt.json").read_text())
audit_preflight = json.loads((audit_ev / "preflight.json").read_text())
audit_log = (audit_ev / "lean.log").read_text()
assert audit_receipt["exit_status"] == 0
assert audit_receipt["source_sha256"] == manifest["audit_source_sha256"]
assert audit_receipt["object_sha256"] == manifest["axiom_audit"]["object_sha256"]
assert audit_receipt["scope_swap_peak_bytes"] == 0
assert audit_preflight["limits"] == {"memory.high": "3221225472", "memory.max": "4294967296", "memory.swap.max": "0"}
assert manifest["axiom_audit"]["axioms"] == ["propext", "Classical.choice", "Quot.sound"]
assert "'AspisR1S9PairCallerScalarFactorCandidateMapV1.pair_scalar_factor_maps_to_candidate' depends on axioms:" in audit_log
assert all(names <= allow for names in reports(audit_log)), reports(audit_log)

for path in ROOT.rglob("*"):
    if path.is_file():
        assert path.suffix not in {".olean", ".ilean", ".c", ".o", ".so", ".a", ".dylib", ".dll", ".exe"}, path
print("packet schema, sources, receipts, structured owner pins, axiom reports, and source-only constraints: PASS")
print("scalar-candidate-map axiom audit: PASS [propext, Classical.choice, Quot.sound]")
