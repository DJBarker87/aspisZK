#!/usr/bin/env python3
"""Read-only consistency audit of published R305/R306 saved evidence."""
from __future__ import annotations
import hashlib, json, re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
DOCS = ROOT / "docs/research/v8-full-view-zk-20260912"
BUNDLES = {
    "R305": {
        "slug": "r305-current-batch-reverse-raw",
        "target": DOCS / "lean/AspisR305BatchReverseRaw.lean",
        "log": "logs/aspis-focus-1790921662646829000.log",
        "axiom_names": [
            "AspisR305BatchReverseRaw.circle_norm.joined_inverse.line_norm.r110_norm.batch_loop2.body",
            "AspisR305BatchReverseRaw.circle_norm.joined_inverse.line_norm.r110_norm.batch_loop2",
            "AspisR305BatchReverseRaw.circle_norm.joined_inverse.line_norm.r110_norm.batch_loop3.body",
            "AspisR305BatchReverseRaw.circle_norm.joined_inverse.line_norm.r110_norm.batch_loop3",
        ],
        "expected": ("0:01.11", 2535516, 0, 0),
    },
    "R306": {
        "slug": "r306-current-batch-reverse-step-execution",
        "target": DOCS / "lean/AspisV8R19/R306BatchReverseStepExecution.lean",
        "log": "logs/aspis-focus-1790921971199603000.log",
        "axiom_names": [
            f"AspisV8R19.R306BatchReverseStepExecution.{n}" for n in [
                "wrapping_sub_one_val", "reverse_next_done", "reverse_next_step",
                "body2_done", "body2_step", "body3_eq_body2",
            ]
        ],
        "expected": ("0:01.70", 3724492, 0, 0),
    },
}
FOUNDATIONS = {"propext", "Classical.choice", "Quot.sound"}
AXIOM_RE = re.compile(r"^'([^']+)' depends on axioms: \[(.*?)\]", re.M | re.S)


def sha(b: bytes) -> str:
    return hashlib.sha256(b).hexdigest()


def axiom_map(text: str) -> dict[str, tuple[str, ...]]:
    return {name: tuple(x.strip() for x in body.replace("\n", " ").split(","))
            for name, body in AXIOM_RE.findall(text)}

results = {"audit": "saved-evidence read-only audit; no compilation", "bundles": {}, "findings": []}
for label, cfg in BUNDLES.items():
    d = DOCS / "evidence" / cfg["slug"]
    manifest = json.loads((d / "manifest.json").read_text())
    sums = json.loads((d / "SHA256SUMS.json").read_text())
    listed_bad, listed_missing = [], []
    for rel, expected in sums.items():
        p = d / rel
        if not p.is_file(): listed_missing.append(rel)
        elif sha(p.read_bytes()) != expected: listed_bad.append(rel)
    actual_files = {str(p.relative_to(d)) for p in d.rglob("*")
                    if p.is_file() and p.name != "SHA256SUMS.json"}
    unlisted = sorted(actual_files - set(sums))
    target_sha = sha(cfg["target"].read_bytes())
    source_copy = d / "source" / cfg["target"].name
    source_sha = sha(source_copy.read_bytes())
    log_text = (d / cfg["log"]).read_text()
    t = re.search(r"Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([^\n]+)", log_text)
    rss = re.search(r"Maximum resident set size \(kbytes\): (\d+)", log_text)
    swaps = re.search(r"Swaps: (\d+)", log_text)
    exit_status = re.search(r"Exit status: (\d+)", log_text)
    metrics = (t.group(1), int(rss.group(1)), int(swaps.group(1)), int(exit_status.group(1)))
    log_axioms = axiom_map(log_text)
    file_axioms = axiom_map((d / "axioms.txt").read_text())
    reports_exact = log_axioms == file_axioms
    foundations_only = bool(log_axioms) and all(set(a) == FOUNDATIONS for a in log_axioms.values())
    report = {
        "hash_manifest_entries": len(sums),
        "missing_or_bad_hashes": listed_missing + listed_bad,
        "unlisted_bundle_files": unlisted,
        "target_sha256": target_sha,
        "manifest_source_sha256": manifest["source_sha256"],
        "source_copy_sha256": source_sha,
        "target_equals_evidence_copy": cfg["target"].read_bytes() == source_copy.read_bytes(),
        "metrics_wall_rss_kib_swaps_exit": list(metrics),
        "manifest_wall_rss_kib_swaps_exit": [manifest["wall_time"], manifest["peak_rss_kib"], manifest["swaps"], manifest["exit_status"]],
        "metrics_match": metrics == cfg["expected"] == (manifest["wall_time"], manifest["peak_rss_kib"], manifest["swaps"], manifest["exit_status"]),
        "axiom_report_count": len(file_axioms),
        "axiom_names_match_expected": sorted(file_axioms) == sorted(cfg["axiom_names"]),
        "axioms_file_matches_success_log": reports_exact,
        "all_axioms_foundations_only": foundations_only,
        "resource_scope": manifest["resources"],
        "source_revision": manifest["source_revision"],
        "lean_version": manifest["lean_version"],
        "log_has_success": "Finished with result: success" in log_text,
        "log_has_scope_caps": all(x in (d / "run_focus.py").read_text() for x in ["MemoryHigh=5G", "MemoryMax=7G", "MemorySwapMax=0", "TasksMax=128"]),
        "no_sorryAx_in_success_axioms": "sorryAx" not in (d / "axioms.txt").read_text(),
    }
    results["bundles"][label] = report
    for key in ["missing_or_bad_hashes", "unlisted_bundle_files"]:
        if report[key]: results["findings"].append(f"{label}: {key} = {report[key]}")
    for key in ["target_equals_evidence_copy", "metrics_match", "axiom_names_match_expected", "axioms_file_matches_success_log", "all_axioms_foundations_only", "log_has_success", "log_has_scope_caps", "no_sorryAx_in_success_axioms"]:
        if not report[key]: results["findings"].append(f"{label}: {key} failed")

# Independently check the four R305 copied definition blocks against the saved R292 generated input.
r305 = DOCS / "evidence/r305-current-batch-reverse-raw"
raw_audit = r305 / "raw-adapter-audit"
raw_source = raw_audit / "source-does-not-exist"
input_funs = raw_audit / "provenance/R292Funs.input.lean"
target_text = (DOCS / "lean/AspisR305BatchReverseRaw.lean").read_text()
input_text = input_funs.read_text()
names = [
    "circle_norm.joined_inverse.line_norm.r110_norm.batch_loop2.body",
    "circle_norm.joined_inverse.line_norm.r110_norm.batch_loop2",
    "circle_norm.joined_inverse.line_norm.r110_norm.batch_loop3.body",
    "circle_norm.joined_inverse.line_norm.r110_norm.batch_loop3",
]
block_results = {}
for name in names:
    hits = list(re.finditer(r"(?m)^def " + re.escape(name) + r"(?:\s|$)", input_text))
    if len(hits) != 1:
        block_results[name] = False
        continue
    at = hits[0].start()
    st = input_text.rfind("/--", 0, at)
    en = input_text.find("/--", at)
    if en < 0: en = len(input_text)
    block = input_text[st:en].rstrip("\n")
    block_results[name] = target_text.count(block) == 1
results["R305_exact_generated_blocks_preserved"] = block_results
if not all(block_results.values()): results["findings"].append("R305: one or more generated declaration blocks differ")

# R305 helper/template audit was saved before compilation; confirm actual published source/multiplication call count.
raw_binding = json.loads((raw_audit / "binding-audit.json").read_text())
raw_target = (DOCS / "lean/AspisR305BatchReverseRaw.lean").read_text()
results["R305_binding_audit"] = {
    "B_alias_and_mul_type_documented": "B_alias_R292" in raw_binding["binding_facts"] and "B_mul_type" in raw_binding["binding_facts"],
    "R292_R249_mul_literal_difference_documented": "31#i32" in raw_binding["binding_facts"]["B_mul_body_difference"] and "31#u32" in raw_binding["binding_facts"]["B_mul_body_difference"],
    "all_six_external_templates_named": len(raw_binding["direct_template_scan"]["absent_names"]) == 6,
    "body_mul_call_count": raw_target.count(".B.mul"),
    "library_semantics_boundary_named": "does not prove their correspondence to Rust library semantics" in raw_binding["library_boundary"],
    "R249_copy_matches_current_tracked_source": sha((DOCS / "lean/AspisR249R110Raw.lean").read_bytes()) == sha((raw_audit / "provenance/AspisR249R110Raw.input.lean").read_bytes()),
    "R249_source_copy_sha256": sha((raw_audit / "provenance/AspisR249R110Raw.input.lean").read_bytes()),
    "stale_prestaging_axiom_status": raw_binding["status"],
    "stale_prestaging_axiom_note": raw_binding["axioms"],
}
if raw_target.count(".B.mul") != 4:
    results["findings"].append("R305: expected four direct body calls to B.mul")
# The provenance note is historically precompile, but its unqualified current tense conflicts with its containing compiled evidence bundle.
results["findings"].append("R305 metadata note: raw-adapter-audit/binding-audit.json still labels the copied source as unverified/no compile and says its #print axioms have not run, although the surrounding bundle records the successful compile and four matching reports. Treat as a stale historical annotation, not a proof/log mismatch.")
results["findings"].append("R305 nested raw-adapter-audit/SHA256SUMS retains original .r21-scratch workspace-relative paths, so it is not runnable from the nested published directory; entries match their original scratch files here, and the outer SHA256SUMS.json fully covers the published bundle.")

# Rejected artifacts and boundary phrases are checked without executing any compiler.
rej305 = r305 / "raw-adapter-audit/rejected-namespace-scaffold"
rej306 = DOCS / "evidence/r306-current-batch-reverse-step-execution/library-and-rejected-proof-preflight/rejected"
results["rejected_history"] = {
    "R305_scaffold_files": sorted(p.name for p in rej305.iterdir()),
    "R305_failure_reason": json.loads((rej305 / "reason.json").read_text())["reason"],
    "R305_rejected_log_has_unknown_Std_Usize": "Unknown identifier `Std.Usize`" in (rej305 / "aspis-focus-1790921602657201000.log").read_text(),
    "R306_rejected_draft_count": len(list(rej306.glob("draft-*.lean"))),
    "R306_rejected_log_count": len(list(rej306.glob("*.log"))),
    "all_R306_rejected_logs_have_sorryAx": all("sorryAx" in p.read_text() for p in rej306.glob("*.log")),
}

# Check the archived input manifests against their original inputs as well as the outer bundles.
raw_inner = (raw_audit / "SHA256SUMS").read_text().splitlines()
raw_scratch_checks = []
for line in raw_inner:
    expected, rel = line.split(None, 1)
    p = ROOT / rel.strip()
    raw_scratch_checks.append(p.is_file() and sha(p.read_bytes()) == expected)
r306_pre = DOCS / "evidence/r306-current-batch-reverse-step-execution/library-and-rejected-proof-preflight"
r306_hashes = json.loads((r306_pre / "source-hashes.json").read_text())
r306_lib_checks = {rel: (r306_pre / rel).is_file() and sha((r306_pre / rel).read_bytes()) == row["sha256"] for rel, row in r306_hashes.items()}
results["copied_input_manifests"] = {
    "R305_original_scratch_sum_entries": len(raw_inner),
    "R305_original_scratch_files_match": all(raw_scratch_checks),
    "R305_nested_sum_paths_are_relative_to_original_workspace_not_bundle": any(line.split(None, 1)[1].startswith(".r21-scratch/") for line in raw_inner),
    "R306_pinned_library_source_hash_count": len(r306_hashes),
    "R306_pinned_library_sources_match_source_hashes_json": all(r306_lib_checks.values()),
    "R306_pinned_library_source_checks": r306_lib_checks,
}
if not all(raw_scratch_checks) or not all(r306_lib_checks.values()):
    results["findings"].append("Copied input manifest/source-hash check failed")
if results["rejected_history"]["R306_rejected_draft_count"] != 3 or results["rejected_history"]["R306_rejected_log_count"] != 3 or not results["rejected_history"]["all_R306_rejected_logs_have_sorryAx"]:
    results["findings"].append("R306 rejected history inventory mismatch")

note305 = (DOCS / "R305_CURRENT_BATCH_REVERSE_RAW.md").read_text()
note306 = (DOCS / "R306_CURRENT_BATCH_REVERSE_STEP_EXECUTION.md").read_text()
results["scope_language"] = {
    "R305_no_complete_Rust_traversal_claim": "not a complete Rust traversal correspondence theorem" in note305,
    "R305_remaining_library_correspondence": "independently close the Rust correspondence" in note305,
    "R306_caller_premises_explicit": "does not establish them for the batch caller" in note306,
    "R306_zero_guard_and_chronology_open": "prove the batch zero guard" in note306 and "full callback chronology" in note306,
    "R306_source_std_correspondence_open": "close independent standard-library source correspondence" in note306,
    "security_boundary_open": "soundness remain open" in note305 and "soundness remain open" in note306,
}
if not all(results["scope_language"].values()): results["findings"].append("Scope-language boundary check failed")

results["overall"] = "PASS_WITH_TWO_DOCUMENTATION_CAVEATS" if len(results["findings"]) == 2 else ("PASS" if not results["findings"] else "FINDINGS")
OUT = Path(__file__).resolve().parent / "audit.json"
OUT.write_text(json.dumps(results, indent=2) + "\n")
print(json.dumps(results, indent=2))
