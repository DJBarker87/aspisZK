#!/usr/bin/env python3
"""Read-only verifier for R360/R361 primary tool-frontier evidence."""
from __future__ import annotations
import hashlib
import json
from pathlib import Path

root = Path(__file__).resolve().parent
manifest = root / "SHA256SUMS"
entries = {}
for line in manifest.read_text().splitlines():
    digest, rel = line.split("  ", 1)
    entries[rel] = digest
actual = {p.relative_to(root).as_posix() for p in root.rglob("*") if p.is_file() and p != manifest}
missing, unlisted, bad = sorted(set(entries)-actual), sorted(actual-set(entries)), []
for rel,digest in entries.items():
    p=root/rel
    if p.exists() and hashlib.sha256(p.read_bytes()).hexdigest()!=digest:
        bad.append(rel)

r360=root/"r360-comment-context-candidate"
build=r360/"build-evidence/078a3bd7d447-20261002T121921Z"
hist=r360/"history/launch-078a3bd7d447-20261002T121921Z"
r361=root/"r361-controlflow-comment-translation"
post=r360/"postbuild-source-audit"
result=json.loads((build/"build-result.json").read_text())
command=json.loads((build/"build-command.json").read_text())
receipt=json.loads((hist/"launch-receipt.json").read_text())
launch_result=json.loads((hist/"launch-result.json").read_text())
post_audit=json.loads((post/"audit.json").read_text())
r361_result=json.loads((r361/"result.json").read_text())
r361_command=json.loads((r361/"command.json").read_text())
r361_launch=json.loads((r361/"launch.json").read_text())
build_time=(build/"compiler-gnu-time.txt").read_text()
docker_time=(build/"docker-cli-time.txt").read_text()
translate=(r361/"translate.log").read_text()
partial=(r361/"generated/AspisR361ControlFlowComment/Types.lean").read_text()
projection=r361/"R334ControlFlowSourceProjection.llbc"
summary=json.loads((root/"R360-R361-summary.json").read_text())

launch_rev="078a3bd7d4471a5f10549843e7818b956163bb77"
parent_rev="56a931fc3879354a2fa584e73bd0a1d412714851"
binary="8a6cc181f75bf1c2ac64fa8c5db2bc896d5f7908b21ef94389217d9c3392c416"
projection_sha="8b9bd55e374866294b591758e1282d08998cb002e30b070207156b61f81a69ca"
checks={
 "manifest_matches_all_files_including_nested_manifests":not missing and not unlisted,
 "all_bundle_hashes_match":not bad,
 "R360_launch_parent_and_binary_identity_match_primary_receipts":result.get("launch_revision")==launch_rev and command.get("launch_revision")==launch_rev and receipt.get("launch_revision_captured_at_launch")==launch_rev and launch_result.get("launch_revision_captured_at_launch")==launch_rev and result.get("source_revision_of_R349_candidate")==parent_rev and command.get("source_revision_of_R349_candidate")==parent_rev and result.get("binary_sha256")==binary,
 "R360_source_candidate_and_patch_hashes_match":result.get("candidate_source_tree_sha256_before_build")=="3a855903889ca3cdffc0580065e974c408087f2d83d467260704c5a39a7efff8" and result.get("candidate_ExtractTypes_sha256")=="0f8ee29aa89c9456ea6c266ff8d767dcb8a83af5bbe8096d04e53582cb32c527" and hashlib.sha256((r360/"ExtractTypes.patch.diff").read_bytes()).hexdigest()=="95338d049cc8a9c0e5a0f29972e3061d45649c9ef7cafc0e617c2564fb10a9d1",
 "R360_pristine_and_materialized_runner_hashes_match_receipt":hashlib.sha256((hist/"run_cached_build-before-revision-capture.py").read_bytes()).hexdigest()=="051b086a915b0f6b461233fe885fd628e809b284feab8cce377777a9d57e916f" and hashlib.sha256((build/"run_cached_build.py").read_bytes()).hexdigest()==receipt.get("runner_sha256_after_revision_capture") and result.get("build_exit_status")==0 and launch_result.get("launcher_exit_status")==0,
 "R360_compiler_measurements_match_GNU_time": "Elapsed (wall clock) time (h:mm:ss or m:ss): 0:08.70" in build_time and "Maximum resident set size (kbytes): 522492" in build_time and "Swaps: 0" in build_time and "Exit status: 0" in build_time,
 "R360_Docker_RSS_is_parent_only":command.get("docker_cli_time_rss_label","").startswith("Docker CLI parent-process RSS only") and "Elapsed (wall clock) time (h:mm:ss or m:ss): 0:09.03" in docker_time and "Maximum resident set size (kbytes): 28336" in docker_time,
 "R360_postbuild_audit_passes_with_build_only_delta":post_audit.get("status", "").startswith("postbuild source/cache inventory passed") and post_audit.get("all_postbuild_changes_under_build") is True and post_audit.get("postbuild_changed_path_count_vs_candidate_prebuild")==33 and post_audit.get("non_build_changed_paths_vs_candidate_prebuild")==[] and post_audit.get("parent_non_build_differences_vs_exact_saved_R349_manifest")==[] and post_audit.get("shared_regular_file_inode_count")==0 and post_audit.get("R360_executable",{}).get("sha256")==binary,
 "R360_did_not_translate_or_compile_Lean":result.get("translation_or_Lean_compile_run") is False and result.get("binary_exists") is True,
 "R361_projection_and_binary_match_primary_inputs":hashlib.sha256(projection.read_bytes()).hexdigest()==projection_sha and r361_result.get("source_sha256")==projection_sha and r361_command.get("source_sha256")==projection_sha and r361_result.get("binary_sha256")==binary and r361_command.get("binary_sha256")==binary,
 "R361_failure_and_partial_output_match_primary_records":r361_result.get("exit_status")==2 and set(r361_result.get("generated_files",{}))=={"generated/AspisR361ControlFlowComment/Types.lean"} and hashlib.sha256((r361/"generated/AspisR361ControlFlowComment/Types.lean").read_bytes()).hexdigest()=="2e0624d3cdef8defb47bf2ffe46eb4f3de21106eb9ff90066424e940d31c0737" and "NameMatcher.ml:1166" in translate and "extract_attributes" in translate and "ExtractTypes.ml\", line 1288" in translate and "def " not in partial and r361_result.get("Lean_compiled") is False,
 "R361_GNU_time_metrics_match_translation_log":"Elapsed (wall clock) time (h:mm:ss or m:ss): 0:00.24" in translate and "Maximum resident set size (kbytes): 55968" in translate and "Swaps: 0" in translate and "Exit status: 2" in translate,
 "R360_caps_match_primary_receipt":receipt.get("systemd_caps")=={"MemoryHigh":"5G","MemoryMax":"7G","MemorySwapMax":"0","TasksMax":128} and receipt.get("docker_caps",{}).get("memory")=="7g" and receipt.get("docker_caps",{}).get("memory_swap")=="7g (equal to memory; zero swap)",
 "R361_systemd_caps_are_recorded":all(x in r361_launch.get("argv",[]) for x in ["MemoryHigh=5G","MemoryMax=7G","MemorySwapMax=0","TasksMax=128"]) and json.loads((r361/"host-reservation-before.json").read_text()).get("caps")=={"MemoryHigh":"5G","MemoryMax":"7G","MemorySwapMax":0,"TasksMax":128} and "Memory peak: 512.0K" in (r361/"launch.log").read_text(),
 "R352_prior_R351_failure_is_retained":(root/"r352-comment-emission-preflight/R351-translate.log").exists() and json.loads((root/"r352-comment-emission-preflight/R351-result.json").read_text()).get("exit_status")==2,
 "report_states_translation_and_axioms_as_not_applicable":r361_result.get("print_axioms")=="N/A; translation only" and summary.get("R361",{}).get("Lean_compiled") is False,
}
report={"status":"PASS" if all(checks.values()) else "FAIL","checks":checks,"manifest_file_count":len(entries),"actual_file_count":len(actual),"missing":missing,"unlisted":unlisted,"hash_mismatches":bad,"primary_values":{"R360_exit":result.get("build_exit_status"),"R360_binary_sha256":result.get("binary_sha256"),"R361_exit":r361_result.get("exit_status"),"R361_input_sha256":r361_result.get("source_sha256"),"R361_partial_Types_sha256":r361_result.get("generated_files",{}).get("generated/AspisR361ControlFlowComment/Types.lean")}}
print(json.dumps(report,indent=2))
if not all(checks.values()): raise SystemExit(1)
