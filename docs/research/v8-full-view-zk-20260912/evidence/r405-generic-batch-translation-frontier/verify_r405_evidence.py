#!/usr/bin/env python3
"""Read-only integrity and receipt checks for the saved R405 evidence bundle."""
from __future__ import annotations
import hashlib
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[4]
PROV = HERE / "provenance"
NOTE = REPO / "docs/research/v8-full-view-zk-20260912/R405_GENERIC_BATCH_TRANSLATION_FRONTIER.md"
EXPECTED_LLBC = "399020435e94aaa7135c06d68445e9b936bd22fe6d1e1d197ee708d448d584ae"
EXPECTED_AENEAS = "29f4a784b0edb1dccf895aba78ec6d5c15c081e8602f7778db264b21272c54a0"
EXPECTED_BINARY = "f12977c5acd368d268d3af9562110ab29be60d7b4055dde937d0049f85409db5"
EXPECTED_CHARON_COMMIT = "cb50ff16b9f1066b8a97dc06da704de2da2fa41c"
EXPECTED_ROOTS = ["crate::circle_norm::joined_inverse::line_norm::r110_norm::batch"]

def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()

def load(path: Path):
    return json.loads(path.read_text())

def require(ok: bool, why: str) -> None:
    if not ok:
        raise AssertionError(why)

def check_nested_manifest(folder: Path) -> None:
    sums = folder / "SHA256SUMS"
    require(sums.is_file(), f"missing nested manifest: {sums}")
    listed: set[str] = set()
    for line in sums.read_text().splitlines():
        if not line.strip():
            continue
        digest, rel = line.split(None, 1)
        rel = rel.lstrip(" *")
        f = folder / rel
        require(f.is_file(), f"missing nested member: {f}")
        require(sha(f) == digest, f"nested SHA mismatch: {f}")
        listed.add(rel)
    actual = {p.relative_to(folder).as_posix() for p in folder.rglob("*") if p.is_file() and p != sums}
    # R396 and R398 carry a FILES.json inventory alongside their original
    # checksum manifest. Verify every entry and allow only that explicit extra.
    extra = actual - listed
    require(extra <= {"FILES.json"}, f"unexpected unmanifested nested members: {folder}: {sorted(extra)}")
    if "FILES.json" in extra:
        inventory = load(folder / "FILES.json")["files"]
        for item in inventory:
            member = folder / item["path"]
            require(member.is_file() and member.stat().st_size == item["bytes"] and sha(member) == item["sha256"], f"FILES.json mismatch: {member}")
        require({item["path"] for item in inventory} == listed, f"FILES.json inventory differs from checksum list: {folder}")
    require(listed <= actual, f"nested manifest files missing: {folder}")

def check_outer_manifest() -> None:
    sums = HERE / "SHA256SUMS"
    listed: set[str] = set()
    for line in sums.read_text().splitlines():
        if not line.strip():
            continue
        digest, rel = line.split(None, 1)
        rel = rel.lstrip(" *")
        f = HERE / rel
        require(f.is_file(), f"missing bundle member: {f}")
        require(sha(f) == digest, f"bundle SHA mismatch: {f}")
        listed.add(rel)
    actual = {p.relative_to(HERE).as_posix() for p in HERE.rglob("*") if p.is_file() and p != sums}
    require(actual == listed, "outer checksum inventory differs")
    note_sha = load(HERE / "publication-index.json")["note_sha256"]
    require(sha(NOTE) == note_sha, "research note hash mismatch")

def main() -> None:
    for name in ("r394-charon-monomorphizer-preflight", "r395-closure-representation-preflight", "r396-private-batch-unmonomorphized-plan", "r398-generic-batch-translation"):
        check_nested_manifest(PROV / name)

    llbc = PROV / "r396-private-batch-unmonomorphized-plan/R396PrivateBatchUnmonomorphized.llbc"
    require(sha(llbc) == EXPECTED_LLBC, "R396 LLBC SHA mismatch")
    r396 = load(PROV / "r396-private-batch-unmonomorphized-plan/result.json")
    require(r396["charon_exit_status"] == 0 and r396["has_errors"] is False, "R396 extraction status mismatch")
    require(r396["llbc_sha256"] == EXPECTED_LLBC, "R396 result does not bind copied LLBC")
    require(r396["start_from"] == EXPECTED_ROOTS, "R396 selected root mismatch")
    require(r396["source_revision_recorded"] == "13617a70553ed3c43cee312acba2407b29a7052d", "R396 source revision mismatch")
    # Recompute the selected declaration directly from the saved LLBC, without
    # invoking its writer-oriented historical auditor.
    raw_llbc = load(llbc)
    translated = raw_llbc["translated"]
    hashcons: dict[int, object] = {}
    def collect(x):
        if isinstance(x, dict):
            if "HashConsedValue" in x:
                ident, value = x["HashConsedValue"]
                hashcons[ident] = value
                collect(value)
            elif "Deduplicated" not in x:
                for value in x.values(): collect(value)
        elif isinstance(x, list):
            for value in x: collect(value)
    def decode(x):
        if isinstance(x, dict):
            if "HashConsedValue" in x: return decode(x["HashConsedValue"][1])
            if "Deduplicated" in x: return decode(hashcons[x["Deduplicated"]])
            return {k:decode(v) for k,v in x.items()}
        if isinstance(x, list): return [decode(v) for v in x]
        return x
    collect(raw_llbc)
    raw_fun = next(row for row in translated["fun_decls"] if isinstance(row, dict) and row.get("def_id") == 58)
    decoded_fun = decode(raw_fun)
    require(raw_llbc["has_errors"] is False, "R396 raw LLBC has_errors mismatch")
    require(raw_fun["item_meta"]["span"]["data"]["beg"]["line"] == 2486 and raw_fun["item_meta"]["span"]["data"]["end"]["line"] == 2490, "raw LLBC try_fold span mismatch")
    require(raw_fun["body"] not in (None, "Opaque"), "raw LLBC try_fold body missing")
    raw_generics = decoded_fun["generics"]
    require(len(raw_generics["regions"]) == 1 and len(raw_generics["types"]) == 5 and len(raw_generics["trait_clauses"]) == 4, "raw try_fold binders/clauses mismatch")
    def count_erased(x):
        if isinstance(x, dict): return sum(1 for k in x if k == "Erased") + sum(count_erased(v) for v in x.values())
        if isinstance(x, list): return sum(count_erased(v) for v in x)
        return 0
    require(count_erased({"generics":raw_generics,"signature":decoded_fun["signature"]}) == 0, "raw try_fold signature contains erased regions")
    constraints = raw_generics["trait_type_constraints"]
    require(len(constraints) == 1, "raw LLBC associated equality count mismatch")
    constraint = constraints[0]["skip_binder"]
    require(constraint["type_id"] == 0 and constraint["ty"] == {"TypeVar":{"Free":1}}, "raw LLBC equality RHS/type id mismatch")
    require(constraint["trait_ref"]["kind"] == {"Clause":{"Free":3}}, "raw LLBC equality trait clause mismatch")
    clause3 = raw_generics["trait_clauses"][3]["trait_"]["skip_binder"]
    require(clause3["id"] == 11 and clause3["generics"]["types"] == [{"TypeVar":{"Free":3}}], "raw LLBC clause 3 is not Try<R>")
    try_trait = next(row for row in translated["trait_decls"] if isinstance(row, dict) and row.get("def_id") == 11)
    trait_name = "::".join(part["Ident"][0] for part in try_trait["item_meta"]["name"] if "Ident" in part)
    require(trait_name == "core::ops::try_trait::Try", "raw associated trait is not core::ops::Try")
    output_assoc = try_trait["types"][0]["skip_binder"]
    require(output_assoc["name"] == "Output" and try_trait["types"][0]["kind"] == {"TraitType":[11,0]}, "raw trait type id 0 is not Try::Output")
    audit396 = load(PROV / "r396-private-batch-unmonomorphized-plan/selected-try-fold-row.json")["summary"]["selected_target"]
    require(audit396["def_id"] == 58 and audit396["body_status"] == "structured", "try_fold identity/body mismatch")
    require(audit396["qualified_name"] == "core::iter::traits::iterator::Iterator::try_fold", "try_fold name mismatch")
    require(audit396["source_span"]["data"]["beg"]["line"] == 2486 and audit396["source_span"]["data"]["end"]["line"] == 2490, "try_fold source span mismatch")
    require(len(audit396["trait_type_constraints"]) == 1, "associated constraint count mismatch")
    require(audit396["erased_region_occurrences_in_decoded_row"] == 0, "decoded signature has erased regions")
    try_fold_census = load(PROV / "r396-private-batch-unmonomorphized-plan/try-fold-census.json")
    require(try_fold_census["all_matching_try_fold_rows"][0]["def_id"] == 58, "try_fold census target mismatch")
    extract_command = load(PROV / "r396-private-batch-unmonomorphized-plan/extract-command.json")
    require(extract_command["monomorphize"] is False, "R396 monomorphization mode mismatch")
    require(extract_command["source_revision_recorded"] == r396["source_revision_recorded"], "R396 command/result revision mismatch")
    require(extract_command["rustflags_sha256"] == load(PROV / "r396-private-batch-unmonomorphized-plan/launch.json")["rustflags_sha256"], "R396 rustflags launch mismatch")
    require(extract_command["start_from"] == EXPECTED_ROOTS and extract_command["include"] == r396["include"], "R396 root/include command mismatch")
    require(extract_command["verified_source_hashes"] == r396["source_hashes"], "R396 source hash set differs between command and result")
    launch396 = load(PROV / "r396-private-batch-unmonomorphized-plan/launch.json")
    require(launch396["caps"] == {"MemoryHigh":"5G", "MemoryMax":"7G", "MemorySwapMax":"0", "TasksMax":128}, "R396 launch caps mismatch")
    require(launch396["rustflags_sha256"] == extract_command["rustflags_sha256"], "R396 launch rustflags hash mismatch")
    toolchain = (PROV / "r396-private-batch-unmonomorphized-plan/toolchain.txt").read_text()
    require("release: 1.98.0-nightly" in toolchain and "charon_sha256=b2b0961a3c55aca64752b2fa4a4701ba0c06b860236979e5727c07de8ac2310c" in toolchain, "R396 pinned toolchain/Charon mismatch")
    extract_log = (PROV / "r396-private-batch-unmonomorphized-plan/extract.log").read_text()
    require("Elapsed (wall clock) time (h:mm:ss or m:ss): 0:13.66" in extract_log, "R396 wall-time mismatch")
    require("Maximum resident set size (kbytes): 623720" in extract_log, "R396 RSS mismatch")
    require("Swaps: 0" in extract_log and "Exit status: 0" in extract_log, "R396 swap/exit mismatch")

    r398dir = PROV / "r398-generic-batch-translation"
    audit398 = load(r398dir / "saved-evidence-audit.json")
    require(audit398["input_llbc_sha256"] == EXPECTED_LLBC, "R398 input hash differs from R396")
    require(audit398["binary_sha256"] == EXPECTED_BINARY, "R398 binary SHA mismatch")
    require(audit398["translator_exit_status"] == 2 and audit398["translation_output_generated"] is False, "R398 status/output mismatch")
    require(audit398["metrics"]["wall_time"] == "0:00.23" and audit398["metrics"]["max_rss_kib"] == 71280 and audit398["metrics"]["swaps"] == 0, "R398 metrics mismatch")
    require(audit398["launch_revision"] == "13617a70553ed3c43cee312acba2407b29a7052d" and audit398["source_revision"] == audit398["launch_revision"], "R398 launch/source revision mismatch")
    require(audit398["launcher_exit_status"] == 2 and audit398["scp_exit_status"] == 0 and audit398["metrics"]["time_exit_status"] == 2, "R398 subprocess statuses mismatch")
    require(audit398["resource_caps"] == {"MemoryHigh":"5G", "MemoryMax":"7G", "MemorySwapMax":"0", "TasksMax":128}, "R398 caps mismatch")
    run = "output/13617a70553e-20261002T165818Z"
    command = load(r398dir / run / "translate-command.json")
    result = load(r398dir / run / "translation-result.json")
    require(command["source_sha256"] == EXPECTED_LLBC and command["binary_sha256"] == EXPECTED_BINARY, "R398 command hashes mismatch")
    require(result["translator_exit_status"] == 2 and result["generated_dir_exists"] is False and result["manifest_function_entries"] == 0, "R398 output inventory mismatch")
    require(command["source_revision"] == audit398["source_revision"] and command["launch_revision"] == audit398["launch_revision"], "R398 command revision mismatch")
    require(command["scope_caps"] == audit398["resource_caps"], "R398 command caps mismatch")
    require(result["source_gate"]["generic_try_fold_body_present"] is True, "R398 did not record try_fold body")
    fail_log = (r398dir / run / "translate.log").read_text()
    require("SymbolicToPureTypes.ml, line 1047" in fail_log and "sanity_check_opt_span" in fail_log, "R398 failure diagnostic mismatch")

    aeneas = PROV / "pinned-aeneas-r385/src/symbolic/SymbolicToPureTypes.ml"
    require(sha(aeneas) == EXPECTED_AENEAS, "pinned Aeneas source hash mismatch")
    a_meta = load(HERE / "pinned-aeneas-source.json")
    require(a_meta["sha256"] == EXPECTED_AENEAS and a_meta["bytes"] == aeneas.stat().st_size, "pinned source metadata mismatch")
    identity = load(PROV / "aeneas-source-identity-crosscheck.json")
    require(identity["sha256"] == EXPECTED_AENEAS, "tracked pinned-source cross-reference SHA mismatch")
    src_lines = aeneas.read_text().splitlines()
    require("[%sanity_check_opt_span] span" in src_lines[1046], "assertion line 1047 mismatch")
    require("sg.item_binder_params.trait_type_constraints = []" in src_lines[1047], "assertion line 1048 mismatch")
    require(load(PROV / "r394-charon-monomorphizer-preflight/provenance.json")["pinned_source_identity"]["commit"] == EXPECTED_CHARON_COMMIT, "R394 Charon source commit mismatch")
    check_outer_manifest()
    print("R405 saved evidence: PASS (checksum inventories, R396 extraction identity, R398 failed translation receipt, pinned assertion source, and note linkage)")

if __name__ == "__main__":
    main()
