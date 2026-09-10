#!/usr/bin/env python3
"""Read-only two-leaf causal checkpoint; no old-suite or sampler replay."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys

EX = Path(__file__).resolve().parent
RD = EX.parent
BASE = "51692ed712ecb646b51e15e4b8e93e149a6b4014"
RUN_PARENT = "289d7356c78a4cd493fe61a54f9548f2a0c11298"
CENSUS_FINAL = True  # Two-leaf checkpoint only, not the full soundness task.
TARGETS = {
    "SelectedQuadraticReduction": ("selected-quadratic-reduction", 2),
    "CausalQuadraticReduction": ("causal-quadratic-reduction", 4),
}
spec = importlib.util.spec_from_file_location("quadratic_selected_family", EX / "quadratic-selected-family-audit.py")
previous = importlib.util.module_from_spec(spec)
spec.loader.exec_module(previous)
checkpoint, old = previous.checkpoint, previous.old
require, sha, relative = old.require, old.sha, old.relative
checkpoint.TARGETS = old.TARGETS = TARGETS
old.helpers.LEAVES = TARGETS
RECEIPT = RD / "quadratic-causal-transfer.json"
RECORD = RD / "quadratic-causal-evidence.json"
FROZEN = (
    ("experiments/quadratic-selected-family-audit.py", "e7f007ee38170320d8377b1ba5b19b4c80e7cad5fefad4e154539d130b9c7b3a"),
    ("quadratic-selected-family-evidence.json", "6330d9716e2942b1db313c84f276766de774bc4913fa966a33a5c423450712e0"),
    ("quadratic-selected-family-transfer.json", "eda229225a91923ab9c0ea8612b0ac1cddc53c7d56c64196c845eb1f03c16b87"),
    ("quadratic-selected-family-build-evidence.md", "d842bd4ff0f383b77585acd20e33d1534fd2491f8974130bf2def36d97720299"),
)


def committed_bytes(path, expected):
    require(sha(path) == expected, "frozen selected-family bytes changed: " + path.name)
    name = "docs/research/v8-no-work-100-20260907/" + str(path.relative_to(RD))
    blob = subprocess.check_output(["git", "-C", str(EX), "show", BASE + ":" + name])
    require(hashlib.sha256(blob).hexdigest() == expected, "inherited source/git mismatch: " + name)


def inherited_selected_family():
    for name, digest in FROZEN:
        committed_bytes(RD / name, digest)
    data = json.loads((RD / "quadratic-selected-family-evidence.json").read_text())
    require(data["parent_revision"] == previous.BASE and data["target_census_final"] is True and
            data["status"] == "selected_family_checkpoint_complete_not_global_security",
            "inherited selected-family identity/status changed")
    require(len(data["leaves"]) == 4 and
            sum(len(row["runs"][0]["axiom_audits"]) for row in data["leaves"]) == 9,
            "inherited selected-family census changed")
    pairs = []
    for row in data["leaves"]:
        require(row["status"] == "green" and len(row["runs"]) == 1, "ambiguous inherited result")
        run = row["runs"][0]
        source = EX / row["target"]
        committed_bytes(source, run["source_sha256"])
        require(sha(source.with_suffix(".olean")) == run["olean_sha256"],
                "inherited output changed: " + source.stem)
        pairs.append({"source": relative(source), "source_sha256": run["source_sha256"],
                      "olean_sha256": run["olean_sha256"]})
    return {"status": "inherited_selected_family_bytes_verified", "commit": BASE,
            "recorded_standard_axiom_audits": 9, "new_axiom_credit": 0,
            "immutable_records": [{"path": name, "sha256": digest} for name, digest in FROZEN],
            "source_output_pairs": pairs, "scope": "Byte/source-origin audit, not a theorem-suite replay."}


def inventory():
    data = previous.inventory()
    data["continuation_parent_revision"] = BASE
    data["inherited_selected_family_parent_revision"] = previous.BASE
    data["inherited_selected_family_receipt_sha256"] = FROZEN[2][1]
    return data


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prepare-receipt", action="store_true")
    parser.add_argument("--check-recorded", action="store_true")
    parser.add_argument("--check-snapshot", action="store_true")
    args = parser.parse_args()
    require(sum((args.prepare_receipt, args.check_recorded, args.check_snapshot)) <= 1, "select one mode")
    if args.prepare_receipt:
        data = inventory()
        print(json.dumps(data, indent=2))
        return int(bool(data["unmapped_artifacts"]))
    transfer = old.helpers.prior.Transfer(RECEIPT)
    require(transfer.data is not None and transfer.data.get("continuation_parent_revision") == BASE and
            transfer.data.get("overlay_research_pin") == RUN_PARENT and
            transfer.data.get("inherited_selected_family_receipt_sha256") == FROZEN[2][1],
            "quadratic-causal receipt pins changed")
    discovered = set(checkpoint.logs())
    retained = [RD / row["log"] for row in transfer.data["runs"]]
    if CENSUS_FINAL or args.check_snapshot:
        require(set(retained) == discovered, "causal receipt omits a discovered attempt")
    checkpoint.FROZEN_LOGS = retained
    result = {
        "schema": "aspis-v8-quadratic-causal-evidence-v1",
        "parent_revision": BASE, "executed_runner_research_pin": RUN_PARENT,
        "borrowed_formal_revision": old.helpers.prior.BORROWED,
        "lean_commit": old.helpers.prior.LEAN, "mathlib_revision": old.helpers.prior.MATHLIB,
        "auditor_sha256": sha(Path(__file__).resolve()),
        "read_only_helper_sha256": {name: sha(EX / name) for name in
            ("quadratic-selected-family-audit.py", "quadratic-source-bridge-audit.py",
             "higher-y-extension-audit.py", "higher-y-audit.py", "audit_symbolic_ood_evidence.py",
             "audit_component_cover_evidence.py", "audit_covered_family_evidence.py",
             "audit_quotient_family_evidence.py", "audit_off_family_tail_evidence.py")},
        "target_census_final": CENSUS_FINAL, "checkpoint_only": True,
        "full_soundness_task_complete": False, "transfer_receipt_sha256": sha(RECEIPT),
        "inherited_selected_family": inherited_selected_family(),
        "inherited_source_bridge": previous.inherited_source_bridge(),
        "inherited_extension": previous.previous.inherited_extension(),
        "inherited_seven_leaf_checkpoint": previous.previous.previous.inherited_checkpoint(),
        "original_bootstrap": checkpoint.bootstrap(),
        "leaves": checkpoint.leaves(transfer),
        "retained_runs": checkpoint.inherited.inherited.retained_runs(transfer),
        "attempt_source_snapshots": checkpoint.inherited.source_snapshots(transfer),
        "all_attempt_resource_contracts": previous.previous.previous.attempt_contract(),
        "network": {"endpoint": "dombarker@100.108.41.90", "transport": "Tailscale",
                    "host_key_alias": "nuc.local", "host_key_alias_is_network_endpoint": False},
        "excluded_non_theorem_work": ["separate source OOD sampler audit"],
        "global_error_bound": None, "remaining_global_allowance": None,
        "scope": "Two scoped reduction leaves retaining the OOD-root indicator and complementary accepted mass; no proved actual OOD sampler law, full extraction/security, privacy or Fiat-Shamir endpoint."
    }
    complete = CENSUS_FINAL and all(row["status"] == "green" for row in result["leaves"])
    result["status"] = "quadratic_causal_checkpoint_complete_not_global_security" if complete else "pending"
    if args.check_recorded or args.check_snapshot:
        if args.check_recorded:
            require(complete, "causal checkpoint leaf remains pending")
        require(json.loads(RECORD.read_text()) == result, "recorded causal evidence differs")
        print("Quadratic causal checkpoint evidence matches; actual OOD sampling and full soundness remain open.")
        return 0
    print(json.dumps(result, indent=2))
    return 0 if complete else 1


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, ValueError, KeyError, IndexError, AttributeError) as error:
        print("QUADRATIC_CAUSAL_EVIDENCE_REJECTED: " + str(error), file=sys.stderr)
        sys.exit(1)
