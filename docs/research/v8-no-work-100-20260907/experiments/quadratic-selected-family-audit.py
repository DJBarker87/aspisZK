#!/usr/bin/env python3
"""Read-only selected-family checkpoint; earlier checkpoint bytes are immutable."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys

EX = Path(__file__).resolve().parent
RD = EX.parent
BASE = "be7a1731bd4d71de50fa39767a53523bf0bc9ff0"
RUN_PARENT = "289d7356c78a4cd493fe61a54f9548f2a0c11298"
CENSUS_FINAL = True  # Four-leaf checkpoint only; full soundness stays open.
TARGETS = {
    "QuadraticSelectedDegree": ("quadratic-selected-degree", 4),
    "QuadraticSourceSharp": ("quadratic-source-sharp", 2),
    "QuadraticFamilyAssembly": ("quadratic-family-assembly", 1),
    "SelectedQuadraticCover": ("selected-quadratic-cover", 2),
}
spec = importlib.util.spec_from_file_location("quadratic_source_bridge", EX / "quadratic-source-bridge-audit.py")
previous = importlib.util.module_from_spec(spec)
spec.loader.exec_module(previous)
checkpoint, old = previous.checkpoint, previous.old
require, sha, relative = old.require, old.sha, old.relative
checkpoint.TARGETS = old.TARGETS = TARGETS
old.helpers.LEAVES = TARGETS
RECEIPT = RD / "quadratic-selected-family-transfer.json"
RECORD = RD / "quadratic-selected-family-evidence.json"
FROZEN = (
    ("experiments/quadratic-source-bridge-audit.py", "e0ac7e9f099fe58ecc9a7955e987a9400803e710ab4db383d2b2ef98f6d96e91"),
    ("quadratic-source-bridge-evidence.json", "cfc77046ee56357ee2a69446c827376300ce8818b8b8fdf21bb3511c08dc2da2"),
    ("quadratic-source-bridge-transfer.json", "9ea12d38771afb78696fd0aed85fe6a421be6f6e3cf07e16a78fa3f5daf1a1dc"),
    ("quadratic-source-bridge-build-evidence.md", "7e24b1dffd48641898d0006d0ddedb9c0e8dbef92d46c62224b84eb25e721f46"),
)


def committed_bytes(path, expected):
    require(sha(path) == expected, "frozen source-bridge bytes changed: " + path.name)
    name = "docs/research/v8-no-work-100-20260907/" + str(path.relative_to(RD))
    blob = subprocess.check_output(["git", "-C", str(EX), "show", BASE + ":" + name])
    require(hashlib.sha256(blob).hexdigest() == expected, "inherited source/git mismatch: " + name)


def inherited_source_bridge():
    for name, digest in FROZEN:
        committed_bytes(RD / name, digest)
    data = json.loads((RD / "quadratic-source-bridge-evidence.json").read_text())
    require(data["parent_revision"] == previous.BASE and data["target_census_final"] is True and
            data["status"] == "source_bridge_checkpoint_complete_not_global_security",
            "inherited source-bridge identity/status changed")
    require(len(data["leaves"]) == 3 and
            sum(len(row["runs"][0]["axiom_audits"]) for row in data["leaves"]) == 19,
            "inherited source-bridge census changed")
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
    return {"status": "inherited_source_bridge_bytes_verified", "commit": BASE,
            "recorded_standard_axiom_audits": 19, "new_axiom_credit": 0,
            "immutable_records": [{"path": name, "sha256": digest} for name, digest in FROZEN],
            "source_output_pairs": pairs, "scope": "Byte/source-origin audit, not a theorem-suite replay."}


def inventory():
    data = previous.inventory()
    data["continuation_parent_revision"] = BASE
    data["inherited_source_bridge_parent_revision"] = previous.BASE
    data["inherited_source_bridge_receipt_sha256"] = FROZEN[2][1]
    return data


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prepare-receipt", action="store_true")
    parser.add_argument("--check-recorded", action="store_true")
    parser.add_argument("--check-snapshot", action="store_true")
    args = parser.parse_args()
    require(sum((args.prepare_receipt, args.check_recorded, args.check_snapshot)) <= 1, "select one mode")
    if args.prepare_receipt:
        result = inventory()
        print(json.dumps(result, indent=2))
        return int(bool(result["unmapped_artifacts"]))
    transfer = old.helpers.prior.Transfer(RECEIPT)
    require(transfer.data is not None and transfer.data.get("continuation_parent_revision") == BASE and
            transfer.data.get("overlay_research_pin") == RUN_PARENT and
            transfer.data.get("inherited_source_bridge_receipt_sha256") == FROZEN[2][1],
            "selected-family receipt pins changed")
    discovered = set(checkpoint.logs())
    retained = [RD / row["log"] for row in transfer.data["runs"]]
    if CENSUS_FINAL or args.check_snapshot:
        require(set(retained) == discovered, "selected-family receipt omits a discovered attempt")
    checkpoint.FROZEN_LOGS = retained
    result = {
        "schema": "aspis-v8-quadratic-selected-family-evidence-v1",
        "parent_revision": BASE, "executed_runner_research_pin": RUN_PARENT,
        "borrowed_formal_revision": old.helpers.prior.BORROWED,
        "lean_commit": old.helpers.prior.LEAN, "mathlib_revision": old.helpers.prior.MATHLIB,
        "auditor_sha256": sha(Path(__file__).resolve()),
        "read_only_helper_sha256": {name: sha(EX / name) for name in
            ("quadratic-source-bridge-audit.py", "higher-y-extension-audit.py", "higher-y-audit.py",
             "audit_symbolic_ood_evidence.py", "audit_component_cover_evidence.py",
             "audit_covered_family_evidence.py", "audit_quotient_family_evidence.py",
             "audit_off_family_tail_evidence.py")},
        "target_census_final": CENSUS_FINAL, "checkpoint_only": True,
        "full_soundness_task_complete": False, "transfer_receipt_sha256": sha(RECEIPT),
        "inherited_source_bridge": inherited_source_bridge(),
        "inherited_extension": previous.inherited_extension(),
        "inherited_seven_leaf_checkpoint": previous.previous.inherited_checkpoint(),
        "original_bootstrap": checkpoint.bootstrap(),
        "leaves": checkpoint.leaves(transfer),
        "retained_runs": checkpoint.inherited.inherited.retained_runs(transfer),
        "attempt_source_snapshots": checkpoint.inherited.source_snapshots(transfer),
        "all_attempt_resource_contracts": previous.previous.attempt_contract(),
        "network": {"endpoint": "dombarker@100.108.41.90", "transport": "Tailscale",
                    "host_key_alias": "nuc.local", "host_key_alias_is_network_endpoint": False},
        "global_error_bound": None, "remaining_global_allowance": None,
        "scope": "Listed deterministic fixed-family/degree bridges only; no complete causal sampler probability, all higher-Y coverage, checked payment extraction, privacy or Fiat-Shamir endpoint."
    }
    complete = CENSUS_FINAL and all(row["status"] == "green" for row in result["leaves"])
    result["status"] = "selected_family_checkpoint_complete_not_global_security" if complete else "pending"
    if args.check_recorded or args.check_snapshot:
        if args.check_recorded:
            require(complete, "selected-family census or leaf remains pending")
        require(json.loads(RECORD.read_text()) == result, "recorded selected-family evidence differs")
        print("Quadratic selected-family evidence matches; full soundness remains unproved.")
        return 0
    print(json.dumps(result, indent=2))
    return 0 if complete else 1


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, ValueError, KeyError, IndexError, AttributeError) as error:
        print("QUADRATIC_SELECTED_FAMILY_EVIDENCE_REJECTED: " + str(error), file=sys.stderr)
        sys.exit(1)
