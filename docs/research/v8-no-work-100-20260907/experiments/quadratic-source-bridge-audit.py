#!/usr/bin/env python3
"""Read-only source-bridge checkpoint; no compilation or frozen-record edits."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys

EX = Path(__file__).resolve().parent
RD = EX.parent
BASE = "2c63df5aab97b826d652b2536fa269bc250386d3"
RUN_PARENT = "289d7356c78a4cd493fe61a54f9548f2a0c11298"
CENSUS_FINAL = True  # Three-leaf checkpoint only; full soundness stays open.
TARGETS = {
    "QuadraticFactorSource": ("quadratic-factor-source", 6),
    "QuadraticConstantParity": ("quadratic-constant-parity", 10),
    "QuadraticSourceDichotomy": ("quadratic-source-dichotomy", 3),
}
spec = importlib.util.spec_from_file_location("higher_y_extension", EX / "higher-y-extension-audit.py")
previous = importlib.util.module_from_spec(spec)
spec.loader.exec_module(previous)
checkpoint, old = previous.checkpoint, previous.old
require, sha, relative = old.require, old.sha, old.relative
checkpoint.TARGETS = old.TARGETS = TARGETS
old.helpers.LEAVES = TARGETS
RECEIPT = RD / "quadratic-source-bridge-transfer.json"
RECORD = RD / "quadratic-source-bridge-evidence.json"
FROZEN = (
    ("experiments/higher-y-extension-audit.py", "ca765989a97178216121278971daf53b2b3efc08cdb37298e351fb666aeba735"),
    ("higher-y-extension-evidence.json", "94a3be0ee29ccb82a5a8f9a6a45d3f58b21d49ea8686659307788d33b6ae6466"),
    ("higher-y-extension-transfer.json", "d448b20884f4dacde23d9761b5f3340064055206edceb92b6e6b479a70f142f2"),
    ("higher-y-extension-build-evidence.md", "90e58d5e9745a831082bae56f484bffb8a4079a8a844df1c8d1994413d2de893"),
)


def committed_bytes(path, expected):
    require(sha(path) == expected, "frozen extension bytes changed: " + path.name)
    relative_repo = "docs/research/v8-no-work-100-20260907/" + str(path.relative_to(RD))
    blob = subprocess.check_output(["git", "-C", str(EX), "show", BASE + ":" + relative_repo])
    require(hashlib.sha256(blob).hexdigest() == expected, "inherited source/git mismatch: " + path.name)


def inherited_extension():
    for name, digest in FROZEN:
        committed_bytes(RD / name, digest)
    evidence = json.loads((RD / "higher-y-extension-evidence.json").read_text())
    require(evidence["parent_revision"] == previous.BASE and evidence["target_census_final"] is True and
            evidence["status"] == "focused_extension_complete_not_global_security",
            "inherited extension identity/status changed")
    require(len(evidence["leaves"]) == 12 and
            sum(len(row["runs"][0]["axiom_audits"]) for row in evidence["leaves"]) == 42,
            "inherited extension census changed")
    pairs = []
    for row in evidence["leaves"]:
        require(row["status"] == "green" and len(row["runs"]) == 1, "ambiguous inherited green result")
        run = row["runs"][0]
        source = EX / row["target"]
        committed_bytes(source, run["source_sha256"])
        require(sha(source.with_suffix(".olean")) == run["olean_sha256"],
                "inherited extension output changed: " + source.stem)
        pairs.append({"source": relative(source), "source_sha256": run["source_sha256"],
                      "olean_sha256": run["olean_sha256"]})
    return {"status": "inherited_twelve_leaf_checkpoint_bytes_verified",
            "commit": BASE, "recorded_standard_axiom_audits": 42, "new_axiom_credit": 0,
            "immutable_records": [{"path": name, "sha256": digest} for name, digest in FROZEN],
            "source_output_pairs": pairs,
            "scope": "Committed bytes and retained outputs only; no prior theorem-suite replay."}


def inventory():
    data = previous.inventory()
    data["continuation_parent_revision"] = BASE
    data["inherited_extension_parent_revision"] = previous.BASE
    data["inherited_extension_receipt_sha256"] = FROZEN[2][1]
    return data


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prepare-receipt", action="store_true")
    parser.add_argument("--check-recorded", action="store_true")
    parser.add_argument("--check-snapshot", action="store_true")
    args = parser.parse_args()
    require(sum((args.prepare_receipt, args.check_recorded, args.check_snapshot)) <= 1,
            "select one mode")
    if args.prepare_receipt:
        result = inventory()
        print(json.dumps(result, indent=2))
        return int(bool(result["unmapped_artifacts"]))
    transfer = old.helpers.prior.Transfer(RECEIPT)
    require(transfer.data is not None and transfer.data.get("continuation_parent_revision") == BASE and
            transfer.data.get("overlay_research_pin") == RUN_PARENT and
            transfer.data.get("inherited_extension_receipt_sha256") == FROZEN[2][1],
            "source-bridge receipt pins changed")
    discovered = set(checkpoint.logs())
    retained = [RD / row["log"] for row in transfer.data["runs"]]
    if CENSUS_FINAL or args.check_snapshot:
        require(set(retained) == discovered, "source-bridge receipt omits a discovered attempt")
    checkpoint.FROZEN_LOGS = retained
    result = {
        "schema": "aspis-v8-quadratic-source-bridge-evidence-v1",
        "parent_revision": BASE, "executed_runner_research_pin": RUN_PARENT,
        "borrowed_formal_revision": old.helpers.prior.BORROWED,
        "lean_commit": old.helpers.prior.LEAN, "mathlib_revision": old.helpers.prior.MATHLIB,
        "auditor_sha256": sha(Path(__file__).resolve()),
        "read_only_helper_sha256": {name: sha(EX / name) for name in
            ("higher-y-extension-audit.py", "higher-y-audit.py", "audit_symbolic_ood_evidence.py",
             "audit_component_cover_evidence.py", "audit_covered_family_evidence.py",
             "audit_quotient_family_evidence.py", "audit_off_family_tail_evidence.py")},
        "target_census_final": CENSUS_FINAL, "checkpoint_only": True,
        "full_soundness_task_complete": False, "transfer_receipt_sha256": sha(RECEIPT),
        "inherited_extension": inherited_extension(),
        "inherited_seven_leaf_checkpoint": previous.inherited_checkpoint(),
        "original_bootstrap": checkpoint.bootstrap(),
        "leaves": checkpoint.leaves(transfer),
        "retained_runs": checkpoint.inherited.inherited.retained_runs(transfer),
        "attempt_source_snapshots": checkpoint.inherited.source_snapshots(transfer),
        "all_attempt_resource_contracts": previous.attempt_contract(),
        "network": {"endpoint": "dombarker@100.108.41.90", "transport": "Tailscale",
                    "host_key_alias": "nuc.local", "host_key_alias_is_network_endpoint": False},
        "global_error_bound": None, "remaining_global_allowance": None,
        "scope": "Listed deterministic source bridges only; no completed probability/sampler composition, full higher-Y coverage, checked payment extraction, privacy or Fiat-Shamir endpoint."
    }
    complete = CENSUS_FINAL and all(row["status"] == "green" for row in result["leaves"])
    result["status"] = "source_bridge_checkpoint_complete_not_global_security" if complete else "pending"
    if args.check_recorded or args.check_snapshot:
        if args.check_recorded:
            require(complete, "source-bridge census or leaf remains pending")
        require(json.loads(RECORD.read_text()) == result, "recorded source-bridge evidence differs")
        print("Quadratic source-bridge evidence matches; full soundness remains unproved.")
        return 0
    print(json.dumps(result, indent=2))
    return 0 if complete else 1


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, ValueError, KeyError, IndexError, AttributeError) as error:
        print("QUADRATIC_SOURCE_BRIDGE_EVIDENCE_REJECTED: " + str(error), file=sys.stderr)
        sys.exit(1)
