#!/usr/bin/env python3
"""Read-only extension audit; preserves the committed seven-leaf checkpoint."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys

EX = Path(__file__).resolve().parent
RD = EX.parent
BASE = "9bc0ceee408f432c879ff2239e3ec565dedcd409"
RUN_PARENT = "289d7356c78a4cd493fe61a54f9548f2a0c11298"
CENSUS_FINAL = True  # This twelve-leaf checkpoint, not the full higher-Y task.
TARGETS = {
    "QuadraticSpecializationSylvester": ("quadratic-specialization-sylvester", 5),
    "QuadraticSquareCancellation": ("quadratic-square-cancellation", 2),
    "QuadraticDiscriminantNonsquare": ("quadratic-discriminant-nonsquare", 6),
    "QuadraticSpecializationGuarded": ("quadratic-specialization-guarded", 3),
    "PolynomialParityFactorization": ("polynomial-parity-factorization", 4),
    "QuadraticParitySeparable": ("quadratic-parity-separable", 2),
    "QuadraticParityCharacteristic": ("quadratic-parity-characteristic", 3),
    "QuadraticSpecializationOdd": ("quadratic-specialization-odd", 5),
    "PolynomialParityLocalization": ("polynomial-parity-localization", 5),
    "QuadraticResultantDescent": ("quadratic-resultant-descent", 1),
    "QuadraticSpecializationTotal": ("quadratic-specialization-total", 4),
    "QuadraticConstructedParity": ("quadratic-constructed-parity", 2),
}
spec = importlib.util.spec_from_file_location("higher_y_checkpoint", EX / "higher-y-audit.py")
checkpoint = importlib.util.module_from_spec(spec)
spec.loader.exec_module(checkpoint)
old = checkpoint.old
require, sha, relative = old.require, old.sha, old.relative
checkpoint.TARGETS = TARGETS
old.TARGETS = TARGETS
old.helpers.LEAVES = TARGETS
RECEIPT = RD / "higher-y-extension-transfer.json"
RECORD = RD / "higher-y-extension-evidence.json"
FROZEN = (
    ("experiments/higher-y-audit.py", "293a6aff09da159068c118feabdbfbe10189b3720e97b16c0ba4b4a07f50365a"),
    ("higher-y-evidence.json", "ab7137e1a4243a906755c80fdd6e05d283caa849c1d370816f41a18103c2e8df"),
    ("higher-y-transfer.json", "44fbb6cacb00c219f2cb7dc4544dbb6ff9fcf305423cc301268fb264290f2f95"),
    ("higher-y-build-evidence.md", "0aaf64bc34428e4a6d48f09fd4f85e67d6407e0d48b8ffb2ddcf37811f823080"),
)


def committed_bytes(path, expected):
    require(sha(path) == expected, "committed inherited bytes changed: " + path.name)
    repo_path = "docs/research/v8-no-work-100-20260907/" + str(path.relative_to(RD))
    raw = subprocess.check_output(["git", "-C", str(EX), "show", BASE + ":" + repo_path])
    require(hashlib.sha256(raw).hexdigest() == expected, "new-parent source mismatch: " + repo_path)


def inherited_checkpoint():
    for name, digest in FROZEN:
        committed_bytes(RD / name, digest)
    prior = json.loads((RD / "higher-y-evidence.json").read_text())
    require(prior["parent_revision"] == RUN_PARENT and prior["checkpoint"]["complete"] is True,
            "inherited checkpoint identity changed")
    require(len(prior["leaves"]) == 7 and
            sum(len(row["runs"][0]["axiom_audits"]) for row in prior["leaves"]) == 33,
            "inherited checkpoint census changed")
    checked = []
    for row in prior["leaves"]:
        require(row["status"] == "green" and len(row["runs"]) == 1, "non-green inherited leaf")
        run = row["runs"][0]
        source = EX / row["target"]
        committed_bytes(source, run["source_sha256"])
        output = source.with_suffix(".olean")
        require(sha(output) == run["olean_sha256"], "inherited output changed: " + output.name)
        checked.append({"source": relative(source), "source_sha256": run["source_sha256"],
                        "olean_sha256": run["olean_sha256"]})
    return {"status": "inherited_seven_leaf_checkpoint_bytes_verified",
            "commit": BASE, "original_research_parent": RUN_PARENT,
            "recorded_standard_axiom_audits": 33, "new_axiom_credit": 0,
            "immutable_records": [{"path": path, "sha256": digest} for path, digest in FROZEN],
            "source_output_pairs": checked,
            "scope": "Committed source blobs and retained outputs checked; no old Lean suite or Rust control replay."}


def inventory():
    data = old.inventory()
    # A failed target can be edited immediately after its log is copied.
    # Preserve the immutable attempted bytes, never that mutable pathname.
    snapshots = {}
    for path in checkpoint.logs():
        source = EX / (path.stem + "-source.txt")
        if source.exists():
            snapshots[sha(source)] = source
    for entry in data["artifacts"]:
        retained = snapshots.get(entry["sha256"])
        if retained is not None and entry["remote_path"].endswith(".lean"):
            entry["local_path"] = relative(retained)
            entry["retention"] = "Immutable runner-created attempt snapshot; current draft pathname may advance."
    require(data["research"] == RUN_PARENT, "actual overlay parent changed")
    data["continuation_parent_revision"] = BASE
    data["overlay_research_pin"] = RUN_PARENT
    data["inherited_checkpoint_receipt_sha256"] = FROZEN[2][1]
    data["ssh_endpoint"] = "dombarker@100.108.41.90"
    data["ssh_options"] = ["BatchMode=yes", "ConnectTimeout=10",
                          "StrictHostKeyChecking=yes", "HostKeyAlias=nuc.local"]
    data["host_key_alias_only"] = True
    return data


def attempt_contract():
    result = []
    for path in checkpoint.logs():
        text = path.read_text()
        require(re.findall(r"^RESEARCH_PIN=(.+)$", text, re.M) == [RUN_PARENT],
                "attempt runner parent mismatch: " + path.name)
        require(old.helpers.prior.BORROWED in text and old.helpers.prior.LEAN in text,
                "attempt borrowed/toolchain pins absent")
        for name, value in (("memory.high", 8 * 1024**3), ("memory.max", 10 * 1024**3),
                            ("memory.swap.max", 0)):
            require(re.findall(r"^" + re.escape(name) + r"=(\d+)\s*$", text, re.M) == [str(value)],
                    "attempt cgroup property mismatch: " + path.name)
        require(re.findall(r"^cpu.max=(.+)$", text, re.M) == ["200000 100000"],
                "attempt CPU cap mismatch")
        command = re.findall(r"^COMMAND=(.+)$", text, re.M)
        require(len(command) == 1 and " -j1 -M9500 " in command[0],
                "attempt literal command/heap/thread profile absent")
        resources = old.helpers.prior.measurements(text)
        require(len(resources) == 1 and resources[0]["swaps"] == 0 and
                resources[0]["peak_rss_bytes"] <= 10 * 1024**3,
                "attempt resource evidence outside authorized profile")
        exits = re.findall(r"^LEAN_EXIT=(\d+)\s*$", text, re.M)
        require(len(exits) == 1 and re.findall(r"Exit status: (\d+)", text) == exits,
                "attempt GNU/Lean terminal mismatch")
        result.append({"log": relative(path), "exit": int(exits[0]),
                       "command": command[0], "measurement": resources[0]})
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prepare-receipt", action="store_true")
    parser.add_argument("--check-recorded", action="store_true")
    parser.add_argument("--check-snapshot", action="store_true")
    args = parser.parse_args()
    require(sum((args.prepare_receipt, args.check_recorded, args.check_snapshot)) <= 1,
            "select one check mode")
    if args.prepare_receipt:
        data = inventory()
        print(json.dumps(data, indent=2))
        return int(bool(data["unmapped_artifacts"]))
    transfer = old.helpers.prior.Transfer(RECEIPT)
    require(transfer.data is not None and transfer.data.get("continuation_parent_revision") == BASE,
            "missing extension receipt or continuation parent")
    require(transfer.data.get("overlay_research_pin") == RUN_PARENT and
            transfer.data.get("inherited_checkpoint_receipt_sha256") == FROZEN[2][1],
            "overlay/checkpoint origins changed")
    discovered = set(checkpoint.logs())
    retained = [RD / run["log"] for run in transfer.data["runs"]]
    if CENSUS_FINAL or args.check_snapshot:
        require(set(retained) == discovered, "receipt omits a discovered extension attempt")
    checkpoint.FROZEN_LOGS = retained
    data = {
        "schema": "aspis-v8-higher-y-extension-evidence-v1",
        "parent_revision": BASE, "executed_runner_research_pin": RUN_PARENT,
        "borrowed_formal_revision": old.helpers.prior.BORROWED,
        "mathlib_revision": old.helpers.prior.MATHLIB, "lean_commit": old.helpers.prior.LEAN,
        "auditor_sha256": sha(Path(__file__).resolve()),
        "inherited_helper_sha256": {name: sha(EX / name) for name in
            ("higher-y-audit.py", "audit_symbolic_ood_evidence.py",
             "audit_component_cover_evidence.py", "audit_covered_family_evidence.py",
             "audit_quotient_family_evidence.py", "audit_off_family_tail_evidence.py")},
        "target_census_final": CENSUS_FINAL,
        "checkpoint_only": True,
        "full_higher_y_continuation_complete": False,
        "later_checkpoint_exclusions": ["selected source bridge", "constant-parity composition"],
        "transfer_receipt_sha256": sha(RECEIPT),
        "inherited_checkpoint": inherited_checkpoint(),
        "original_bootstrap": checkpoint.bootstrap(),
        "leaves": checkpoint.leaves(transfer),
        "retained_runs": checkpoint.inherited.inherited.retained_runs(transfer),
        "attempt_source_snapshots": checkpoint.inherited.source_snapshots(transfer),
        "all_attempt_resource_contracts": attempt_contract(),
        "network": {"endpoint": "dombarker@100.108.41.90", "transport": "Tailscale",
                    "host_key_alias": "nuc.local", "host_key_alias_is_network_endpoint": False},
        "global_error_bound": None, "global_remaining_allowance": None,
        "scope": "New algebraic implications only. No new sampler law, selected global higher-Y bound, checked payment extraction, privacy or Fiat-Shamir endpoint."
    }
    complete = CENSUS_FINAL and all(row["status"] == "green" for row in data["leaves"])
    data["status"] = "focused_extension_complete_not_global_security" if complete else "pending"
    if args.check_recorded or args.check_snapshot:
        if args.check_recorded:
            require(complete, "extension census or leaf remains pending")
        require(json.loads(RECORD.read_text()) == data, "recorded extension evidence differs")
        print("Higher-Y extension evidence snapshot matches; global security remains unproved.")
        return 0
    print(json.dumps(data, indent=2))
    return 0 if complete else 1


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, ValueError, KeyError, IndexError, AttributeError) as error:
        print("HIGHER_Y_EXTENSION_EVIDENCE_REJECTED: " + str(error), file=sys.stderr)
        sys.exit(1)
