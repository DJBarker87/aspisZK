#!/usr/bin/env python3
"""Read-only higher-Y evidence: no compiler, remote call or old-suite replay."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

import audit_symbolic_ood_evidence as inherited

old = inherited.old
EX, RD = old.EX, old.RD
BASE = "289d7356c78a4cd493fe61a54f9548f2a0c11298"
INITIAL = EX / "higher-y-initial-manifest.json"
INITIAL_SHA = "46c0485b661719d093fa8392783e36f42f5f446fa95d54525f3e0438ff232ab1"
CENSUS_FINAL = False
FROZEN_LOGS = None
TARGETS = {"SimplePolynomialRootRigidity": ("simple-polynomial-root-rigidity", 3),
    "SelectedSimpleRootRigidity": ("selected-simple-root-rigidity", 4),
    "QuadraticSpecializationDeterminant": ("quadratic-specialization-determinant", 5),
    "QuadraticSpecializationKernel": ("quadratic-specialization-kernel", 8),
    "QuadraticSpecializationCount": ("quadratic-specialization-count", 2),
    "QuadraticSpecializationBasis": ("quadratic-specialization-basis", 2),
    "QuadraticTwistObstruction": ("quadratic-twist-obstruction", 9)}
CHECKPOINT_TARGETS = tuple(TARGETS)
old.BASE = old.helpers.BASE = old.helpers.prior.BASE = BASE
old.INITIAL, old.INITIAL_SHA, old.TARGETS = INITIAL, INITIAL_SHA, TARGETS
require, sha, relative = old.require, old.sha, old.relative


def target_logs(name):
    result = []
    paths = EX.glob(TARGETS[name][0] + "-*.log") if FROZEN_LOGS is None else FROZEN_LOGS
    for path in sorted(paths):
        target = re.search(r"^TARGET=(.+)$", path.read_text(), re.M)
        require(target and target.group(1) in TARGETS, "unexpected proof log: " + path.name)
        if target.group(1) == name:
            result.append(path)
    return result


def logs():
    if FROZEN_LOGS is not None:
        return sorted(FROZEN_LOGS)
    return sorted({path for name in TARGETS for path in target_logs(name)})


old.logs = logs


def leaves(transfer):
    result = []
    for name in TARGETS:
        green, diagnostics = [], []
        for path in target_logs(name):
            try:
                green.append(old.helpers.check_leaf(name, path, transfer))
            except (OSError, ValueError, KeyError) as error:
                diagnostics.append({"log": relative(path), "log_sha256": sha(path),
                    "status": "retained_diagnostic_not_release_evidence", "reason": str(error),
                    "recorded_exits": re.findall(r"^LEAN_EXIT=(\d+)\s*$", path.read_text(), re.M)})
        result.append({"target": name + ".lean", "status": "green" if green else "pending",
                       "runs": green, "retained_diagnostics": diagnostics})
    return result


def bootstrap():
    require(sha(INITIAL) == INITIAL_SHA, "initial import manifest changed")
    data = json.loads(INITIAL.read_text())
    require(data["research"] == BASE and data["pending_no_olean"] == [], "bootstrap pin changed")
    origin = data["origin"]
    require(origin["research"] == "ed41b2537e7dad15ce8055d9e5524e337ee8b9a4", "origin changed")
    require(sha(EX / origin["manifest_name"]) == origin["manifest_sha256"] and
            sha(RD / origin["receipt_name"]) == origin["receipt_sha256"] and
            sha(EX / "higher-y-prior-green-outputs.json") == origin["green_outputs_sha256"],
            "inherited receipts changed")
    require(sha(EX / "bootstrap_higher_y.py") == data["bootstrap"]["source_sha256"], "bootstrap source changed")
    repo = subprocess.check_output(["git", "-C", str(EX), "rev-parse", "--show-toplevel"], text=True).strip()
    sources = outputs = 0
    for entry in data["files"]:
        path = Path(entry["local"])
        require(sha(path) == entry["sha256"], "retained imported bytes changed: " + entry["module"])
        if entry["kind"] == "source":
            borrowed = entry["module"].startswith("AspisFormal.")
            revision = old.helpers.prior.BORROWED if borrowed else BASE
            name = ("AspisFormal/" if borrowed else "docs/research/v8-no-work-100-20260907/experiments/") + entry["overlay"]
            raw = subprocess.check_output(["git", "-C", repo, "show", revision + ":" + name])
            require(hashlib.sha256(raw).hexdigest() == entry["sha256"], "source/git mismatch: " + name)
            sources += 1
        else:
            outputs += 1
    require((sources, outputs) == (397, 397), "bootstrap artifact census changed")
    log = EX / "higher-y-bootstrap-preflight.log"
    raw = log.read_text()
    require(INITIAL_SHA in raw and "OVERLAY_PROVENANCE_PASS=794" in raw and "METADATA_EXIT=0" in raw,
            "successful metadata preflight absent")
    return {"status": "green", "manifest_sha256": INITIAL_SHA, "origin": origin,
            "pinned_source_blobs_checked": sources, "retained_compiled_artifacts_checked": outputs,
            "preflight_log_sha256": sha(log), "host_log_sha256": sha(EX / "higher-y-host-preflight.log"),
            "native_package_revisions": data["packages"],
            "scope": "Exact source/git/olean bytes and inherited proof evidence; native package cache is a pinned revision boundary, not replayed."}


def transport():
    path = EX / "selected-simple-root-rigidity-nuc-v1-transport.txt"
    text = path.read_text()
    require("exit 143" in text and "exit 255" in text and "NOT a Lean failure" in text,
            "transport-only record changed")
    require(not (EX / "selected-simple-root-rigidity-nuc-v1.log").exists(),
            "new v1 runner evidence needs independent reconciliation")
    return {"record": relative(path), "sha256": sha(path), "status": "transport_only_not_a_Lean_attempt",
            "stopped_local_ssh_exit": 143, "dns_probe_exit": 255,
            "observed_runner_or_lean_result": None,
            "future_ssh_endpoint": "dombarker@100.108.41.90",
            "future_ssh_options": ["BatchMode=yes", "ConnectTimeout=10", "StrictHostKeyChecking=yes", "HostKeyAlias=nuc.local"],
            "host_key_alias_only": True,
            "historical_network": "Bootstrap/generic and failed v1 SSH used the earlier local-DNS route. The user then required Tailscale; subsequent commands use the numeric Tailscale endpoint."}


def rust_control():
    source = EX / "quadratic_specialization_control.rs"
    expected = "0ca3312f6bbf472418328395fb2bf1b64cccd9f82e8a7aaaae1d3c7732197740"
    require(sha(source) == expected, "quadratic control source changed")
    rows = []
    for version in (1, 2):
        tag = "quadratic-control-nuc-v" + str(version)
        log, snapshot = EX / (tag + ".log"), EX / (tag + "-source.txt")
        text = log.read_text()
        require(BASE in text and expected in text and sha(snapshot) == expected, "Rust attempt source/pin changed")
        measurements = [] if version == 1 else old.helpers.prior.measurements(text)
        if version == 1:
            require("rustc: command not found" in text and not measurements, "v1 transport/PATH scope changed")
        else:
            require(len(measurements) == 2 and all(r["swaps"] == 0 for r in measurements), "Rust GNU resources absent")
            require(text.count("Exit status: 0") == 2 and "rustc --edition=2021 -O" in text,
                    "optimized successful compile/execute absent")
            require(all(p in text for p in ("MemoryHigh=1073741824", "MemoryMax=2147483648",
                    "MemorySwapMax=0", "CPUQuotaPerSecUSec=2s")), "Rust resource profile absent")
        rows.append({"log": relative(log), "log_sha256": sha(log), "source_snapshot_sha256": sha(snapshot),
            "status": "precompile_PATH_failure" if version == 1 else "restricted_control_pass",
            "measurements": measurements})
    result = json.loads(next(line for line in (EX / "quadratic-control-nuc-v2.log").read_text().splitlines()
                             if line.startswith('{"field_prime"')))
    require((result["restricted_families"], result["nonzero_resultant_families"],
        result["numeric_determinant_checks"], result["square_specializations_nonzero_resultant"],
        result["root_multiplicity_mass"], result["maximum_square_gammas"]) ==
        (15625, 15000, 78125, 17000, 40300, 3), "restricted Rust result changed")
    binary = EX / "target/higher-y-quadratic-control-nuc-v2.bin"
    retention = EX / "higher-y-quadratic-binary-retention.log"
    digest = "61951072b95b342a3afe93d803a76c56fb7d49c6dc921294b381344a011a8116"
    require(sha(binary) == digest and digest in retention.read_text(), "post-run binary retention changed")
    return {"source_sha256": expected, "current_runner_sha256": sha(EX / "run_quadratic_control_nuc.sh"),
        "attempts": rows, "result": result, "retained_binary": relative(binary), "retained_binary_sha256": digest,
        "binary_retention_log_sha256": sha(retention), "execution_time_binary_digest_recorded": False,
        "scope": "Post-run tagged binary retained at 08:11:24Z. Fixed F5 family control only; not a universal theorem, causal verifier or QM31 security experiment. No rerun performed by this auditor."}


def main():
    global FROZEN_LOGS
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prepare-receipt", action="store_true")
    parser.add_argument("--check-recorded", action="store_true")
    parser.add_argument("--check-checkpoint", action="store_true")
    args = parser.parse_args()
    if args.prepare_receipt:
        require(not args.check_recorded and not args.check_checkpoint, "receipt is not an evidence pass")
        data = old.inventory()
        print(json.dumps(data, indent=2))
        return int(bool(data["unmapped_artifacts"]))
    old.helpers.LEAVES = {n: (s, old.target_count(n, c)) for n, (s, c) in TARGETS.items()}
    receipt = old.helpers.prior.Transfer(RD / "higher-y-transfer.json")
    require(receipt.data is not None, "missing current receipt")
    retained = [RD / run["log"] for run in receipt.data["runs"]]
    if CENSUS_FINAL or args.check_checkpoint:
        require(set(retained) == set(logs()), "final receipt omits a discovered proof attempt")
    FROZEN_LOGS = retained
    data = {"schema": "aspis-v8-higher-y-evidence-v1", "parent_revision": BASE,
        "borrowed_formal_revision": old.helpers.prior.BORROWED,
        "mathlib_revision": old.helpers.prior.MATHLIB, "lean_commit": old.helpers.prior.LEAN,
        "auditor_sha256": sha(Path(__file__).resolve()), "target_census_final": CENSUS_FINAL,
        "read_only_helper_sha256": {name: sha(EX / name) for name in
            ("audit_symbolic_ood_evidence.py", "audit_component_cover_evidence.py",
             "audit_covered_family_evidence.py", "audit_quotient_family_evidence.py",
             "audit_off_family_tail_evidence.py")},
        "transfer_receipt_sha256": sha(receipt.path), "bootstrap": bootstrap(), "leaves": leaves(receipt),
        "retained_runs": inherited.inherited.retained_runs(receipt),
        "attempt_source_snapshots": inherited.source_snapshots(receipt),
        "transport_boundary": transport(), "restricted_rust_control": rust_control(),
        "native_import_inspection_sha256": sha(EX / "higher-y-native-imports-tailscale.log"),
        "global_accepted_extraction_bound": None, "remaining_global_allowance": None,
        "scope": "Only listed checked implications and restricted control evidence; no complete higher-Y coverage, sampler/FS, checked payment extraction, privacy or global numerical security result."}
    complete = CENSUS_FINAL and all(row["status"] == "green" for row in data["leaves"])
    checkpoint = [row for row in data["leaves"]
                  if row["target"].removesuffix(".lean") in CHECKPOINT_TARGETS]
    data["checkpoint"] = {"targets": list(CHECKPOINT_TARGETS),
        "expected_standard_axiom_audits": sum(TARGETS[name][1] for name in CHECKPOINT_TARGETS),
        "complete": all(row["status"] == "green" for row in checkpoint),
        "scope": "Listed focused leaves only; Sylvester and further nonsquare drafts are not part of this checkpoint."}
    data["status"] = "focused_evidence_complete_not_global_security" if complete else "pending"
    if args.check_checkpoint:
        require(not args.check_recorded, "select one check mode")
        require(data["checkpoint"]["complete"], "checkpoint leaf remains pending")
        require(json.loads((RD / "higher-y-evidence.json").read_text()) == data, "recorded checkpoint differs")
        print("Higher-Y seven-leaf/33-audit checkpoint matches; continuation and global security remain pending.")
        return 0
    elif args.check_recorded:
        require(complete, "target census/endpoint remains pending")
        require(json.loads((RD / "higher-y-evidence.json").read_text()) == data, "recorded evidence differs")
        print("Higher-Y focused evidence matches; global security remains unproved.")
    else:
        print(json.dumps(data, indent=2))
    return 0 if complete else 1


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, ValueError, KeyError, IndexError, AttributeError) as error:
        print("HIGHER_Y_EVIDENCE_REJECTED: " + str(error), file=sys.stderr)
        sys.exit(1)
