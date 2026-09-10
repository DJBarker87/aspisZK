#!/usr/bin/env python3
"""Read-only ordinary-mass checkpoint audit; no compiler, remote call or old replay."""
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
BASE = "15700387af1d52af4b7ddff8de92541ec2891ff2"
RUN_PARENT = "289d7356c78a4cd493fe61a54f9548f2a0c11298"
CENSUS_FINAL = True  # Four-leaf checkpoint, not the complete nested tape law.
TARGETS = {
    "FiniteOptionMass": ("finite-option-mass", 2),
    "OrdinaryRawMass": ("ordinary-raw-mass", 6),
    "OrdinaryPrefixMass": ("ordinary-prefix-mass", 6),
    "NestedCircleRouting": ("nested-circle-routing", 10),
}
spec = importlib.util.spec_from_file_location("secure_circle_sampler", EX / "secure-circle-sampler-audit.py")
previous = importlib.util.module_from_spec(spec)
spec.loader.exec_module(previous)
checkpoint, old = previous.checkpoint, previous.old
require, sha, relative = old.require, old.sha, old.relative
checkpoint.TARGETS = old.TARGETS = TARGETS
old.helpers.LEAVES = TARGETS
RECEIPT = RD / "ordinary-mass-transfer.json"
RECORD = RD / "ordinary-mass-evidence.json"
FROZEN = (
    ("experiments/secure-circle-sampler-audit.py", "2c19e92b9cc6d89e780f1128e974573b2ee8483a745379f89dc11df0803c6ba5"),
    ("secure-circle-sampler-evidence.json", "449e3b2f13d939ada15bfe80f10fc648140df7147fbd36f50ebf001d3686497c"),
    ("secure-circle-sampler-transfer.json", "d1cef28ddc207014b11a953b83b153606bcbe39aca1b368008f32e9bbf6be238"),
    ("secure-circle-sampler-build-evidence.md", "61a86fda3180d8eb8e6653ec41db66af8b2b839d4cbd4a4806592a5d1c584a49"),
)


def committed_bytes(path, expected):
    require(sha(path) == expected, "frozen sampler bytes changed: " + path.name)
    name = "docs/research/v8-no-work-100-20260907/" + str(path.relative_to(RD))
    blob = subprocess.check_output(["git", "-C", str(EX), "show", BASE + ":" + name])
    require(hashlib.sha256(blob).hexdigest() == expected, "inherited source/git mismatch: " + name)


def inherited_sampler():
    for name, digest in FROZEN:
        committed_bytes(RD / name, digest)
    data = json.loads((RD / "secure-circle-sampler-evidence.json").read_text())
    require(data["parent_revision"] == previous.BASE and data["target_census_final"] is True and
            data["status"] == "secure_circle_sampler_checkpoint_complete_not_source_probability",
            "inherited sampler identity/status changed")
    require(len(data["leaves"]) == 4 and
            sum(len(row["runs"][0]["axiom_audits"]) for row in data["leaves"]) == 33,
            "inherited sampler census changed")
    pairs = []
    for row in data["leaves"]:
        require(row["status"] == "green" and len(row["runs"]) == 1, "ambiguous inherited result")
        run = row["runs"][0]
        source = EX / row["target"]
        committed_bytes(source, run["source_sha256"])
        require(sha(source.with_suffix(".olean")) == run["olean_sha256"],
                "inherited sampler output changed: " + source.stem)
        pairs.append({"source": relative(source), "source_sha256": run["source_sha256"],
                      "olean_sha256": run["olean_sha256"]})
    return {"status": "inherited_sampler_bytes_verified", "commit": BASE,
            "recorded_standard_axiom_audits": 33, "new_axiom_credit": 0,
            "immutable_records": [{"path": name, "sha256": digest} for name, digest in FROZEN],
            "source_output_pairs": pairs, "scope": "Byte/source-origin audit, not a theorem-suite replay."}


def inventory():
    data = previous.inventory()
    data["continuation_parent_revision"] = BASE
    data["inherited_sampler_parent_revision"] = previous.BASE
    data["inherited_sampler_receipt_sha256"] = FROZEN[2][1]
    return data


def cache_appends():
    rows = []
    for name, pairs in (("raw", 2), ("decoder", 1)):
        script = EX / ("audit_ordinary_" + name + "_cache.py")
        checked = subprocess.run([sys.executable, str(script)], capture_output=True, text=True)
        require(checked.returncode == 0, "cache append audit failed: " + checked.stdout + checked.stderr)
        receipt = RD / ("ordinary-" + name + "-cache-append.json")
        value = json.loads(receipt.read_text())
        require(value["source_parent"] == BASE and value["compiler_launched"] is False,
                "cache append scope changed")
        rows.append({"receipt": relative(receipt), "receipt_sha256": sha(receipt),
                     "auditor": relative(script), "auditor_sha256": sha(script),
                     "audit_output": checked.stdout.strip(), "local_source_output_pairs": pairs,
                     "new_axiom_credit": 0})
    return rows


def scope_documents():
    ledger = RD / "ordinary-mass-ledger.json"
    data = json.loads(ledger.read_text())
    require(data["source_parent"] == BASE and data["maximum_proof_body_bytes"] == 40282 and
            data["grinding_security_credit_bits"] == 0, "ordinary ledger scope changed")
    require(all(data[key] is None for key in
                ("full_raw_error", "full_fiat_shamir_advantage", "remaining_global_allowance")),
            "unproved global charge entered ledger")
    require(all(data["composition"][key] is None for key in
                ("nested_decoder_mass", "adaptive_ood_pair_law", "source_fiat_shamir_coupling")),
            "unproved nested/source law entered ledger")
    require(data["ordinary_raw_law"]["status"] == "kernel_checked" and
            data["ordinary_raw_law"]["p"] == 2147483647 and
            data["composition"]["one_call_block_law"].startswith("kernel_checked OrdinaryPrefixMass"),
            "ordinary finite-coin endpoint changed")
    names = ("ordinary-mass-ledger.json", "ordinary-mass-review.md", "nested-circle-routing-review.md",
             "ordinary-raw-cache-review.md", "ordinary-decoder-cache-review.md")
    return {"files": [{"path": name, "sha256": sha(RD / name)} for name in names],
            "scope": "Scoped proof/cache documentation; no extra theorem or global probability credit."}


def source_contracts():
    imports = {
        "FiniteOptionMass": ["BoundedRetryKernel"],
        "OrdinaryRawMass": ["AspisFormal.K1.V7Tag73EightRetrySamplerLaw", "FiniteOptionMass"],
        "OrdinaryPrefixMass": ["OrdinaryRawMass", "AspisFormal.K1.V7Tag73EightRetryDecoderBridge",
                               "AspisFormal.K1.V7Tag73SamplerExactValue"],
        "NestedCircleRouting": ["DistinctCircleDecoder"],
    }
    result = []
    for target, (_, count) in TARGETS.items():
        source = EX / (target + ".lean")
        text = source.read_text()
        expected_heartbeats = 250000 if target == "OrdinaryPrefixMass" else 200000
        require(re.findall(r"^import (.+)$", text, re.M) == imports[target], "unexpected import expansion")
        require(not re.search(r"\b(sorry|admit|native_decide)\b|^axiom\s", text, re.M),
                "unproved source declaration: " + target)
        declarations = re.findall(r"^#print axioms ([\w.]+)$", text, re.M)
        require(len(declarations) == count, "current audit declaration census changed")
        for path in [source] + [EX / (log.stem + "-source.txt") for log in checkpoint.target_logs(target)]:
            attempted = path.read_text()
            require(re.findall(r"set_option maxRecDepth (\d+)", attempted) == ["200"] and
                    re.findall(r"set_option maxHeartbeats (\d+)", attempted) == [str(expected_heartbeats)],
                    "attempt changed the declared symbolic proof budget: " + path.name)
        result.append({"target": target, "source_sha256": sha(source), "imports": imports[target],
                       "max_rec_depth": 200, "max_heartbeats": expected_heartbeats,
                       "axiom_declarations": declarations})
    return {"status": "exact_imports_and_unchanged_attempt_budgets_verified", "targets": result,
            "scope": "The Prefix leaf declared 250000 heartbeats before its first attempt; other leaves declared 200000. No failure retry raised either limit."}


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
            transfer.data.get("inherited_sampler_receipt_sha256") == FROZEN[2][1],
            "ordinary-mass receipt pins changed")
    discovered = set(checkpoint.logs())
    retained = [RD / row["log"] for row in transfer.data["runs"]]
    if CENSUS_FINAL or args.check_snapshot:
        require(set(retained) == discovered, "ordinary receipt omits a discovered attempt")
    checkpoint.FROZEN_LOGS = retained
    result = {
        "schema": "aspis-v8-ordinary-mass-evidence-v1",
        "parent_revision": BASE, "executed_runner_research_pin": RUN_PARENT,
        "borrowed_formal_revision": old.helpers.prior.BORROWED,
        "lean_commit": old.helpers.prior.LEAN, "mathlib_revision": old.helpers.prior.MATHLIB,
        "auditor_sha256": sha(Path(__file__).resolve()),
        "read_only_helper_sha256": {name: sha(EX / name) for name in
            ("secure-circle-sampler-audit.py", "quadratic-causal-audit.py",
             "quadratic-selected-family-audit.py", "quadratic-source-bridge-audit.py",
             "higher-y-extension-audit.py", "higher-y-audit.py", "audit_symbolic_ood_evidence.py",
             "audit_component_cover_evidence.py", "audit_covered_family_evidence.py",
             "audit_quotient_family_evidence.py", "audit_off_family_tail_evidence.py")},
        "target_census_final": CENSUS_FINAL, "checkpoint_only": True,
        "full_soundness_task_complete": False, "transfer_receipt_sha256": sha(RECEIPT),
        "inherited_sampler": inherited_sampler(),
        "inherited_causal": previous.inherited_causal(),
        "inherited_selected_family": previous.previous.inherited_selected_family(),
        "inherited_source_bridge": previous.previous.previous.inherited_source_bridge(),
        "inherited_extension": previous.previous.previous.previous.inherited_extension(),
        "inherited_seven_leaf_checkpoint": previous.previous.previous.previous.previous.inherited_checkpoint(),
        "original_bootstrap": checkpoint.bootstrap(),
        "verified_cache_appends": cache_appends(),
        "leaves": checkpoint.leaves(transfer),
        "retained_runs": checkpoint.inherited.inherited.retained_runs(transfer),
        "attempt_source_snapshots": checkpoint.inherited.source_snapshots(transfer),
        "all_attempt_resource_contracts": previous.previous.previous.previous.previous.attempt_contract(),
        "source_contracts": source_contracts(),
        "scope_documents": scope_documents(),
        "network": {"endpoint": "dombarker@100.108.41.90", "transport": "Tailscale",
                    "host_key_alias": "nuc.local", "host_key_alias_is_network_endpoint": False},
        "actual_nested_tape_sampler_law_proved": False,
        "global_error_bound": None, "remaining_global_allowance": None,
        "scope": "Scoped finite one-call unconditional value mass and deterministic decoder/routing prerequisites. Aborts stay in the sample space. No full nested routing equivalence, adaptive OOD pair law, source/Fiat-Shamir coupling, payment extraction or privacy theorem."
    }
    complete = CENSUS_FINAL and all(row["status"] == "green" for row in result["leaves"])
    contracts = result["all_attempt_resource_contracts"]
    result["census"] = {
        "targets": len(result["leaves"]), "attempts": len(contracts),
        "successful_attempts": sum(row["exit"] == 0 for row in contracts),
        "failed_attempts": sum(row["exit"] != 0 for row in contracts),
        "standard_axiom_audits": sum(len(run["axiom_audits"]) for leaf in result["leaves"] for run in leaf["runs"]),
    }
    if complete:
        require(result["census"] == {"targets": 4, "attempts": 8, "successful_attempts": 4,
                                     "failed_attempts": 4, "standard_axiom_audits": 24},
                "final ordinary checkpoint census differs from retained attempts")
    result["status"] = "ordinary_mass_checkpoint_complete_not_nested_source_law" if complete else "pending"
    if args.check_recorded or args.check_snapshot:
        if args.check_recorded:
            require(complete, "ordinary checkpoint leaf or census remains pending")
        require(json.loads(RECORD.read_text()) == result, "recorded ordinary-mass evidence differs")
        print("Ordinary-mass evidence matches; nested tape/source coupling and full soundness remain open.")
        return 0
    print(json.dumps(result, indent=2))
    return 0 if complete else 1


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, ValueError, KeyError, IndexError, AttributeError) as error:
        print("ORDINARY_MASS_EVIDENCE_REJECTED: " + str(error), file=sys.stderr)
        sys.exit(1)
