#!/usr/bin/env python3
"""Read-only sampler checkpoint metadata; no compiler or actual sampler replay."""
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
BASE = "ce36c58168987142d3f07e5d8cba00fb7b1dd05b"
RUN_PARENT = "289d7356c78a4cd493fe61a54f9548f2a0c11298"
CENSUS_FINAL = True  # Four-leaf checkpoint only; no actual sampler law credit.
TARGETS = {
    "SecureCircleParameterDomain": ("secure-circle-parameter-domain", 9),
    "DistinctCircleDecoder": ("distinct-circle-decoder", 4),
    "BoundedRetryKernel": ("bounded-retry-kernel", 4),
    "SecureCircleParameterInverse": ("secure-circle-parameter-inverse", 16),
}
spec = importlib.util.spec_from_file_location("quadratic_causal", EX / "quadratic-causal-audit.py")
previous = importlib.util.module_from_spec(spec)
spec.loader.exec_module(previous)
checkpoint, old = previous.checkpoint, previous.old
require, sha, relative = old.require, old.sha, old.relative
checkpoint.TARGETS = old.TARGETS = TARGETS
old.helpers.LEAVES = TARGETS
RECEIPT = RD / "secure-circle-sampler-transfer.json"
RECORD = RD / "secure-circle-sampler-evidence.json"
FROZEN = (
    ("experiments/quadratic-causal-audit.py", "e0e885037015367546ba641de36b6cc819118bceb6084af405c60581e0271c21"),
    ("quadratic-causal-evidence.json", "1d52867f247b8fc404a313eb89d8e01a1a1c640e0bcaaa2717ee7617604e9a43"),
    ("quadratic-causal-transfer.json", "b8a2514413ddb0754027095818bc2a05dd47f8c3b4b70e9eda5ad469b43e6084"),
    ("quadratic-causal-build-evidence.md", "eacda0b5d45480426c16ffbc064da83b0cd7e0ade3576eb9b3b374aafaeb4aa9"),
)


def committed_bytes(path, expected):
    require(sha(path) == expected, "frozen causal bytes changed: " + path.name)
    name = "docs/research/v8-no-work-100-20260907/" + str(path.relative_to(RD))
    blob = subprocess.check_output(["git", "-C", str(EX), "show", BASE + ":" + name])
    require(hashlib.sha256(blob).hexdigest() == expected, "inherited source/git mismatch: " + name)


def inherited_causal():
    for name, digest in FROZEN:
        committed_bytes(RD / name, digest)
    data = json.loads((RD / "quadratic-causal-evidence.json").read_text())
    require(data["parent_revision"] == previous.BASE and data["target_census_final"] is True and
            data["status"] == "quadratic_causal_checkpoint_complete_not_global_security",
            "inherited causal identity/status changed")
    require(len(data["leaves"]) == 2 and
            sum(len(row["runs"][0]["axiom_audits"]) for row in data["leaves"]) == 6,
            "inherited causal census changed")
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
    return {"status": "inherited_causal_bytes_verified", "commit": BASE,
            "recorded_standard_axiom_audits": 6, "new_axiom_credit": 0,
            "immutable_records": [{"path": name, "sha256": digest} for name, digest in FROZEN],
            "source_output_pairs": pairs, "scope": "Byte/source-origin audit, not a theorem-suite replay."}


def inventory():
    data = previous.inventory()
    data["continuation_parent_revision"] = BASE
    data["inherited_causal_parent_revision"] = previous.BASE
    data["inherited_causal_receipt_sha256"] = FROZEN[2][1]
    return data


def reused_codec_bodies():
    borrowed = old.helpers.prior.BORROWED
    path = "AspisFormal/AspisFormal/K1/V7Tag73SemanticTranscriptBridge.lean"
    raw = subprocess.check_output(["git", "-C", str(EX), "show", borrowed + ":" + path])
    require(hashlib.sha256(raw).hexdigest() ==
            "91ada7d79b858d045eacb57a4b8a34b5e01594800f8829fea0888b4820c3f189",
            "borrowed codec proof source changed")
    selected = (EX / "SecureCircleParameterInverse.lean").read_text()
    names = ("encodeWordLE_decodeWordLE", "encodeQM31LE_of_decodeQM31LE",
             "encodeTagQM31ExactLE_of_decode", "decodeTagQM31ExactLE_injective_on_success")
    def declaration(text, name):
        pattern = r"theorem " + re.escape(name) + r"\b.*?(?=\n(?:/--|theorem |end Codec))"
        found = re.search(pattern, text, re.S)
        require(found is not None, "missing reused codec declaration: " + name)
        return " ".join(found.group(0).split())
    for name in names:
        require(declaration(raw.decode(), name) == declaration(selected, name),
                "reused codec theorem differs: " + name)
    return {"borrowed_revision": borrowed, "source_path": path,
            "source_sha256": hashlib.sha256(raw).hexdigest(),
            "identical_declarations_modulo_whitespace": list(names),
            "whole_semantic_module_imported": False}


def scope_documents():
    ledger = RD / "secure-circle-open-ledger.json"
    data = json.loads(ledger.read_text())
    require(data["source_parent"] == BASE and data["maximum_proof_body_bytes"] == 40282 and
            data["grinding_security_credit_bits"] == 0, "sampler ledger scope changed")
    require(all(data[key] is None for key in
                ("full_raw_error", "full_fiat_shamir_advantage", "remaining_global_allowance")),
            "unproved global sampler charge entered ledger")
    names = ("secure-circle-open-ledger.json", "secure-circle-parameter-domain-review.md",
             "secure-circle-retry-review.md", "secure-circle-parameter-inverse-review.md",
             "sampler-ordinary-law-interface.md", "secure-circle-sampler-cache-preflight.json")
    return {"files": [{"path": name, "sha256": sha(RD / name)} for name in names],
            "scope": "Documentation and cache inspection only, not extra theorem or probability credit."}


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
            transfer.data.get("inherited_causal_receipt_sha256") == FROZEN[2][1],
            "secure-circle sampler receipt pins changed")
    discovered = set(checkpoint.logs())
    retained = [RD / row["log"] for row in transfer.data["runs"]]
    if CENSUS_FINAL or args.check_snapshot:
        require(set(retained) == discovered, "sampler receipt omits a discovered attempt")
    checkpoint.FROZEN_LOGS = retained
    result = {
        "schema": "aspis-v8-secure-circle-sampler-evidence-v1",
        "parent_revision": BASE, "executed_runner_research_pin": RUN_PARENT,
        "borrowed_formal_revision": old.helpers.prior.BORROWED,
        "lean_commit": old.helpers.prior.LEAN, "mathlib_revision": old.helpers.prior.MATHLIB,
        "auditor_sha256": sha(Path(__file__).resolve()),
        "read_only_helper_sha256": {name: sha(EX / name) for name in
            ("quadratic-causal-audit.py", "quadratic-selected-family-audit.py",
             "quadratic-source-bridge-audit.py", "higher-y-extension-audit.py", "higher-y-audit.py",
             "audit_symbolic_ood_evidence.py", "audit_component_cover_evidence.py",
             "audit_covered_family_evidence.py", "audit_quotient_family_evidence.py",
             "audit_off_family_tail_evidence.py")},
        "target_census_final": CENSUS_FINAL, "checkpoint_only": True,
        "full_soundness_task_complete": False, "transfer_receipt_sha256": sha(RECEIPT),
        "inherited_causal": inherited_causal(),
        "inherited_selected_family": previous.inherited_selected_family(),
        "inherited_source_bridge": previous.previous.inherited_source_bridge(),
        "inherited_extension": previous.previous.previous.inherited_extension(),
        "inherited_seven_leaf_checkpoint": previous.previous.previous.previous.inherited_checkpoint(),
        "original_bootstrap": checkpoint.bootstrap(),
        "leaves": checkpoint.leaves(transfer),
        "retained_runs": checkpoint.inherited.inherited.retained_runs(transfer),
        "attempt_source_snapshots": checkpoint.inherited.source_snapshots(transfer),
        "all_attempt_resource_contracts": previous.previous.previous.previous.attempt_contract(),
        "reused_codec_proof_bodies": reused_codec_bodies(),
        "scope_documents": scope_documents(),
        "network": {"endpoint": "dombarker@100.108.41.90", "transport": "Tailscale",
                    "host_key_alias": "nuc.local", "host_key_alias_is_network_endpoint": False},
        "actual_tape_sampler_law_proved": False,
        "conditional_retry_kernel": "Requires the same one-step hit and successful-rejection masses at every history; None aborts immediately.",
        "excluded_non_theorem_work": ["read-only SemanticTranscriptBridge cache preflight"],
        "global_error_bound": None, "remaining_global_allowance": None,
        "scope": "Exact secure-circle domain/inverse algebra, deterministic distinct-point decoder control flow, and a conditional history-dependent retry-mass recursion. No actual raw-tape/source sampling law, fresh-oracle coupling, joint distinct-point distribution or new global OOD probability bound."
    }
    complete = CENSUS_FINAL and all(row["status"] == "green" for row in result["leaves"])
    result["status"] = "secure_circle_sampler_checkpoint_complete_not_source_probability" if complete else "pending"
    if args.check_recorded or args.check_snapshot:
        if args.check_recorded:
            require(complete, "sampler checkpoint leaf remains pending")
        require(json.loads(RECORD.read_text()) == result, "recorded sampler evidence differs")
        print("Secure-circle sampler evidence matches; actual tape/source sampling and full soundness remain open.")
        return 0
    print(json.dumps(result, indent=2))
    return 0 if complete else 1


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, ValueError, KeyError, IndexError, AttributeError) as error:
        print("SECURE_CIRCLE_SAMPLER_EVIDENCE_REJECTED: " + str(error), file=sys.stderr)
        sys.exit(1)
