#!/usr/bin/env python3
"""Read-only f196 focused evidence audit; never builds or replays old leaves.

The five selected endpoints are an explicit census. Missing source, successful
log, imported artifact or standard-axiom audit leaves the result pending.
"""
import argparse
from fractions import Fraction
import hashlib
import json
from math import comb
from pathlib import Path
import re
import subprocess
import sys

import audit_quotient_family_evidence as helpers

EX, RD = helpers.EX, helpers.RD
BASE = "f19673b4fe72cf74ae687a926eeae9d1e5a6a52e"
ORIGIN = "bc23dfeb647320c4fbf09012cd92da1a6a5fa95a"
INITIAL = EX / "covered-family-initial-manifest.json"
INITIAL_SHA = "aec29d19e0277209a33e245c9434527dc9bf35c594b3f40bcce589998cdcec30"
TARGETS = {
    "CoveredFirstCollision": ("covered-first-collision", 6),
    "SelectedCoveredRelation": ("selected-covered-relation", 4),
    "CausalCoveredRecovery": ("causal-covered-recovery", 8),
    "SelectedWeightedCopyCore": ("selected-weighted-copy-core", 7),
    "SelectedWeightedCopyRows": ("selected-weighted-copy-rows", 5),
}
helpers.BASE = helpers.prior.BASE = BASE
require, sha, relative = helpers.require, helpers.sha, helpers.relative


def target_count(name, expected):
    path = EX / (name + ".lean")
    if expected is not None or not path.exists():
        return expected or 0
    # The log parser checks every literal current-source #print declaration;
    # no count alone is treated as proof that a requested theorem was checked.
    return len(re.findall(r"^#print axioms\s+([\w.]+)\s*$", path.read_text(), re.M))


def logs():
    paths = set()
    for stem, _ in TARGETS.values():
        paths.update(EX.glob(stem + "-nuc-*.log"))
    return sorted(paths)


def inventory():
    manifest = json.loads(INITIAL.read_text())
    artifacts, runs, missing = {}, [], []
    for path in logs():
        log = path.read_text()
        target = re.search(r"^TARGET=(.+)$", log, re.M)
        require(target and target.group(1) in TARGETS, "unexpected target log")
        for digest, raw in re.findall(r"^([a-f0-9]{64})  (.+)$", log, re.M):
            candidates = [EX / Path(raw).name, EX / (path.stem + "-source.txt"),
                          EX / (path.stem + "-runner.txt")]
            local = next((p for p in candidates if p.exists() and sha(p) == digest), None)
            if local is None:
                missing.append({"log": relative(path), "remote_path": raw, "sha256": digest})
            else:
                artifacts[(raw, digest)] = {"remote_path": raw, "local_path": relative(local), "sha256": digest}
        command = re.search(r"^COMMAND=(.+)$", log, re.M)
        def prop(name):
            match = re.search(r"^" + re.escape(name) + r"=(\d+)\s*$", log, re.M)
            return int(match.group(1)) if match else None
        runs.append({"target": target.group(1), "log": relative(path),
                     "command": command.group(1) if command else None,
                     "memory_high_bytes": prop("memory.high"), "memory_max_bytes": prop("memory.max"),
                     "memory_swap_max": prop("memory.swap.max")})
    for record in list(artifacts.values()):
        if not record["remote_path"].endswith("-manifest.json"):
            continue
        snapshot = json.loads((RD / record["local_path"]).read_text())
        task = record["remote_path"].rsplit("/", 1)[0]
        for item in snapshot["files"]:
            if item["category"] != "new_checked":
                continue
            raw = task + "/overlay/" + item["overlay"]
            key = (raw, item["sha256"])
            if key in artifacts:
                continue
            path = EX / Path(item["overlay"]).name
            if path.exists() and sha(path) == item["sha256"]:
                artifacts[key] = {"remote_path": raw, "local_path": relative(path), "sha256": item["sha256"]}
            else:
                missing.append({"manifest": record["local_path"], "remote_path": raw, "sha256": item["sha256"]})
    return {**{key: manifest[key] for key in ("research", "borrowed", "mathlib", "lean_commit")},
            "status": "retained_artifact_inventory_not_security_certificate",
            "manifest": {"path": relative(INITIAL), "sha256": sha(INITIAL)},
            "origin": manifest["origin"], "artifacts": list(artifacts.values()), "runs": runs,
            "unmapped_artifacts": missing}


def bootstrap():
    require(sha(INITIAL) == INITIAL_SHA, "initial manifest changed")
    manifest = json.loads(INITIAL.read_text())
    require(manifest["research"] == BASE and manifest["pending_no_olean"] == [], "new parent/baseline mismatch")
    origin = manifest["origin"]
    require(origin["research"] == ORIGIN, "prior origin confused with current parent")
    require(sha(EX / origin["manifest_name"]) == origin["manifest_sha256"], "prior import manifest changed")
    require(sha(EX / "covered-family-prior-green-outputs.json") == origin["green_outputs_sha256"], "prior green receipt changed")
    require(sha(EX / "bootstrap_covered_family.py") == manifest["bootstrap"]["source_sha256"], "bootstrap source changed")
    repo = subprocess.check_output(["git", "-C", str(EX), "rev-parse", "--show-toplevel"], text=True).strip()
    sources = outputs = 0
    for entry in manifest["files"]:
        if entry["kind"] == "source":
            borrowed = entry["module"].startswith("AspisFormal.")
            revision = helpers.prior.BORROWED if borrowed else BASE
            path = ("AspisFormal/" if borrowed else "docs/research/v8-no-work-100-20260907/experiments/") + entry["overlay"]
            blob = subprocess.check_output(["git", "-C", repo, "show", revision + ":" + path])
            require(hashlib.sha256(blob).hexdigest() == entry["sha256"], "pinned source mismatch: " + entry["module"])
            sources += 1
        else:
            require(sha(Path(entry["local"])) == entry["sha256"], "compiled artifact mismatch: " + entry["module"])
            outputs += 1
    log_path = EX / "covered-family-bootstrap-preflight.log"
    log = log_path.read_text()
    require("METADATA_EXIT=0" in log and "OVERLAY_PROVENANCE_PASS=" + str(len(manifest["files"])) in log and
            INITIAL_SHA in log, "missing remote bootstrap preflight")
    return {"status": "green", "manifest_sha256": INITIAL_SHA, "pinned_source_blobs_checked": sources,
            "retained_compiled_artifacts_checked": outputs, "origin": origin,
            "remote_metadata_log_sha256": sha(log_path), "native_package_revisions": manifest["packages"],
            "boundary": "Inherited source-to-olean evidence plus exact pinned sources/compiled bytes. Native package cache is pinned but not compiler-reproduced or package-replayed."}


def arithmetic():
    path, script = RD / "covered-relation-ledger.json", EX / "covered_relation_ledger.py"
    ledger = json.loads(path.read_text())
    k, T, q = (2**31 - 1)**4, 262144, 22
    beta = lambda m: Fraction(comb(m, q), comb(T, q))
    outside = beta(9557) + Fraction(9396508281246, k) * beta(117964) + Fraction(127, k)
    first = 99 * (Fraction(3, k - 1) + Fraction(6, k))
    suffix = Fraction(q, k - 1) + Fraction(18, k)
    def rational(record):
        return Fraction(int(record["numerator"]), int(record["denominator"]))
    require(ledger["parent_revision"] == BASE and ledger["theorem"] ==
            "SelectedCoveredRelation.no_good_quotient_bound", "wrong arithmetic event/parent")
    require((int(ledger["field_size"]), ledger["queries"], ledger["fibres"], ledger["family_cap"])
            == (k, q, T, 99), "ledger parameter mismatch")
    require([term["name"] for term in ledger["terms"]] ==
            ["off_family_pointwise_moment", "represented_bad_first_collision", "single_actual_suffix"],
            "ledger event precedence changed")
    require([rational(term["value"]) for term in ledger["terms"]] == [outside, first, suffix],
            "term rational mismatch or duplicated query-family factor")
    total = outside + first + suffix
    require(rational(ledger["joint_bound"]) == total and total < Fraction(1, 2**100),
            "local exact subtotal mismatch")
    require(total == beta(9557) + Fraction(9396508281246, k) * beta(117964) +
            Fraction(319, k - 1) + Fraction(739, k), "independent collected coefficient check failed")
    require(ledger["remaining_accepted_good_quotient_mass"] is None and
            ledger["global_accepted_payment_extraction_upper_bound"] is None and
            ledger["global_remaining_numerical_allowance"] is None, "unsupported global bound promoted")
    require((ledger["proof_body_bytes"], ledger["new_verifier_operations"], ledger["new_proof_bytes"],
             ledger["grinding_security_credit"], ledger["new_complete_transaction_CU"])
            == (40282, 0, 0, 0, None), "cost/work contract changed")
    require(697 * 16 + 52 + 24 + q * 621 + 2 * 296 * 26 == 40282, "body census mismatch")
    return {"status": "green", "ledger_sha256": sha(path), "script_sha256": sha(script),
            "event": ledger["event"], "joint_bound": ledger["joint_bound"],
            "scope": "Exact arithmetic for the no-good-quotient ideal event; numerical correctness is separate from the five current-source theorem checks and does not bound accepted payment-extraction failure."}


def weighted_source_metadata():
    """Tiny static table/definition check, not a Rust-to-Lean translation."""
    repo = subprocess.check_output(["git", "-C", str(EX), "rev-parse", "--show-toplevel"], text=True).strip()
    sources = {}
    for revision, path, expected in (
        (BASE, "crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal_constants.rs",
         "cfce7ec499d3cfd54cf91eb88675e45d89ada5ce073fe00c78be5211204fbc50"),
        (BASE, "crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs",
         "50062fff8b6afbffad3ddbb8eda09992353a9171c4955151cece26a654c6a6d5"),
        (helpers.prior.BORROWED, "AspisFormal/AspisFormal/Pool/NativePaymentCompiledCopyLogUpV1.lean",
         "86b10589ca637514f0eb772a0bb29e9da28304c50f7aa1627bccf2ddbed1993f")):
        raw = subprocess.check_output(["git", "-C", repo, "show", revision + ":" + path])
        require(hashlib.sha256(raw).hexdigest() == expected, "weighted-copy pinned source changed: " + path)
        sources[path] = {"revision": revision, "sha256": expected, "text": raw.decode()}
    constants = sources["crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal_constants.rs"]["text"]
    rows = (EX / "SelectedWeightedCopyRows.lean").read_text()
    rust_masks = re.search(r"ACTIVE_ROW_MASKS: \[u16; 64\] = \[([^]]+)\]", constants)
    lean_masks = re.search(r"def activeMasks : List Nat := \[([^]]+)\]", rows)
    require(rust_masks and lean_masks, "literal mask array missing")
    masks = [int(n) for n in re.findall(r"\d+", rust_masks.group(1))]
    require(masks == [int(n) for n in re.findall(r"\d+", lean_masks.group(1))] and len(masks) == 64,
            "source/Lean64-mask mismatch")
    normalize = lambda text: re.sub(r"\s+", "", text)
    actual_kind = rows.split("def selectedKind", 1)[1].split("def selectedTag", 1)[0]
    expected_kind = """(index : Fin 136) : WeightKind :=
      if index.val = 3 ∨ index.val = 4 ∨ index.val = 12 ∨
          index.val = 20 ∨ index.val = 21 then .transfer
      else if index.val = 22 then .withdrawal
      else if 24 ≤ index.val ∧ index.val < 64 then
        if index.val % 2 = 0 then .appendLeft ((index.val - 24) / 2)
        else .appendRight ((index.val - 24) / 2)
      else .one"""
    require(normalize(actual_kind) == normalize(expected_kind), "audited literal weight decision changed")
    actual_tag = rows.split("def selectedTag", 1)[1].split("theorem selectedTag_injective", 1)[0]
    require(normalize(actual_tag) == normalize("(index : Fin 136) : Nat := 1124073472 + index.val"),
            "audited literal tag expression changed")
    actual_row = rows.split("def rowActive", 1)[1].split("instance rowActive_decidable", 1)[0]
    require(normalize(actual_row) == normalize("""(row : Fin 1024) : Prop :=
      ((activeMasks.getD (row.val / 16) 0).testBit (row.val % 16)) = true"""),
      "audited row/block/bit order changed")
    links = [tuple(map(int, values)) for values in re.findall(
        r"CompiledPoolV1PairForestLink \{ tag: (\d+), weight_kind: (\d+), weight_level: (\d+),", constants)]
    require(len(links) == 136, "source136-link metadata census changed")
    for i, actual in enumerate(links):
        kind = 1 if i in {3, 4, 12, 20, 21} else 2 if i == 22 else 3 + i % 2 if 24 <= i < 64 else 0
        level = (i - 24) // 2 if 24 <= i < 64 else 0
        require(actual == (1124073472 + i, kind, level), "source/Lean weight/tag mismatch at " + str(i))
    require(sum(mask.bit_count() for mask in masks) == 214, "active-row census changed")
    return {"status": "green", "pinned_sources": {name: {k: v for k, v in item.items() if k != "text"}
            for name, item in sources.items()}, "mask_entries": 64, "active_rows": 214,
            "link_weight_tag_entries": 136, "append_pairs": 20,
            "scope": "Static64-mask and136 weight/tag/level comparison against the exact selected Lean definitions. No endpoint/pattern placement, Rust execution refinement, off-domain evaluator, alias or payment implication is inferred."}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prepare-receipt", action="store_true")
    parser.add_argument("--check-recorded", action="store_true")
    args = parser.parse_args()
    if args.prepare_receipt:
        require(not args.check_recorded, "receipt generation is not an evidence pass")
        data = inventory()
        print(json.dumps(data, indent=2))
        return 1 if data["unmapped_artifacts"] else 0
    helpers.LEAVES = {name: (stem, target_count(name, count)) for name, (stem, count) in TARGETS.items()}
    transfer = helpers.prior.Transfer(RD / "covered-family-transfer.json")
    require(transfer.data is not None, "missing new-turn transfer receipt")
    output = {"schema": "aspis-v8-covered-family-evidence-v1", "parent_revision": BASE,
              "borrowed_formal_revision": helpers.prior.BORROWED, "mathlib_revision": helpers.prior.MATHLIB,
              "lean_commit": helpers.prior.LEAN, "auditor_sha256": sha(Path(__file__).resolve()),
              "read_only_helper_sha256": {name: sha(EX / name) for name in
                  ("audit_quotient_family_evidence.py", "audit_off_family_tail_evidence.py")},
              "transfer_receipt_sha256": sha(transfer.path), "bootstrap": bootstrap(),
              "leaves": helpers.leaves(transfer), "exact_arithmetic": arithmetic(),
              "weighted_source_metadata": weighted_source_metadata(),
              "proof_body_bytes": 40282, "positive_work_credit": 0,
              "global_accepted_extraction_bound": None, "remaining_global_allowance": None,
              "scope": "Focused ideal-game and deterministic row algebra only. No actual-verifier witness extractor, authenticated replay, full-view privacy, resource-bounded Fiat–Shamir or CU-parity theorem."}
    complete = all(row["status"] == "green" for row in output["leaves"])
    output["status"] = "focused_evidence_complete_not_global_security" if complete else "pending"
    if args.check_recorded:
        require(complete, "pending endpoint: refusing recorded-evidence success")
        require(json.loads((RD / "covered-family-evidence.json").read_text()) == output, "recorded evidence changed")
        print("Covered-family focused evidence matches; global security remains unproved.")
    else:
        print(json.dumps(output, indent=2))
    return 0 if complete else 1


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, ValueError, KeyError) as error:
        print("COVERED_FAMILY_EVIDENCE_REJECTED: " + str(error), file=sys.stderr)
        sys.exit(1)
