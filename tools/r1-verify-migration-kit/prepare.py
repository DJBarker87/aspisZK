#!/usr/bin/env python3
"""Exact-source, test-only actual S2 overlay for verify/round refactors.

This writes only a separately staged crate snapshot. Synthetic interface
errors are explicitly distinguished from production-reachable errors.
"""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
SOURCE = "crates/aspis-r1-cost-probe/src/r1_semantic.rs"
BEFORE = "deb68369ba3ad7cc6706dc24b6503fac1cbe942b"
CFG = '#[cfg(all(test, feature="prover", feature="private-leaf-salts"))]'
sha = lambda b: hashlib.sha256(b).hexdigest()


def git(rev, path):
    return subprocess.check_output(["git", "-C", str(ROOT), "show", rev + ":" + path])


def declaration(raw, anchor):
    spec = importlib.util.spec_from_file_location("source_lexer", ROOT /
        "docs/research/100bit-spend-path-20261013/tools/j1e-source-effect-audit.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module.fragment(raw, anchor)[0].encode()


def instrument(body):
    replacements = [
        (b"Prefix::parse(bytes)?", b"verify_migration_tests::parse(bytes)?"),
        (b"public_transcript(public, hash, prefix.c1_root)?",
         b"verify_migration_tests::public_transcript(public, hash, prefix.c1_root)?"),
        (b"wire::begin(&prefix, &mut transcript)?",
         b"verify_migration_tests::begin(&prefix, &mut transcript)?"),
        (b"prefix.validated_record(14)?.decode_k::<1>(0)?[0]",
         b"verify_migration_tests::decode::<1>(&prefix, 14, 0)?[0]"),
        (b"prefix.validated_record(row)?.decode_k::<28>(0)?",
         b"verify_migration_tests::decode::<28>(&prefix, row, 0)?"),
        (b"transcript.semantic_validated(prefix.validated_record(row)?)?",
         b"verify_migration_tests::semantic_validated(&mut transcript, verify_migration_tests::lookup(&prefix, row)?)?"),
    ]
    counts = []
    for old, new in replacements:
        count = body.count(old)
        body = body.replace(old, new)
        counts.append(count)
    return body, counts


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--after", required=True)
    ap.add_argument("--stage", type=Path)
    ap.add_argument("--check", action="store_true")
    args = ap.parse_args()
    after = subprocess.check_output(["git", "-C", str(ROOT), "rev-parse", args.after], text=True).strip()
    old_source, new_source = git(BEFORE, SOURCE), git(after, SOURCE)
    old = declaration(old_source, "pub fn verify_observed<")
    new = declaration(new_source, "pub fn verify_observed<")
    finish = declaration(new_source, "fn verify_finish<")
    old_instrumented, old_counts = instrument(old)
    new_instrumented, new_counts = instrument(new)
    finish_instrumented, finish_counts = instrument(finish)
    _, all_counts = instrument(new_source)
    assert old_counts == [1, 1, 1, 1, 1, 1], old_counts
    assert new_counts == [1, 1, 1, 0, 0, 0], new_counts
    assert finish_counts[:3] == [0, 0, 0]
    assert all_counts[:3] == [1, 1, 1]
    assert all_counts[3:] in [[1, 1, 1], [1, 10, 10], [2, 20, 20], [2, 2, 2]], all_counts
    old_instrumented = old_instrumented.replace(b"pub fn verify_observed<", b"fn migration_old_verify_observed<", 1)
    overlay, _ = instrument(new_source)
    assert overlay != new_source
    overlay += ("\n" + CFG + "\n").encode() + old_instrumented + ("\n" + CFG +
        '\n#[path="verify_migration_tests.rs"]\nmod verify_migration_tests;\n').encode()
    harness = (HERE / "real-fixture.rs").read_bytes()
    files = {SOURCE: overlay,
        "crates/aspis-r1-cost-probe/src/verify_migration_tests.rs": harness}
    pins = {"before_revision": BEFORE, "after_revision": after,
        "production_file_sha256": {"old": sha(old_source), "new": sha(new_source)},
        "whole_declaration_sha256": {"old_verify_observed": sha(old),
            "new_verify_observed": sha(new), "new_verify_finish": sha(finish)},
        "symmetric_replacement_counts": {"old": old_counts, "new_prefix": new_counts,
            "new_finish": finish_counts, "all_new_cfg_declarations": all_counts},
        "overlay_files": {p: sha(raw) for p, raw in files.items()},
        "generator_sha256": sha(Path(__file__).read_bytes()), "harness_sha256": sha(harness),
        "coverage": {"semantic_rows": list(range(15, 25)),
            "each_row_faults": ["lookup0", "decode", "boundary", "lookup1", "semantic"],
            "prefix_faults": ["parse", "public_transcript", "begin"],
            "row14_initializer_faults": ["lookup0", "decode"],
            "cases_per_observer_mode": 56, "observer": ["Some", "None"],
            "feature_builds_required": ["detail-phases", "default"]},
        "scope": "Actual saved S2 P3 semantic verification, real fields, SHA, parser and source arithmetic. Errors are injected only at explicit symmetric test wrappers; boundary injection changes one decoded coefficient before the unchanged source Boundary check. All returned fields, state/next_row, full digest inputs/outputs, native trace values, call events and observer phases are compared. Semantic verify has no Variant argument. No S1/D valid-proof execution or production-reachability claim is made.",
        "production_candidate_modified": False, "SBF_build": False}
    pin_bytes = (json.dumps(pins, indent=2) + "\n").encode()
    if args.check:
        assert (HERE / "source-pins.json").read_bytes() == pin_bytes
    else:
        (HERE / "source-pins.json").write_bytes(pin_bytes)
    if args.stage:
        assert args.stage.resolve() != ROOT and args.stage.is_dir()
        assert (args.stage / SOURCE).read_bytes() == new_source, "Stage must be a clean, exact final Git snapshot"
        for path, raw in files.items():
            dest = args.stage / path
            dest.parent.mkdir(parents=True, exist_ok=True)
            dest.write_bytes(raw)
        (args.stage / "verify-migration-overlay.json").write_bytes(pin_bytes)
    print(json.dumps({"status": "PASS", "after": after, "source_pins_sha256": sha(pin_bytes),
        "staged": str(args.stage) if args.stage else None}))


if __name__ == "__main__":
    main()
