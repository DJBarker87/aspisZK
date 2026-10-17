#!/usr/bin/env python3
"""Read-only source/reverse audit of Decisions 1d, 1e and registered 1f moves.

No build, Lean or runtime gate is run here. All inputs come from explicit Git
objects; temporary patch applications never touch a checked-out source tree.
"""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import resource
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parents[4]
BASE = "docs/research/100bit-spend-path-20261013"
LEAD = "deb68369ba3ad7cc6706dc24b6503fac1cbe942b"
PAIR = "d4da2a662"
TRACE = "abd4c40a4"
ROUND = "8c348ebbe"
HELPER = "2a5b09f40"
FOLD = "d0dbb2181"
STEP = "88b9bd4f1"
WIRE = "crates/aspis-r1-cost-probe/src/"
sha = lambda b: hashlib.sha256(b).hexdigest()


def git(*args):
    return subprocess.check_output(["git", "-C", str(ROOT), *args])


def blob(rev, path):
    return git("show", rev + ":" + path)


def patch_audit(path, proposal):
    before = blob(LEAD, path)
    after = blob(PAIR, path)
    patch = blob(PAIR, proposal)
    with tempfile.TemporaryDirectory(prefix="verify-query-reverse-") as tmp:
        target = Path(tmp) / path
        target.parent.mkdir(parents=True)
        target.write_bytes(before)
        forward = subprocess.run(["git", "apply", "--no-index", "-"],
                                 cwd=tmp, input=patch, capture_output=True)
        assert forward.returncode == 0, forward.stderr.decode()
        assert target.read_bytes() == after, "Not the exact approved proposal: " + path
        reverse = subprocess.run(["git", "apply", "--no-index", "--reverse", "-"],
                                 cwd=tmp, input=patch, capture_output=True)
        assert reverse.returncode == 0, reverse.stderr.decode()
        assert target.read_bytes() == before, "Reverse mismatch: " + path
    return {"path": path, "proposal": proposal, "proposal_sha256": sha(patch),
            "before_sha256": sha(before), "after_sha256": sha(after),
            "forward_exit": forward.returncode, "reverse_exit": reverse.returncode,
            "exact_proposal_and_reverse": True}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    start = time.monotonic()
    decisions = [patch_audit(WIRE + "r1_semantic.rs", BASE +
        "/tools/verify-prefix-proposal-kit/proposal/proposal.patch"),
        patch_audit(WIRE + "transcript.rs", BASE +
        "/tools/opening-queries-extraction-kit/proposal-eight-pairs/proposal.patch")]
    before = blob(PAIR, WIRE + "transcript.rs")
    after = blob(TRACE, WIRE + "transcript.rs")
    old = b"        for (i,&u) in q.iter().enumerate() { crate::trace::value(5,i,E::from_m31(aspis_core::field::M31(u))); }\n"
    new = "".join("        { let u=q[%d]; crate::trace::value(5,%d,E::from_m31(aspis_core::field::M31(u))); }\n" % (i, i)
                  for i in range(22)).encode()
    assert before.count(old) == 1
    assert before.replace(old, new) == after
    assert after.count(new) == 1 and after.replace(new, old) == before
    # The decoder's returned state (which can be an earlier advance) is retained.
    assert b"let (q,state)=aspis_core::r0_transcript::queries_from_pairs" in after
    assert b"self.state=state;" in after
    assert b"Result<[u32;22],crate::verifier::Error>" in after
    changed = git("diff", "--name-only", PAIR, TRACE, "--", "crates", "programs").decode().splitlines()
    assert changed == [WIRE + "transcript.rs"], changed
    semantic_before = blob(TRACE, WIRE + "r1_semantic.rs")
    semantic_after = blob(ROUND, WIRE + "r1_semantic.rs")
    lexer_spec = importlib.util.spec_from_file_location("source_lexer", ROOT / BASE /
        "tools/j1e-source-effect-audit.py")
    lexer = importlib.util.module_from_spec(lexer_spec)
    lexer_spec.loader.exec_module(lexer)
    loop = lexer.fragment(semantic_before, "for round in 0..10 {")[0].encode()
    inner = loop.split(b"\n", 1)[1].rsplit(b"\n", 1)[0]
    expanded = b"\n".join(b"    {\n        let round = " + str(i).encode() +
        b"usize;\n" + inner + b"\n    }" for i in range(10))
    assert semantic_before.count(loop) == 1
    assert semantic_before.replace(loop, expanded) == semantic_after
    assert semantic_after.count(expanded) == 1
    assert semantic_after.replace(expanded, loop) == semantic_before
    assert blob(ROUND, WIRE + "transcript.rs") == after
    helper_source = blob(HELPER, WIRE + "r1_semantic.rs")
    old_finish = lexer.fragment(semantic_after, "fn verify_finish<")[0].encode()
    moved = old_finish.split(b"\n", 1)[1].split(b"    mark(obs, 2);\n", 1)[0]
    assert moved.startswith(b"    let mut running = ")
    helper_headers = [
        b'#[cfg(not(feature = "prover"))]\nfn semantic_rounds<H: Digest32>(prefix: &Prefix<\'_>, mut transcript: SemanticTranscript<H>) -> Result<(QM31, [QM31; 10], SemanticTranscript<H>), Error> {\n',
        b'#[cfg(feature = "prover")]\nfn semantic_rounds<H: Digest32>(prefix: &Prefix<\'_>, mut transcript: SemanticTranscript<H>) -> Result<(QM31, [QM31; 10], SemanticTranscript<H>, [[QM31; 3]; 10]), Error> {\n']
    helper_returns = [b"    Ok((running, alpha, transcript))\n}\n\n",
                      b"    Ok((running, alpha, transcript, round_checks))\n}\n\n"]
    helpers = b"".join(head + moved + ret for head, ret in zip(helper_headers, helper_returns))
    calls = b'''    #[cfg(not(feature = "prover"))]
    let (running, alpha, mut transcript) = semantic_rounds(&prefix, transcript)?;
    #[cfg(feature = "prover")]
    let (running, alpha, mut transcript, round_checks) = semantic_rounds(&prefix, transcript)?;
'''
    assert helper_source.count(helpers) == 1 and helper_source.count(calls) == 1
    assert helper_source.replace(helpers, b"", 1).replace(calls, moved, 1) == semantic_after
    assert blob(HELPER, WIRE + "transcript.rs") == after
    fold_source = blob(FOLD, WIRE + "r1_semantic.rs")
    boundary_statement = b"        let boundary = polynomial.iter().copied().fold(polynomial[0], QM31::add);\n"
    value_statement = b"""        let value = polynomial
            .iter()
            .rev()
            .fold(QM31::ZERO, |a, &c| a.mul(alpha[round]).add(c));
"""
    fold_helpers = b"fn semantic_boundary(polynomial: &[QM31; 28]) -> QM31 {\n" + boundary_statement + b"    boundary\n}\n\n" + \
        b"fn semantic_value(polynomial: &[QM31; 28], alpha: &[QM31; 10], round: usize) -> QM31 {\n" + value_statement + b"    value\n}\n\n"
    boundary_call = b"        let boundary = semantic_boundary(&polynomial);\n"
    value_call = b"        let value = semantic_value(&polynomial, &alpha, round);\n"
    assert helper_source.count(boundary_statement) == helper_source.count(value_statement) == 20
    assert fold_source.count(fold_helpers) == 1
    restored = fold_source.replace(fold_helpers, b"", 1)
    assert restored.count(boundary_call) == restored.count(value_call) == 20
    assert restored.replace(boundary_call, boundary_statement).replace(value_call, value_statement) == helper_source
    assert blob(FOLD, WIRE + "transcript.rs") == after
    step_source = blob(STEP, WIRE + "r1_semantic.rs")
    begin = fold_source.index(b"        let row = 15 + round as u8;\n")
    end = fold_source.index(b"        running = value;\n", begin) + len(b"        running = value;\n")
    iteration = fold_source[begin:end]
    assert fold_source.count(iteration) == 20
    step_headers = [
        b'#[cfg(not(feature = "prover"))]\nfn semantic_round<H: Digest32>(prefix: &Prefix<\'_>, mut transcript: SemanticTranscript<H>, mut alpha: [QM31; 10], mut running: QM31, round: usize) -> Result<(QM31, [QM31; 10], SemanticTranscript<H>), Error> {\n',
        b'#[cfg(feature = "prover")]\nfn semantic_round<H: Digest32>(prefix: &Prefix<\'_>, mut transcript: SemanticTranscript<H>, mut alpha: [QM31; 10], mut running: QM31, round: usize, mut round_checks: [[QM31; 3]; 10]) -> Result<(QM31, [QM31; 10], SemanticTranscript<H>, [[QM31; 3]; 10]), Error> {\n']
    step_helpers = b"".join(head + iteration + ret for head, ret in zip(step_headers, helper_returns))
    step_calls = [b"        (running, alpha, transcript) = semantic_round(prefix, transcript, alpha, running, round)?;\n",
        b"        (running, alpha, transcript, round_checks) = semantic_round(prefix, transcript, alpha, running, round, round_checks)?;\n"]
    assert step_source.count(step_helpers) == 1
    restored = step_source.replace(step_helpers, b"", 1)
    assert all(restored.count(call) == 10 for call in step_calls)
    assert restored.replace(step_calls[0], iteration).replace(step_calls[1], iteration) == fold_source
    assert blob(STEP, WIRE + "transcript.rs") == after
    lead_retained = []
    for path in [WIRE + "r1_wire.rs",
                 "crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs",
                 "crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs"]:
        assert blob(STEP, path) == blob(LEAD, path)
        lead_retained.append({"path": path, "sha256": sha(blob(LEAD, path))})
    assert blob(TRACE, WIRE + "r1_semantic.rs") == blob(PAIR, WIRE + "r1_semantic.rs")
    own = resource.getrusage(resource.RUSAGE_SELF)
    children = resource.getrusage(resource.RUSAGE_CHILDREN)
    rss_unit = 1 if sys.platform == "darwin" else 1024
    report = {"target": str(Path(__file__).relative_to(ROOT)), "exit_status": 0,
        "command_argv": [sys.executable, *sys.argv],
        "wall_seconds": time.monotonic() - start,
        "peak_rss_bytes": max(own.ru_maxrss, children.ru_maxrss) * rss_unit,
        "swap_events": own.ru_nswap + children.ru_nswap,
        "source_revision": git("rev-parse", STEP).decode().strip(),
        "lead_revision": LEAD, "exact_1d_and_1e": decisions,
        "decision_1f": {"kind": "compile-time bound 22 <= 32",
            "before_sha256": sha(before), "after_sha256": sha(after),
            "reverse_expansion_exact": True, "ordered_trace_positions": list(range(22)),
            "introduced_fallible_calls": 0,
            "decoder_returned_state_preserved": True},
        "decision_1f_rounds": {"kind": "compile-time bound 10 <= 32",
            "before_sha256": sha(semantic_before), "after_sha256": sha(semantic_after),
            "original_loop_body_sha256": sha(inner), "reverse_expansion_exact": True,
            "ordered_rounds": list(range(10)), "ordered_rows": list(range(15, 25)),
            "all_10_body_copies_byte_identical": True},
        "decision_1f_owned_round_helpers": {"kind": "unchanged sequence in private owned-argument helper",
            "before_sha256": sha(semantic_after), "after_sha256": sha(helper_source),
            "moved_sequence_sha256": sha(moved), "both_cfg_bodies_byte_identical": True,
            "exact_reverse_to_predecessor": True, "cfg_alternatives": ["not(prover)", "prover"],
            "returned_existing_values": [["running", "alpha", "transcript"],
                ["running", "alpha", "transcript", "round_checks"]]},
        "decision_1f_fold_helpers": {"kind": "unchanged complete let statements in private helpers",
            "before_sha256": sha(helper_source), "after_sha256": sha(fold_source),
            "boundary_statement_sha256": sha(boundary_statement),
            "value_statement_sha256": sha(value_statement), "exact_reverse_to_predecessor": True,
            "each_helper_call_count_across_both_cfgs": 20,
            "boundary_arguments": ["&polynomial"],
            "value_arguments": ["&polynomial", "&alpha", "round"],
            "arithmetic_changed": False, "introduced_fallible_calls": 0},
        "decision_1f_single_round_helper": {"kind": "unchanged iteration sequence in private owned-argument helper",
            "before_sha256": sha(fold_source), "after_sha256": sha(step_source),
            "iteration_body_sha256": sha(iteration), "both_cfg_bodies_byte_identical": True,
            "exact_reverse_to_predecessor": True, "ordered_rounds_each_cfg": list(range(10)),
            "carried_existing_values": ["running", "alpha", "transcript", "prover:round_checks"],
            "arithmetic_changed": False, "new_failure_variants": False},
        "lead_source_retained": lead_retained,
        "runtime_or_formal_result": False, "print_axioms": "N/A (source audit)",
        "live_worktree_mutation": False, "SBF_build": False}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print("PASS: exact 1d/1e; fixed22/fixed10; owned round/fold/step helpers; all reverse audits; lead source retained")


if __name__ == "__main__":
    main()
