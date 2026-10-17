#!/usr/bin/env python3
"""Independent read-only source/reverse audit of Decisions 1d, 1e and fixed22 1f.

No build, Lean or runtime gate is run here. All inputs come from explicit Git
objects; temporary patch applications never touch a checked-out source tree.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile
import time

ROOT = Path(__file__).resolve().parents[4]
BASE = "docs/research/100bit-spend-path-20261013"
LEAD = "deb68369ba3ad7cc6706dc24b6503fac1cbe942b"
PAIR = "d4da2a662"
TRACE = "abd4c40a4"
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
    lead_retained = []
    for path in [WIRE + "r1_wire.rs",
                 "crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs",
                 "crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs"]:
        assert blob(TRACE, path) == blob(LEAD, path)
        lead_retained.append({"path": path, "sha256": sha(blob(LEAD, path))})
    assert blob(TRACE, WIRE + "r1_semantic.rs") == blob(PAIR, WIRE + "r1_semantic.rs")
    report = {"target": str(Path(__file__).relative_to(ROOT)), "exit_status": 0,
        "wall_seconds": time.monotonic() - start,
        "source_revision": git("rev-parse", TRACE).decode().strip(),
        "lead_revision": LEAD, "exact_1d_and_1e": decisions,
        "decision_1f": {"kind": "compile-time bound 22 <= 32",
            "before_sha256": sha(before), "after_sha256": sha(after),
            "reverse_expansion_exact": True, "ordered_trace_positions": list(range(22)),
            "introduced_fallible_calls": 0,
            "decoder_returned_state_preserved": True},
        "lead_source_retained": lead_retained,
        "runtime_or_formal_result": False, "print_axioms": "N/A (source audit)",
        "live_worktree_mutation": False, "SBF_build": False}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print("PASS: exact 1d/1e forward and reverse; fixed22 expansion/reverse; lead source retained")


if __name__ == "__main__":
    main()
