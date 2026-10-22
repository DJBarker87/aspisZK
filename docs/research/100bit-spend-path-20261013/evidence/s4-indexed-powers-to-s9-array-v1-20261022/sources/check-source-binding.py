#!/usr/bin/env python3
"""Check the adopted S4 powers body against the already-proved S1 model."""
from pathlib import Path
import hashlib
import json
import subprocess

ROOT = next(p for p in Path(__file__).resolve().parents if (p / ".git").exists())
HERE = Path(__file__).resolve().parent
RESEARCH = ROOT / "docs/research/100bit-spend-path-20261013"
SOURCE = ROOT / "crates/aspis-r1-cost-probe/src/weights.rs"
PINNED = HERE / "source-pins/weights.rs"
S1 = RESEARCH / "lean-candidates/s1-early-return-powers-proved-candidate-20261020"
sha = lambda b: hashlib.sha256(b).hexdigest()

adoption_commit = "29cbab431742f7e899870595167efa193a379f0a"
head = subprocess.check_output(
    ["git", "-C", str(ROOT), "rev-parse", "HEAD"], text=True
).strip()
subprocess.run(
    ["git", "-C", str(ROOT), "merge-base", "--is-ancestor", adoption_commit, head],
    check=True,
)
working = SOURCE.read_bytes()
committed = subprocess.check_output(
    ["git", "-C", str(ROOT), "show", f"{head}:crates/aspis-r1-cost-probe/src/weights.rs"]
)
assert working == committed == PINNED.read_bytes()

pins = json.loads((S1 / "extraction-input/source-pins.json").read_text())
expected = pins["candidate_transform"]["after"]
text = working.decode()
start = text.index("pub fn powers<const N:usize>")
brace = text.index("{", start)
depth = 0
end = None
for i in range(brace, len(text)):
    if text[i] == "{":
        depth += 1
    elif text[i] == "}":
        depth -= 1
        if depth == 0:
            end = i + 1
            break
assert end is not None
actual = text[start:end]
assert actual == expected, "adopted weights::powers body differs from proved S1 early-return body"

# Re-run the retained S1 provenance/source-model checker. This verifies the
# emitted Lean chunk is the same exact renamed function body consumed by its proof.
check = subprocess.run(
    ["python3", str(S1 / "check-source-model.py")],
    check=True,
    capture_output=True,
    text=True,
)
old_result = json.loads(check.stdout)
assert old_result["status"] == "PASS"

print(json.dumps({
    "status": "PASS",
    "observed_head": head,
    "adoption_commit_ancestor": adoption_commit,
    "weights_rs_sha256": sha(working),
    "weights_rs_git_blob": subprocess.check_output(
        ["git", "-C", str(ROOT), "hash-object", "crates/aspis-r1-cost-probe/src/weights.rs"], text=True
    ).strip(),
    "adopted_powers_body_sha256": sha(actual.encode()),
    "body_binding": "current merged weights::powers exactly equals retained S1 early-return candidate body",
    "retained_s1_model_checker": old_result,
    "scope": "N=4 S9 array bridge is candidate proof reuse; kpowers/from_fn and complete S4 closure remain open",
}, indent=2))
