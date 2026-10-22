#!/usr/bin/env python3
from pathlib import Path
import hashlib
import json
import re
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
REPO = next(p for p in HERE.parents if (p / ".git").exists())
RESEARCH = REPO / "docs/research/100bit-spend-path-20261013"
M = json.loads((HERE / "manifest.json").read_text())
CANDIDATE = Path(M["candidate_branch"])

def sha_bytes(data):
    return hashlib.sha256(data).hexdigest()

def sha_file(path):
    return sha_bytes(Path(path).read_bytes())

def require(ok, why):
    if not ok:
        raise SystemExit("FAIL: " + why)

require(subprocess.check_output(["git", "-C", str(CANDIDATE), "rev-parse", "HEAD"], text=True).strip() == M["candidate_head"], "candidate HEAD")
for name, expected in {**M["three_candidate_blobs"], **M["unchanged_s4_callers"]}.items():
    p = CANDIDATE / name
    require(p.is_file() and sha_file(p) == expected, "candidate source pin " + name)

# Reconstruct the exact proposed weights.rs from the accepted baseline and the
# accepted early-return patch; compare the whole blob, not only the powers body.
weights = "crates/aspis-r1-cost-probe/src/weights.rs"
baseline = subprocess.check_output(["git", "-C", str(CANDIDATE), "show", M["candidate_overlay_base"] + ":" + weights])
patch = (RESEARCH / "evidence/s4-early-powers-generated-full-tx2-fields-d18-v1-20261022/source-pins/s1/powers-early.patch").read_bytes()
with tempfile.TemporaryDirectory(prefix="s4-pr10-sourcecheck-") as td:
    p = Path(td) / weights
    p.parent.mkdir(parents=True)
    p.write_bytes(baseline)
    proc = subprocess.run(["patch", "--batch", "-p1"], cwd=td, input=patch, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    require(proc.returncode == 0, "apply exact accepted powers patch: " + proc.stdout.decode(errors="replace"))
    reconstructed = p.read_bytes()
require(reconstructed == (CANDIDATE / weights).read_bytes(), "complete weights.rs equals accepted early-return patch output")
require(sha_bytes(reconstructed) == M["three_candidate_blobs"][weights], "reconstructed weights.rs PR#10 hash")

# Check the concrete constructor call and its exact N=29 powers use.
verifier = (CANDIDATE / "crates/aspis-r1-cost-probe/src/verifier.rs").read_text()
new_start = verifier.index("pub fn new<H:Digest32>")
new_end = verifier.index("\n    }", new_start)
new_body = verifier[new_start:new_end]
require("*g=powers::<29>(gamma);" in new_body, "Prepared::new calls powers::<29>(gamma) into caller scratch")

# Reuse the accepted focused source/body gates. They independently pin the
# generated candidate body, actual query callsite, checked-Q source, and prepare cut.
checks = [
    RESEARCH / "lean-candidates/s1-zero-loop-powers-proved-candidate-20261020/check-source-model.py",
    RESEARCH / "evidence/s4-concrete-v10-candidate-endpoint-v1-20261021/check_packet.py",
    RESEARCH / "evidence/s4-checked-q-push-bridge-v1-20261021/check-packet.py",
    RESEARCH / "evidence/s4-v10-concrete-queryops-builder-v1-20261021/source-evidence/check_query_callsite.py",
    RESEARCH / "evidence/s4-candidate-prepare-s1-parent-v1-20261022/check-source-cut.py",
    RESEARCH / "evidence/s4-early-powers-generated-full-tx2-fields-d18-v1-20261022/check_packet.py",
]
for script in checks:
    r = subprocess.run(["python3", str(script)], cwd=REPO, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    require(r.returncode == 0, "accepted evidence checker " + str(script) + "\n" + r.stdout)
    print(r.stdout.strip())

for p in HERE.rglob("*"):
    if p.is_file():
        require(p.suffix not in {".olean", ".llbc", ".elf", ".so", ".dylib", ".a"}, "compiled artifact in packet: " + str(p))

print(json.dumps({
    "status": "PASS",
    "candidate_head": M["candidate_head"],
    "three_blob_pins": M["three_candidate_blobs"],
    "unchanged_callers": M["unchanged_s4_callers"],
    "weights_patch_reconstructs_full_PR10_blob": True,
    "Prepared_new_powers29_call": True,
    "query_values_opening_then_four_dots": True,
    "claim": "candidate source/body binding checkpoint only; no frozen Std/runtime/adoption claim"
}, indent=2))
