#!/usr/bin/env python3
"""Pin exact old/new begin bodies; generate a test-only interface overlay."""
from pathlib import Path
import argparse
import hashlib
import importlib.util
import json
import subprocess

P = Path(__file__).resolve().parent
ROOT = P.parents[1]
SOURCE = "crates/aspis-r1-cost-probe/src/r1_wire.rs"
ap = argparse.ArgumentParser(description=__doc__)
ap.add_argument("--check", action="store_true")
args = ap.parse_args()
spec = importlib.util.spec_from_file_location(
    "source_audit", ROOT / "docs/research/100bit-spend-path-20261013/tools/j1e-source-effect-audit.py")
audit = importlib.util.module_from_spec(spec)
spec.loader.exec_module(audit)

def revision(ref):
    return subprocess.check_output(["git", "rev-parse", ref], cwd=ROOT, text=True).strip()

def sha(raw):
    return hashlib.sha256(raw).hexdigest()

before = revision("99263bea0")
after = revision("c16ab4d76619cf2cf80ece9d7e60e47975957af0")
sources = {side: audit.git_bytes(rev, SOURCE) for side, rev in [("old", before), ("new", after)]}
bodies = {side: audit.fragment(raw, "pub fn begin<")[0] + "\n" for side, raw in sources.items()}
loop = """    for (i, value) in zc.iter_mut().enumerate() {
        *value = transcript.semantic_validated(prefix.validated_record(3 + i as u8)?)?;
    }
"""
straightline = "".join(
    f"    zc[{i}] = transcript.semantic_validated(prefix.validated_record({i + 3})?)?;\n"
    for i in range(10))
assert bodies["old"].count(loop) == 1
assert bodies["new"] == bodies["old"].replace(loop, straightline)
errors = {side: audit.fragment(raw, "pub enum Error {")[0] for side, raw in sources.items()}
assert errors["old"] == errors["new"]
files = {side + "_begin.rs": body.encode() for side, body in bodies.items()}
files["error.rs"] = ("#[derive(Clone, Copy, Debug, PartialEq, Eq)]\n" + errors["new"] + "\n").encode()
pins = {
    "before_revision": before,
    "after_revision": after,
    "source": SOURCE,
    "source_sha256": {side: sha(raw) for side, raw in sources.items()},
    "generated_files": {name: sha(raw) for name, raw in files.items()},
    "kit_files": {name: sha((P / name).read_bytes()) for name in ["Cargo.toml", "harness.rs", "extract.py"]},
    "approved_diff_only": "Replace exactly the old zc loop with ten calls for rows3..12; all other begin bytes identical.",
    "scope": "Test-only overlay of exact entire old/new begin declarations against the same instrumented interfaces. Twenty injected failures plus success control check Rust Result/error and call/state prefix ordering. These injected interface failures are not claimed reachable in actual production SemanticTranscript.",
}
if args.check:
    assert all((P / name).read_bytes() == raw for name, raw in files.items())
    assert json.loads((P / "source-pins.json").read_text()) == pins
    print("PASS: exact99263bea0/c16ab4d76 begin bodies; only approved ten-call replacement; overlay pins")
else:
    for name, raw in files.items():
        (P / name).write_bytes(raw)
    (P / "source-pins.json").write_text(json.dumps(pins, indent=2) + "\n")
