#!/usr/bin/env python3
"""Check the frozen source/trace packet; this does not run Aeneas."""

import hashlib
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parent


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


expected = {
    "source/InterpMatchCtxs.v2.ml": "7a23c3abc469212b14c2ec1ada3997c89fc65b418535ba8be01682cb4b5d4cd3",
    "source/InterpMatchCtxs.v3.ml": "0d2ab7873780feaea346facc38f5429144153f6e93a08aef636509505216bb18",
    "trace/admission.json": "93196bba00616d04720cf2879cb2f414345b9c55ff372f1af1a0ae494d88bab0",
    "trace/receipt.json": "0df77bf5bb4548dcdee5b1a202b0bb3aa6134713e45777723a64506904eb2c99",
    "trace/run.time": "a9029e55c7f1e1a363643747166539b2a73f84ba0e89ce86e5a7014005390e0a",
    "trace/stdout.log": "dc591a7d3feb7eab65f74128f3a9e49c6202e96ebddeaec90714748d6e2ecf25",
    "selector-output.json": "",  # regenerated extraction summary; input is checked below
    "tooling/toolchain.json": "",  # retained direct producer receipt; hash checked for presence below
    "tooling/source-pins.json": "",  # retained direct producer receipt; hash checked for presence below
}

for rel, want in expected.items():
    path = ROOT / rel
    assert path.is_file(), f"missing {rel}"
    if want:
        assert sha(path) == want, f"hash mismatch: {rel}"

v2 = (ROOT / "source/InterpMatchCtxs.v2.ml").read_text()
v3 = (ROOT / "source/InterpMatchCtxs.v3.ml").read_text()
assert "ty_has_regions_complete" not in v2
assert "method! visit_TDynTrait env tr = super#visit_TDynTrait env tr" in v3
assert "not (ty_has_regions_complete ty0)" in v3
assert "not (ty_has_regions_complete ty1)" in v3
assert "not (ty_has_regions_in_pred (fun _ -> true) ty0)" in v2

receipt = json.loads((ROOT / "trace/receipt.json").read_text())
assert receipt["exit_status"] == 2
assert receipt["input_sha256"] == "32f4b2416a2566ab2ceb6bd04f10a1b601e765fab9217a4fe3501cab0b0340a4"
assert receipt["binary_sha256_before"] == receipt["binary_sha256_after"]
assert receipt["limits"] == {
    "memory.high": "2147483648",
    "memory.max": "3221225472",
    "memory.swap.max": "0",
}
trace = (ROOT / "trace/stdout.log").read_text()
assert "push_unchecked" in trace
assert "- projected target:" in trace
assert "array_mut = ⊥" in trace
assert "match_ctx_with_target" in trace

selector = json.loads((ROOT / "selector-output.json").read_text())
assert selector["sha256"] == "551bbefc19ef647c0670f119bfac8f2589d677169c49101fc7b584d0b71fa3bc"
assert selector["classification"].startswith("changed Charon selector output only")
assert selector["selected_declarations"]["types"]["7"]["kind"] == "Union"
assert selector["selected_declarations"]["functions"]["21"]["opacity"] == "Transparent"
assert selector["selected_declarations"]["functions"]["35"]["opacity"] == "Foreign"

# Predicate-level negative/positive contract tests only, not an OCaml run.
import subprocess
subprocess.run(["python3", str(ROOT / "review/test_trait_type_guard.py")], check=True)
print("source/trace pins and scoped guard contract PASS; no v3 Aeneas run claimed")
