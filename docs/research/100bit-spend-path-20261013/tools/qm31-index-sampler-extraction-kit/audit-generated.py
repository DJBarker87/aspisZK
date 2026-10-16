#!/usr/bin/env python3
"""Fail closed on a changed/opaque sampler emission. This is not refinement."""
import argparse
import hashlib
import json
from pathlib import Path
import re

EXPECTED = {
    "field.CM31.new", "sampler.qm31_div_pass_loop.body",
    "sampler.qm31_div_pass_loop", "sampler.qm31_div_pass",
    "sampler.qm31_digits_loop0.body", "sampler.qm31_digits_loop0",
    "sampler.qm31_digits_loop1.body", "sampler.qm31_digits_loop1",
    "sampler.qm31_digits", "sampler.qm31_sample",
}
NS = "AspisR1Qm31SamplerIndex."

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("generated", type=Path)
    args = p.parse_args()
    root = args.generated
    meta = json.loads((root / "translation.json").read_text())
    assert {f["lean_name"] for f in meta["functions"]} == {NS+n for n in EXPECTED}
    assert len(meta["functions"]) == len(EXPECTED)
    assert all(f["is_local"] and not f["is_opaque"] for f in meta["functions"])
    assert {t["lean_name"] for t in meta["types"]} == {NS+"field."+n for n in ["M31", "CM31", "QM31"]}
    assert [g["lean_name"] for g in meta["globals"]] == [NS+"field.P"]
    assert not meta["trait_decls"] and not meta["trait_impls"]
    files = {str(f.relative_to(root)) for f in root.rglob("*") if f.is_file()}
    assert files == {"translation.json", "AspisR1Qm31SamplerIndex/Types.lean", "AspisR1Qm31SamplerIndex/Funs.lean"}
    code = (root / "AspisR1Qm31SamplerIndex/Funs.lean").read_text()
    assert not re.search(r"\b(sorry|axiom|opaque)\b", code)
    for text in ["let a ← Array.update rank j1 i5", "ok (cont (a, remainder1, j1))",
                 "let (quotient, digit) ← sampler.qm31_div_pass rank",
                 "ok (cont (quotient, a, i1))"]:
        assert text in code, text
    print(json.dumps({"functions": 10, "types": 3, "globals": 1, "opaque": 0,
        "files": {n: hashlib.sha256((root/n).read_bytes()).hexdigest() for n in sorted(files)},
        "scope": "Pinned declaration/output inventory and visible array carry only; semantic correspondence requires separate proofs."}, indent=2))

if __name__ == "__main__":
    main()
