#!/usr/bin/env python3
"""Hash exact Kani-compiler std method bodies at the recorded Rust commit."""
from pathlib import Path
import hashlib, json, re

root = Path(__file__).resolve().parent
array = root / "std-source/kani-1.93/array-mod.rs"
tr = root / "std-source/kani-1.93/try_trait.rs"
expected = {
    "array-mod.rs": "5abe1fe75291e4f82c46d8ed27e0d0fabc2d733025c94fc326aa7f4dc6118053",
    "try_trait.rs": "306d8b525083f1319fe08af7d8429a5be7f99009c5c3ea2c92102c0b4d396f45",
}
sha = lambda b: hashlib.sha256(b).hexdigest()
assert sha(array.read_bytes()) == expected["array-mod.rs"]
assert sha(tr.read_bytes()) == expected["try_trait.rs"]

def function(src: str, needle: str):
    p = src.index(needle)
    b = src.index("{", p)
    depth = 0
    for i in range(b, len(src)):
        if src[i] == "{": depth += 1
        elif src[i] == "}":
            depth -= 1
            if depth == 0:
                body = src[p:i+1]
                return {"span": [src.count("\n", 0, p)+1, src.count("\n", 0, i+1)],
                        "body_sha256_whitespace_normalized": sha(re.sub(r"\s+", "", body).encode()),
                        "body": body}
    raise ValueError(needle)

a = array.read_text(); t = tr.read_text()
rows = {
    "array.from_fn": function(a, "pub fn from_fn<T, const N: usize, F>"),
    "array.try_from_fn": function(a, "pub fn try_from_fn<R, const N: usize, F>"),
    "array.try_from_trusted_iterator": function(a, "fn try_from_trusted_iterator<T, R, const N: usize>("),
    "array.try_from_fn_erased": function(a, "fn try_from_fn_erased<T, R>("),
    "array.Guard.push_unchecked": function(a, "pub(crate) unsafe fn push_unchecked(&mut self, item: T)"),
    "ops.NeverShortCircuit.wrap_mut_1": function(t, "pub(crate) fn wrap_mut_1<A>("),
    "ops.NeverShortCircuit.branch": function(t, "fn branch(self) -> ControlFlow<NeverShortCircuitResidual, T>"),
}
for row in rows.values(): row.pop("body")
out = {"schema":"kani-rust-std-critical-body-hashes-v1", "commit":"53732d5e076329a62f71d3c6901886ce8a71e812",
       "inputs":{"array-mod.rs_sha256":expected["array-mod.rs"],"try_trait.rs_sha256":expected["try_trait.rs"]},
       "bodies":rows,
       "cross_toolchain_note":"These hashes pin only upstream Kani 1.93 source; no SBF 1.89 fork body was available to compare."}
(root/"critical-bodies.json").write_text(json.dumps(out,indent=2)+"\n")
print(json.dumps(out,indent=2))
