#!/usr/bin/env python3
from pathlib import Path
import hashlib, json

HERE = Path(__file__).resolve().parent
ROOT = next(p for p in HERE.parents if (p / ".git").exists())
PIN = json.loads((HERE / "toolchain.json").read_text())

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

for entry in PIN["source_files"]:
    local = HERE / entry["relative_path"]
    upstream = ROOT / "docs/research/100bit-spend-path-20261013" / entry["upstream_comparator"]
    assert local.is_file(), local
    assert local.stat().st_size == entry["bytes"], local
    assert sha(local) == entry["sha256"], local
    assert upstream.is_file(), upstream
    assert sha(upstream) == entry["sha256"], upstream

array = (HERE / PIN["source_files"][0]["relative_path"]).read_text()
traits = (HERE / PIN["source_files"][1]["relative_path"]).read_text()
assert "pub fn from_fn<T, const N: usize, F>(f: F) -> [T; N]" in array
assert "try_from_fn(NeverShortCircuit::wrap_mut_1(f)).0" in array
assert "fn try_from_fn_erased<T, R>(" in array
assert "while guard.initialized < guard.array_mut.len()" in array
assert "generator(guard.initialized).branch()?" in array
assert "guard.push_unchecked(item)" in array
assert "pub(crate) unsafe fn push_unchecked(&mut self, item: T)" in array
assert "pub(crate) struct NeverShortCircuit<T>(pub T);" in traits
assert "move |a| NeverShortCircuit(f(a))" in traits
assert "impl<T> Try for NeverShortCircuit<T>" in traits

print(json.dumps({"status":"PASS", "source_files":2,
                  "source_shas_match_sysroot_snapshot_and_upstream_comparator":True,
                  "critical_from_fn_path":"from_fn -> wrap_mut_1 -> try_from_fn -> try_from_fn_erased -> Guard.push_unchecked",
                  "binary_source_commit":"unknown",
                  "lean_or_aeneas_refinement":False}, indent=2))
