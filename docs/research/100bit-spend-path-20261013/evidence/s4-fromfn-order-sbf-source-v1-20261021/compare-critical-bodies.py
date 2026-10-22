#!/usr/bin/env python3
"""Check exact source pins and normalized critical std function bodies."""
import hashlib, json, re
from pathlib import Path
ROOT=Path(__file__).resolve().parent
sha=lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
versions={
  "sbf_1_89_dev": {"array":ROOT/"source/sbf/core/array/mod.rs", "try":ROOT/"source/sbf/core/ops/try_trait.rs"},
  "kani_1_93": {"array":ROOT/"source/kani/core/array/mod.rs", "try":ROOT/"source/kani/core/ops/try_trait.rs"},
  "upstream_1_89": {"array":ROOT/"source/upstream-1.89/core/array/mod.rs", "try":ROOT/"source/upstream-1.89/core/ops/try_trait.rs"},
}
expected={
  "sbf_1_89_dev":{"array":"b5239b8af6bb1eb99b589518161f7fcf017dc80c275620517d145974cf7029a1","try":"bea48e635d47037be935806d3f5917a4954a88994c3c3663e8a1d44685b96dfa"},
  "kani_1_93":{"array":"5abe1fe75291e4f82c46d8ed27e0d0fabc2d733025c94fc326aa7f4dc6118053","try":"306d8b525083f1319fe08af7d8429a5be7f99009c5c3ea2c92102c0b4d396f45"},
  "upstream_1_89":{"array":"b5239b8af6bb1eb99b589518161f7fcf017dc80c275620517d145974cf7029a1","try":"bea48e635d47037be935806d3f5917a4954a88994c3c3663e8a1d44685b96dfa"},
}
def extract(path,needle):
    s=path.read_text(); p=s.index(needle); b=s.index("{",p); depth=0
    for i in range(b,len(s)):
        if s[i]=="{": depth+=1
        elif s[i]=="}":
            depth-=1
            if depth==0:
                body=s[p:i+1]
                return {"lines":[s.count("\n",0,p)+1,s.count("\n",0,i+1)],"normalized_sha256":hashlib.sha256(re.sub(r"\s+","",body).encode()).hexdigest()}
    raise ValueError(needle)
specs={
 "array.from_fn":("array","pub fn from_fn<T, const N: usize, F>"),
 "array.try_from_fn":("array","pub fn try_from_fn<R, const N: usize, F>"),
 "array.try_from_trusted_iterator":("array","fn try_from_trusted_iterator<T, R, const N: usize>("),
 "array.try_from_fn_erased":("array","fn try_from_fn_erased<T, R>("),
 "array.Guard.push_unchecked":("array","pub(crate) unsafe fn push_unchecked(&mut self, item: T)"),
 "ops.NeverShortCircuit.wrap_mut_1":("try","pub(crate) fn wrap_mut_1<A>("),
 "ops.NeverShortCircuit.branch":("try","fn branch(self) -> ControlFlow<NeverShortCircuitResidual, T>"),
}
actual={}
for ver,files in versions.items():
    actual[ver]={}
    for key,p in files.items():
        h=sha(p); assert h==expected[ver][key],(ver,key,h)
        actual[ver][key+"_file_sha256"]=h
comparisons={}
for name,(fkey,needle) in specs.items():
    rows={v:extract(fs[fkey],needle) for v,fs in versions.items()}
    hashes={v:r["normalized_sha256"] for v,r in rows.items()}
    comparisons[name]={"owners":rows,"all_three_same_normalized_body":len(set(hashes.values()))==1}
    assert comparisons[name]["all_three_same_normalized_body"],(name,hashes)
fetch=json.loads((ROOT/"upstream-fetch.json").read_text())
assert fetch["commit"]=="790f1537507dbdb0da320fbb3b1c1eca3b33c474"
for check in fetch["checks"]:
    assert check["http_status"]==200 and check["matches_installed_sbf_rust_src"]
    assert check["sha256"]==actual["sbf_1_89_dev"]["array_file_sha256" if check["path"].endswith("array/mod.rs") else "try_file_sha256"]
version=(ROOT/"toolchain/platform-tools-version.md").read_text().splitlines()
assert version[0]=="790f1537507dbdb0da320fbb3b1c1eca3b33c474  https://github.com/anza-xyz/rust.git"
meta=(ROOT/"toolchain/sbf-metadata.txt").read_text()
assert "rustc 1.89.0-dev" in meta and "commit-hash: unknown" in meta and "LLVM version: 20.1.7" in meta
out={"schema":"sbf-rust-stdlib-critical-owner-v1","rustc_source_commit":"790f1537507dbdb0da320fbb3b1c1eca3b33c474","rustc_binary_commit":None,"rustc_binary_commit_status":"rustc -vV reports unknown; do not infer from source commit","versions":actual,"critical_bodies":comparisons,"claim_limit":"Exact source package pin and matching source contents are established. Body equality across these source snapshots does not prove Aeneas translation, Rust operational semantics in Lean, or source-to-extracted-program refinement."}
(ROOT/"critical-body-comparison.json").write_text(json.dumps(out,indent=2)+"\n")
print("PASS: SBF source package pin, installed/source-commit bytes, and all seven critical bodies match Kani and upstream snapshots")
