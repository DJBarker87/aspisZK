#!/usr/bin/env python3
"""Compare critical upstream Kani and Rust 1.89 array/try-trait bodies."""
from pathlib import Path
import hashlib,json,re

root=Path(__file__).resolve().parent
versions={
  "kani_1_93": {"array":root/"std-source/kani-1.93/array-mod.rs", "try":root/"std-source/kani-1.93/try_trait.rs"},
  "rust_1_89_upstream": {"array":root/"std-source/rust-1.89-upstream/array-mod.rs", "try":root/"std-source/rust-1.89-upstream/try_trait.rs"},
}
expected={
  "kani_1_93":{"array":"5abe1fe75291e4f82c46d8ed27e0d0fabc2d733025c94fc326aa7f4dc6118053","try":"306d8b525083f1319fe08af7d8429a5be7f99009c5c3ea2c92102c0b4d396f45"},
  "rust_1_89_upstream":{"array":"b5239b8af6bb1eb99b589518161f7fcf017dc80c275620517d145974cf7029a1","try":"bea48e635d47037be935806d3f5917a4954a88994c3c3663e8a1d44685b96dfa"}}
def extract(path,needle):
    s=path.read_text(); p=s.index(needle); b=s.index("{",p); depth=0
    for i in range(b,len(s)):
        if s[i]=="{": depth+=1
        elif s[i]=="}":
            depth-=1
            if depth==0:
                body=s[p:i+1]
                return {"span":[s.count("\n",0,p)+1,s.count("\n",0,i+1)],
                        "normalized_sha256":hashlib.sha256(re.sub(r"\s+","",body).encode()).hexdigest(),
                        "body":body}
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
out={"schema":"rust-std-array-critical-body-compare-v1", "versions":{},"comparisons":{},
     "limitation":"Kani compiler uses upstream commit 53732...; 1.89 source fetched is upstream commit 294838..., while frozen SBF is a Solana rustc 1.89.0-dev fork with no exposed exact source commit. Equality here is upstream-to-upstream and does not establish SBF-fork body identity."}
for name,files in versions.items():
    out["versions"][name]={}
    for fkey,p in files.items():
        h=hashlib.sha256(p.read_bytes()).hexdigest(); assert h==expected[name][fkey],(name,fkey,h)
        out["versions"][name][fkey+"_file_sha256"]=h
for name,(fkey,needle) in specs.items():
    rows={}
    for ver,files in versions.items(): rows[ver]=extract(files[fkey],needle)
    out["comparisons"][name]={v:{k:x for k,x in r.items() if k!="body"} for v,r in rows.items()}
    out["comparisons"][name]["same_normalized_body"]=rows["kani_1_93"]["normalized_sha256"]==rows["rust_1_89_upstream"]["normalized_sha256"]
    out["comparisons"][name]["difference_excerpt"] = None if out["comparisons"][name]["same_normalized_body"] else {
        "kani_1_93":rows["kani_1_93"]["body"],"rust_1_89_upstream":rows["rust_1_89_upstream"]["body"]}
(root/"upstream-body-comparison.json").write_text(json.dumps(out,indent=2)+"\n")
print(json.dumps(out,indent=2))
