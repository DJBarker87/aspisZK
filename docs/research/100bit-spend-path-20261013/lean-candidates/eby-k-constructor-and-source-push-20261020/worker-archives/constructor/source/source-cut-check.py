from pathlib import Path
import hashlib,json
repo=Path('/Users/dominic/ZK')
original=repo/'crates/aspis-r1-cost-probe/src/fast_pairing.rs'
cut=Path(__file__).resolve().parent/'input/lib.rs'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
s=original.read_text(); c=cut.read_text()
fragments={
 'canonical_dot_new':'pub struct Dot { sums:[u64;4] }\n    impl Dot {\n        pub fn new()->Self {Self{sums:[0;4]}}',
 'eby_k_dot_new':'pub struct EbyKDot {\n    c0: canonical::Dot,\n    c1: canonical::Dot,\n    count: usize,\n}\n\nimpl EbyKDot {\n    pub fn new() -> Self {\n        Self { c0: canonical::Dot::new(), c1: canonical::Dot::new(), count: 0 }\n    }'
}
checks={k:(v in s) for k,v in fragments.items()}
checks['cut_mentions_dot_constructor']='Self{sums:[0;4]}' in c
checks['cut_mentions_eby_k_constructor']='Self { c0: canonical::Dot::new(), c1: canonical::Dot::new(), count: 0 }' in c
checks['public_wrapper']='pub fn new_entry() -> fast_pairing::EbyKDot { fast_pairing::EbyKDot::new() }' in c
checks['no_extra_methods']='pub fn push' not in c and 'pub fn finish' not in c
out={'schema':'exact-source-cut-check-v1','source_path':str(original),'source_sha256':sha(original),'cut_path':str(cut),'cut_sha256':sha(cut),'source_fragments_exact':checks,'passed':all(checks.values()),'scope':'Verifies selected constructor source fragments are present byte-for-byte and the cut contains no push/finish operation. It does not claim whole-module Rust identity.'}
(Path(__file__).with_name('source-cut-check.json')).write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
assert out['passed']
print(json.dumps(out,indent=2))
