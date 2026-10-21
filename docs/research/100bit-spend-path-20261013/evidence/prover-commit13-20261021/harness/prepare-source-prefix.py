#!/usr/bin/env python3
from pathlib import Path
import hashlib,json
E=Path(__file__).resolve().parent.parent
source=Path('crates/aspis-prover/src/state_only_entropy.rs').read_text()
a=source.index('        let source_mask_seed',source.index('pub fn reserve_and_build_pool_v1_pair_forest_mask_material_v1('))
b=source.index('        self.field_mask_entropy.zeroize();',a)
prefix=source[a:b]
assert prefix.count('self.field_mask_entropy.as_ref()')==1
cut=prefix.replace('self.field_mask_entropy.as_ref()','&entropy')
p=E/'rust-sources/state_only_entropy.rs';s=p.read_text()
(p.parent/(p.name+'.source-words-v2.txt')).write_text(s)
assert s.rstrip().endswith('}')
code='''
    // Exact inline expression, cut after material success and consumed check.
    // Does not certify that the full wrapper reaches this point.
    #[kani::proof]
    #[kani::unwind(170)]
    fn source_inline_prefix() {
        let context=init();let hash:HashFn=observe_hash;
        let precommit_binding=unsafe{BIND};let entropy=unsafe{ENTROPY};
'''+cut+'''
        unsafe{assert_eq!(HASH_CALLS,1);assert_eq!(*source_mask_seed,ANSWERS[0]);}
    }
'''
s=s.rstrip()[:-1]+code+'}\n';p.write_text(s)
(E/'source-prefix-generation.json').write_text(json.dumps(dict(source_sha256=hashlib.sha256(source.encode()).hexdigest(),literal_prefix=prefix,only_replacement='self.field_mask_entropy.as_ref() -> universally arbitrary &entropy',generated_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),scope='literal inline source seed expression only; successful complete wrapper remains unproved'),indent=2)+'\n')
