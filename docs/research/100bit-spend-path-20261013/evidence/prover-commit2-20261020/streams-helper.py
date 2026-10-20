from pathlib import Path
p=Path('/home/dombarker/project-offloads/codex-cx-prover-commit2-20261020/src/crates/aspis-prover/src/state_only_entropy.rs')
s=p.read_text()
a='            self.block = hash(&[\n                PROFILE21_SOURCE_EXPAND_DOMAIN,\n                &seed,\n                &counter.to_le_bytes(),\n            ]);'
b='            self.block = profile21_source_expander_block(hash, seed, counter);'
assert s.count(a)==1
p.write_text(s.replace(a,b)+'\nfn profile21_source_expander_block(hash: HashFn, seed: [u8;32], counter: u64) -> [u8;32] {\n    hash(&[PROFILE21_SOURCE_EXPAND_DOMAIN, &seed, &counter.to_le_bytes()])\n}\n')
