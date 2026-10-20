from pathlib import Path
p=Path('/home/dombarker/project-offloads/codex-cx-prover-commit2-20261020/src/crates/aspis-prover/src/state_only_hiding.rs')
s=p.read_text()
a='            self.block =\n                (self.hash)(&[MASK_EXPAND_DOMAIN, &self.seed, &self.counter.to_le_bytes()]);'
b='            self.block = state_only_mask_expander_block(self.hash, self.seed, self.counter);'
assert s.count(a)==1
p.write_text(s.replace(a,b)+'\nfn state_only_mask_expander_block(hash: HashFn, seed: [u8;32], counter: u64) -> [u8;32] {\n    hash(&[MASK_EXPAND_DOMAIN, &seed, &counter.to_le_bytes()])\n}\n')
