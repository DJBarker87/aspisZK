from pathlib import Path
p=Path('/home/dombarker/project-offloads/codex-cx-prover-commit2-20261020/src/crates/aspis-prover/src/state_only_entropy.rs')
s=p.read_text()
a='            self.block = (self.hash)(&[\n                PROFILE21_SOURCE_EXPAND_DOMAIN,\n                self.seed.as_ref(),\n                &self.counter.to_le_bytes(),\n            ]);'
b='            let hash = self.hash;\n            let seed: [u8; 32] = *self.seed;\n            let counter = self.counter;\n            self.block = hash(&[\n                PROFILE21_SOURCE_EXPAND_DOMAIN,\n                &seed,\n                &counter.to_le_bytes(),\n            ]);'
assert s.count(a)==1
p.write_text(s.replace(a,b))
