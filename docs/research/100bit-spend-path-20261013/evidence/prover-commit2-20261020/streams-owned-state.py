from pathlib import Path
p=Path('/home/dombarker/project-offloads/codex-cx-prover-commit2-20261020/src/crates/aspis-prover/src/state_only_entropy.rs')
s=p.read_text()
start=s.index('    fn next_word(&mut self) -> u32 {',s.index('impl Profile21SourceExpander'))
end=s.index('\n    fn m31(',start)
s=s[:start]+'    fn next_word(&mut self) -> u32 {\n        let (value, block, counter, word) = profile21_source_next_word(\n            self.hash, *self.seed, self.block, self.counter, self.word);\n        self.block = block;\n        self.counter = counter;\n        self.word = word;\n        value\n    }\n'+s[end:]
s+='\nfn profile21_source_next_word(hash: HashFn, seed: [u8;32], mut block: [u8;32], mut counter: u64, mut word: usize) -> (u32, [u8;32], u64, usize) {\n    if word == 8 {\n        block = profile21_source_expander_block(hash, seed, counter);\n        counter = counter.wrapping_add(1);\n        word = 0;\n    }\n    let start = 4 * word;\n    word += 1;\n    let value = u32::from_le_bytes(block[start..start+4].try_into().unwrap());\n    (value, block, counter, word)\n}\n'
p.write_text(s)
