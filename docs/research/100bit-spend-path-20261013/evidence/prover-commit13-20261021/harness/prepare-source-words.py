#!/usr/bin/env python3
"""Split only the timed-out source scalar by its nine legal word positions."""
from pathlib import Path
import hashlib,json
E=Path(__file__).resolve().parent.parent
p=E/'rust-sources/state_only_entropy.rs';s=p.read_text()
a=s.index('\n#[cfg(kani)]\nmod scalar13');b=s.index('\n#[cfg(kani)]\nmod seeds13',a)
block=s[a:b]
attrs='''    #[kani::proof]
    #[kani::unwind(84)]
    #[kani::stub(crate::host_hashv, rom::expander_query)]
    #[kani::stub(<core::array::TryFromSliceError as core::fmt::Debug>::fmt, formatter_never)]
'''
assert attrs in block
block=block.replace(attrs+'    fn source_scalar_partition() {', '    fn check<const WORD:usize>() {')
block=block.replace('        let word: usize = kani::any();\n        kani::assume(word <= 8);','        let word = WORD;')
block=block.rstrip()[:-1]
for i in range(9):block+=attrs+f'    fn source_word_{i}() {{check::<{i}>();}}\n'
block+='}\n'
p.write_text(s[:a]+block+s[b:])
(E/'source-words-generation.json').write_text(json.dumps(dict(source_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),partition='word positions 0 through 8; symbolic first-acceptance position retained'),indent=2)+'\n')
