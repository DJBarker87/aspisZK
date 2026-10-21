#!/usr/bin/env python3
"""Partition one actual scalar execution by its first accepted candidate.
No second scalar execution and no scalar/next-word stub.
"""
from pathlib import Path
import hashlib,json
E=Path(__file__).resolve().parent.parent
rows=[]
for family,file,cls,seed,seed_after in [('mask','state_only_hiding.rs','SeedExpander','seed','actual.seed'),('source','state_only_entropy.rs','Profile21SourceExpander','Zeroizing::new(seed)','*actual.seed')]:
 p=E/'rust-sources'/file
 s=p.read_text().split('\n#[cfg(kani)]\nmod scalar13')[0]
 domain='aspis:state-only:private-mask-expand:v1' if family=='mask' else 'aspis:state-only:profile21:source-expand:v1'
 text=f'''
#[cfg(kani)]
mod scalar13 {{
    use super::*;
    use crate::prover_commit_oracle as rom;
    fn candidate(block: [u8;32], word: usize, counter: u64, i: usize) -> u32 {{
        let linear = word + i;
        let bytes = if linear < 8 {{block}}
            else {{rom::expander_block(counter.wrapping_add((linear / 8 - 1) as u64))}};
        let offset = 4 * (linear % 8);
        u32::from_le_bytes([bytes[offset],bytes[offset+1],bytes[offset+2],bytes[offset+3]]) & 0x7fff_ffff
    }}
    fn formatter_never(_: &core::array::TryFromSliceError,
        _: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {{
        kani::assert(false, "scalar slice formatter is unreachable"); loop {{}}
    }}
    #[kani::proof]
    #[kani::unwind(84)]
    #[kani::stub(crate::host_hashv, rom::expander_query)]
    #[kani::stub(<core::array::TryFromSliceError as core::fmt::Debug>::fmt, formatter_never)]
    fn {family}_scalar_partition() {{
        let seed: [u8;32] = kani::any();
        let counter: u64 = kani::any();
        let block: [u8;32] = kani::any();
        let word: usize = kani::any();
        kani::assume(word <= 8);
        let stop: usize = kani::any();
        kani::assume(stop <= 16);
        rom::reset_expander(b"{domain}", seed, counter);
        for i in 0..16 {{
            let c = candidate(block,word,counter,i);
            if i < stop {{ kani::assume(c == aspis_core::field::P); }}
            if i == stop {{ kani::assume(c < aspis_core::field::P); }}
        }}
        let consumed = if stop < 16 {{stop+1}} else {{16}};
        let linear = word + consumed - 1;
        let reloads = linear / 8;
        let expected_block = if reloads == 0 {{block}}
            else {{rom::expander_block(counter.wrapping_add((reloads - 1) as u64))}};
        let expected = if stop < 16 {{Ok(aspis_core::field::M31(candidate(block,word,counter,stop)))}}
            else {{Err(StateOnlyMaskBuildError::MaskSampleExhausted)}};
        let mut actual = {cls} {{hash: crate::HOST_HASH,seed:{seed},counter,block,word}};
        let result = actual.m31();
        assert_eq!(result,expected);
        assert_eq!({seed_after},seed);
        assert_eq!(actual.counter,counter.wrapping_add(reloads as u64));
        assert_eq!(actual.block,expected_block);
        assert_eq!(actual.word,linear % 8 + 1);
    }}
}}
'''
 p.write_text(s+text)
 rows.append(dict(family=family,generated_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),domain=domain,partition='first success 0..15 or all sixteen reject; arbitrary before state word<=8'))
(E/'scalar-generation.json').write_text(json.dumps(rows,indent=2)+'\n')
