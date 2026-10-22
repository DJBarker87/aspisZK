#!/usr/bin/env python3
"""Append proof-only safety checks to unchanged shipped stream methods."""
from pathlib import Path
import hashlib,json
E=Path(__file__).resolve().parent.parent
S=Path('crates/aspis-prover/src')
rows=[]
for family,file,cls,seed in [('mask','state_only_hiding.rs','SeedExpander','seed'),('source','state_only_entropy.rs','Profile21SourceExpander','Zeroizing::new(seed)')]:
 domain = "aspis:state-only:private-mask-expand:v1" if family == "mask" else "aspis:state-only:profile21:source-expand:v1"
 s=(S/file).read_text()
 code=f'''
#[cfg(kani)]
mod safety13 {{
    use super::*;

    // A reachable formatter stub fails verification before diverging.
    fn formatter_never(_: &core::array::TryFromSliceError,
        _: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {{
        kani::assert(false, "slice formatter is unreachable");
        loop {{}}
    }}
    #[kani::proof]
    #[kani::unwind(84)]
    #[kani::stub(crate::host_hashv, crate::prover_commit_oracle::expander_query)]
    fn {family}_next_no_panic() {{
        let seed: [u8;32] = kani::any();
        let counter: u64 = kani::any();
        let word: usize = kani::any();
        kani::assume(word <= 8);
        let block: [u8;32] = kani::any();
        crate::prover_commit_oracle::reset_expander(b"{domain}", seed, counter);
        let mut actual = {cls} {{hash: crate::HOST_HASH, seed:{seed},counter,block,word}};
        let raw = actual.next_word();
        assert!(actual.word >= 1 && actual.word <= 8);
        assert_eq!(actual.counter, if word == 8 {{counter.wrapping_add(1)}} else {{counter}});
        let slot = actual.word - 1;
        let at = slot * 4;
        assert_eq!(raw, u32::from_le_bytes([actual.block[at],actual.block[at+1],actual.block[at+2],actual.block[at+3]]));
    }}
    #[kani::proof]
    #[kani::unwind(84)]
    #[kani::stub(<core::array::TryFromSliceError as core::fmt::Debug>::fmt, formatter_never)]
    #[kani::stub(crate::host_hashv, crate::prover_commit_oracle::expander_query)]
    fn {family}_next_no_formatter() {{ {family}_next_no_panic(); }}
}}
'''
 out=E/'rust-sources'/file;out.parent.mkdir(exist_ok=True);out.write_text(s+code)
 rows.append(dict(source=str(S/file),sha256=hashlib.sha256(s.encode()).hexdigest(),generated_sha256=hashlib.sha256(out.read_bytes()).hexdigest()))
(E/'safety-generation.json').write_text(json.dumps(rows,indent=2)+'\n')
