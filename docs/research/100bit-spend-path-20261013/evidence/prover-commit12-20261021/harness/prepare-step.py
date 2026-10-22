#!/usr/bin/env python3
"""Generate a one-iteration harness from each literal shipped m31 loop body.
No full scalar/array unroll. Production bodies are copied unchanged.
"""
import hashlib, json, re
from pathlib import Path
E=Path(__file__).resolve().parent.parent
S=Path('crates/aspis-prover/src')
rows=[]
for family, file, cls, seed, domain, p in [
 ('mask','state_only_hiding.rs','SeedExpander','seed','aspis:state-only:private-mask-expand:v1','P'),
 ('source','state_only_entropy.rs','Profile21SourceExpander','Zeroizing::new(seed)','aspis:state-only:profile21:source-expand:v1','aspis_core::field::P')]:
 s=(S/file).read_text()
 start=s.index('    fn m31(&mut self)')
 a=s.index('            let candidate = self.next_word()',start)
 b=s.index('\n        }',a)
 body=s[a:b].replace('self.next_word()', 'actual.next_word()')
 # Wrap exactly the body once, retaining early return in the local closure.
 text=f'''
#[cfg(kani)]
mod callsite12 {{
    use super::*;
    use crate::prover_commit_reference::State;
    use crate::prover_commit_oracle as rom;
    #[kani::proof]
    #[kani::unwind(84)]
    #[kani::stub(crate::host_hashv, rom::expander_query)]
    #[kani::stub_verified({cls}::next_word)]
    #[kani::stub_verified(crate::prover_commit_reference::next)]
    fn {family}_iteration() {{
        let before: State = kani::any();
        kani::assume(before.word <= 8);
        let State {{seed,counter,block,word}} = before;
        rom::reset_expander(b"{domain}", seed, counter);
        let (raw, after) = crate::prover_commit_reference::next(
            crate::HOST_HASH, b"{domain}", before);
        let candidate = raw & 0x7fff_ffff;
        let expected = if candidate < {p} {{ Ok(aspis_core::field::M31(candidate)) }}
            else {{ Err(StateOnlyMaskBuildError::MaskSampleExhausted) }};
        let mut actual = {cls} {{hash: crate::HOST_HASH,seed: {seed},counter,block,word}};
        let observed = (|| {{
{body}
            Err(StateOnlyMaskBuildError::MaskSampleExhausted)
        }})();
        assert_eq!(observed, expected);
        assert_eq!({('*actual.seed' if family=='source' else 'actual.seed')}, after.seed);
        assert_eq!(actual.counter, after.counter);
        assert_eq!(actual.block, after.block);
        assert_eq!(actual.word, after.word);
        assert!(actual.word <= 8);
    }}
}}
'''
 out=E/'rust-sources'/file
 out.parent.mkdir(exist_ok=True)
 out.write_text(s+text)
 rows.append(dict(family=family,source=str(S/file),sha256=hashlib.sha256(s.encode()).hexdigest(),loop_iteration=body,generated_sha256=hashlib.sha256(out.read_bytes()).hexdigest()))
for file in ['prover_commit_reference.rs','prover_commit_oracle.rs']:
 (E/'rust-sources'/file).write_bytes((S/file).read_bytes())
(E/'step-inputs.json').write_text(json.dumps(rows,indent=2)+'\n')
