#!/usr/bin/env python3
"""Generate nine complete word-slot cases; retain arbitrary base/digest data."""
from pathlib import Path
import sys
check='--check' in sys.argv
assert '--source-root' in sys.argv, 'Historical experiment: pass --source-root for a retained snapshot.'
root=Path(sys.argv[sys.argv.index('--source-root')+1])
for file,kind,typ,domain,seed in [
 ('prover_commit_reference.rs','reference','limb_caller',None,None),
 ('state_only_hiding.rs','mask','SeedExpander::m31','aspis:state-only:private-mask-expand:v1','seed'),
 ('state_only_entropy.rs','source','Profile21SourceExpander::m31','aspis:state-only:profile21:source-expand:v1','Zeroizing::new(seed)')]:
 p=root/file;s=p.read_text();module='mod contracts {' if kind=='reference' else 'mod prover_commit_caller7 {'
 start=s.index(module);end=s.index('\n}',start)
 begin='    // BEGIN PROVER_COMMIT7_SCALAR_WORD_CASES\n';finish='    // END PROVER_COMMIT7_SCALAR_WORD_CASES\n'
 if kind=='reference':
  setup='''        let domain = domain();
        let seed: [u8;32] = kani::any();
        let base: u64 = kani::any();
        let delta: u8 = kani::any();
        kani::assume(delta <= 6);
        let counter = base.wrapping_add(u64::from(delta));
        let block: [u8;32] = kani::any();
        rom::reset_expander(domain, seed, base);
        let _ = limb_caller(crate::HOST_HASH, domain, State { seed, counter, block, word });
'''
  attrs='    #[kani::stub_verified(rom::expander_query)]\n'
 else:
  setup='''        let seed: [u8;32] = kani::any();
        let base: u64 = kani::any();
        let delta: u8 = kani::any();
        kani::assume(delta <= 6);
        let counter = base.wrapping_add(u64::from(delta));
        let block: [u8;32] = kani::any();
        rom::reset_expander(b"DOMAIN", seed, base);
        let mut actual = TYPE { hash: crate::HOST_HASH, seed: SEED, counter, block, word };
        let _ = actual.m31();
'''.replace('DOMAIN',domain).replace('TYPE',typ.split('::')[0]).replace('SEED',seed)
  attrs='''    #[kani::stub_verified(rom::expander_query)]
    #[kani::stub_verified(crate::prover_commit_reference::limb_caller)]
'''.replace('TYPE',typ.split('::')[0])
 block=begin+'    fn scalar_at(word: usize) {\n'+setup+'    }\n    macro_rules! scalar_word_case { ($name:ident, $word:expr) => {\n'+f'    #[kani::proof_for_contract({typ})]\n'+'    #[kani::unwind(84)]\n    #[kani::stub(crate::host_hashv, rom::expander_query)]\n'+attrs+'    fn $name() { scalar_at($word); }\n    }; }\n'
 block+=''.join(f'    scalar_word_case!({kind}_scalar_w{w}, {w});\n' for w in range(9))+finish
 if begin in s:
  a=s.index(begin,start);b=s.index(finish,a)+len(finish);new=s[:a]+block+s[b:]
 else:new=s[:end]+'\n'+block+s[end:]
 if check:assert new==s,file
 else:p.write_text(new)
