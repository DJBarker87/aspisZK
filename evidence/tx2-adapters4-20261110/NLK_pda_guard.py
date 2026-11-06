from NLK_native import *
P='programs/r1-cost-probe/src/r1_pool_adapter.rs'
def attempt(a,mode):
 source=json.loads((E/'NLK_PUBKEY_SOURCE.json').read_text());s=source['text'];start=s.index('        if seeds.len() > MAX_SEEDS',s.index('    pub fn create_program_address'));end=s.index('        // Perform the calculation inline',start);segment=s[start:end]
 assert 'pub const MAX_SEEDS: usize = 16;' in s and 'pub const MAX_SEED_LEN: usize = 32;' in s
 text='''use super::*;
use solana_program::pubkey::PubkeyError;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
const MAX_SEEDS:usize=16;const MAX_SEED_LEN:usize=32;
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn stage(){let raw:[u8;33]=kani::any();let lengths:[usize;17]=kani::any();for i in 0..17{kani::assume(lengths[i]<=33);}let count:usize=kani::any();kani::assume(count<=17);let all:[&[u8];17]=core::array::from_fn(|i|&raw[..lengths[i]]);let seeds=&all[..count];let mut suffix=0u8;
let out=(||->Result<(),PubkeyError>{BODY suffix+=1;Ok(())})();CORRUPT
let valid=count<=16&&(0..count).all(|i|lengths[i]<=32);
assert!(out==if valid{Ok(())}else{Err(PubkeyError::MaxSeedLengthExceeded)}&&suffix==if valid{1}else{0},"pinned SDK ordered seed bounds reject before syscall and preserve prefix");}
'''.replace('BODY',segment).replace('CORRUPT','suffix^=1;' if mode=='inverse' else '')
 mod='NLK_pda_guard'
 (E/(a+'_CUT.json')).write_text(json.dumps(dict(source=source['path'],source_sha256=source['sha256'],segment=segment,mode=mode,domain='0..17 descriptors, lengths0..33, arbitrary data; all actual callers have2..5 descriptors and lengths<=32 by NLK_PdaSites',limits='bounds prelude only; no inline SHA/curve work, no PDA value claim'),indent=1)+'\n')
 (E/(a+'.patch')).write_text('--- /dev/null\n+++ b/'+mod+'.rs\n@@ -0,0 +1,'+str(len(text.splitlines()))+' @@\n'+''.join('+'+l for l in text.splitlines(True)))
 return submit(a,'r1_pool_adapter::'+mod+'::stage',P,mod,text,mode)
if __name__=='__main__':
 import sys
 attempt(*sys.argv[1:])
