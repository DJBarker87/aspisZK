import sys,json,hashlib
sys.dont_write_bytecode=True
from NIZ_native_prepare import stage,attrs,account_setup
from NIZ_frozen_identity import frozen
mode=sys.argv[1]
p='programs/aspis-pool/src/processor.rs';text=frozen()[p].decode();start=text.index('            if accounts[left].key == accounts[right].key {',text.index('pub(crate) fn require_unique_accounts'));end=text.index('            }',start)+len('            }');body=text[start:end]
# Natural fixed32-byte spec, written without a memcmp call or a loop. No copy stub.
expr=' && '.join(f'a[{i}]==b[{i}]' for i in range(32))
stub='fn NIZ_eq(left:&solana_program::pubkey::Pubkey,right:&solana_program::pubkey::Pubkey)->bool{let a:&[u8]=left.as_ref();let b:&[u8]=right.as_ref();'+expr+'}\n'
selected='Ok(())' if mode=='negative' else '(||->Result<(),ProgramError>{'+body+'\nOk(())})()'
s=account_setup(2)+'let accounts=[a0,a1];let left=0usize;let right=1usize;let same=accounts[left].key==accounts[right].key;let result:Result<(),ProgramError>='+selected+';assert!(result==if same{Err(ProgramError::InvalidArgument)}else{Ok(())});'
source=stub+attrs()+'\n#[kani::stub(solana_program::pubkey::Pubkey::eq,NIZ_eq)]\n#[kani::proof]\nfn certificate(){'+s+'}\n'
stage(p,source,'actual uniqueness comparison with fixed32 key-equality specification cut',mode,'Arbitrary full keys and actual AccountInfo key carriers; byte comparison stub domain exactly valid 32-byte key references.','Equality-stub/host-loop source association and Lean pairing must close before native source credit; full caller prefix/callee scopes still OPEN.',dict(expected_verdict='FAIL' if mode=='negative' else 'PASS',member='require_unique_accounts_comparison',native_args=['--unwind','34'],stub=dict(name='NIZ_eq',domain='all valid Pubkey references, exactly 32 readable bytes',status='OPEN until native/loop association and paired theorem complete')))
