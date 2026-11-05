from pathlib import Path
import sys,json,hashlib
sys.dont_write_bytecode=True
from NIZ_native_prepare import stage,attrs,account_setup
from NIZ_frozen_identity import frozen
E=Path(__file__).resolve().parent
mode=sys.argv[1]; negative=mode=='negative'
p='programs/aspis-pool/src/processor.rs';text=frozen()[p].decode()
start=text.index('            if accounts[left].key == accounts[right].key {',text.index('pub(crate) fn require_unique_accounts'))
end=text.index('            }',start)+len('            }')
body=text[start:end]
assert body.count('return Err(ProgramError::InvalidArgument);')==1
selected='Ok(())' if negative else '(||->Result<(),ProgramError>{'+body+'\nOk(())})()'
s="use solana_program::{pubkey::Pubkey,program_error::ProgramError}; struct NIZ_Selected<'a>{key:&'a Pubkey} let k0=Pubkey::new_from_array(kani::any());let k1=Pubkey::new_from_array(kani::any()); let accounts=[NIZ_Selected{key:&k0},NIZ_Selected{key:&k1}];"+ ' let left=0usize;let right=1usize;let same=accounts[left].key==accounts[right].key;let result:Result<(),ProgramError>='+selected+';assert!(result==if same{Err(ProgramError::InvalidArgument)}else{Ok(())});'
source=attrs()+'\n#[kani::proof]\nfn certificate(){'+s+'}\n'
(E/'NIZ_UNIQUE_STEP.json').write_text(json.dumps(dict(path=p,source_sha256=hashlib.sha256(text.encode()).hexdigest(),body=body,body_sha256=hashlib.sha256(body.encode()).hexdigest(),method='One native nested-loop body on arbitrary selected keys, not a whole-buffer replay; indices represent the selected ordered pair. Lean must compose all lexicographic pairs.',production_credit=False),indent=2))
stage(p,source,'original uniqueness inner iteration with key-only receiver projection',mode,'Arbitrary selected account keys, exact native comparison and ProgramError; payload values unused.','Key-only receiver projection is not an AccountInfo carrier certificate; full source-loop association and caller dominance remain OPEN.',dict(expected_verdict='FAIL' if negative else 'PASS',member='require_unique_accounts',control='skip comparison' if negative else None))
