from pathlib import Path
import json
from NFU_add_inputs import update
E=Path(__file__).resolve().parent;p='programs/r1-cost-probe/src/NFU_owned.rs';s=json.loads((E/'NFU_NATIVE_INPUTS.json').read_text())[p]
a='let expected=if a.is_signer||a.is_writable||a.executable{Err(ProgramError::InvalidAccountData)}else{Ok(())};assert!((r==expected) != cfg!(NFU_invert));'
b='let good=!(a.is_signer||a.is_writable||a.executable);let exact=if good{matches!(r,Ok(()))}else{matches!(r,Err(ProgramError::InvalidAccountData))};assert!(exact != cfg!(NFU_invert));'
assert s.count(a)==1;update({p:s.replace(a,b)},'NFU_adapter_tag_split')
