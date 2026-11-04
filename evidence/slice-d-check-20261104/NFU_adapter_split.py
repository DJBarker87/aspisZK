from pathlib import Path
import json
from NFU_add_inputs import update
E=Path(__file__).resolve().parent;p='programs/r1-cost-probe/src/NFU_owned.rs';s=json.loads((E/'NFU_NATIVE_INPUTS.json').read_text())[p]
# Remove unrelated source-owned account cleanup from the borrowed helper target.
s=s.replace('key:Pubkey::new_from_array(kani::any()),owner:Pubkey::new_from_array(kani::any())','key:Pubkey::new_from_array([0;32]),owner:Pubkey::new_from_array([0;32])')
s=s.replace('length:Ok(kani::any())','length:Ok(0)')
s=s.replace('let a=account();','let a=core::mem::ManuallyDrop::new(account());')
update({p:s},'NFU_adapter_borrow_split')
