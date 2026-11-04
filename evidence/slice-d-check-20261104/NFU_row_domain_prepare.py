from pathlib import Path
import json
from NFU_add_inputs import update
E=Path(__file__).resolve().parent;p='crates/aspis-r1-cost-probe/src/NFU_wire.rs';s=json.loads((E/'NFU_NATIVE_INPUTS.json').read_text())[p]
a='fn row_contract(){let row:u8=kani::any();let r=ValidatedRecord{row,framed:&[]};let _=r.row();}'
b='fn row_contract(){let bytes:[u8;3717]=kani::any();let start:usize=kani::any();let len:usize=kani::any();kani::assume(start<=3717&&len<=3717-start);let r=ValidatedRecord{row:kani::any(),framed:&bytes[start..start+len]};let _=r.row();}'
assert s.count(a)==1;update({p:s.replace(a,b)},'NFU_row_domain')
