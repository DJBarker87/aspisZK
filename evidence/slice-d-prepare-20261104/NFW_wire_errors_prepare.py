"""Broaden the local verify cut from Public to every WireError payload."""
from pathlib import Path
import json,hashlib,difflib
E=Path(__file__).resolve().parent
x=json.loads((E/'NFW_NATIVE_INPUTS.json').read_text());n='crates/aspis-r1-cost-probe/src/NFW_prefix.rs';old=x[n]
a='Err(crate::r1_wire::Error::Public)'
b='''{use crate::r1_wire::Error as W;let choice:u8=kani::any();let row:u8=kani::any();let actual:u8=kani::any();let value:usize=kani::any();Err(match choice%11{0=>W::Allocation,1=>W::RowOrder{expected:row,actual},2=>W::InvalidRow,3=>W::Tag{row},4=>W::Length{row},5=>W::NonCanonical{row,value},6=>W::Boundary{round:value},7=>W::Terminal,8=>W::EqualCirclePoints,9=>W::TrailingBytes,_=>W::Public})}'''
assert old.count(a)==1
x[n]=old.replace(a,b);(E/'NFW_NATIVE_INPUTS.json').write_text(json.dumps(x,indent=1)+'\n')
pins=json.loads((E/'NFW_SOURCE_PINS.json').read_text());pins[n]=hashlib.sha256(x[n].encode()).hexdigest();(E/'NFW_SOURCE_PINS.json').write_text(json.dumps(pins,indent=1)+'\n')
(E/'NFW_prefix_wire_errors.rs.txt').write_text(x[n]);(E/'NFW_prefix_wire_errors.patch').write_text(''.join(difflib.unified_diff(old.splitlines(True),x[n].splitlines(True),fromfile='a/'+n,tofile='b/'+n)))
(E/'NFW_WIRE_ERROR_SCOPE.json').write_text(json.dumps(dict(change='Every WireError constructor and arbitrary full u8/usize payload, replacing fixed Public fixture only',same_property=True,stricter_domain=True,not_row_credit=True,paired_model='NFW_ErrorReferenceEq.semantic',source_sha256=pins[n]),indent=1)+'\n')
