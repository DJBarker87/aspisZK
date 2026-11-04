from pathlib import Path
import json
from NGD_add_inputs import update
E=Path(__file__).resolve().parent;p='crates/aspis-r1-cost-probe/src/NGD_wire.rs';s=json.loads((E/'NGD_NATIVE_INPUTS.json').read_text())[p]
code='''
// CLOSED opaque-Q child, exact natural four-word spec; no multiplication.
fn NGD_decode_le(bytes:&[u8])->Option<QM31>{
 assert_eq!(bytes.len(),16);
 fn word(b:&[u8],i:usize)->u32{u32::from(b[i])|(u32::from(b[i+1])<<8)|(u32::from(b[i+2])<<16)|(u32::from(b[i+3])<<24)}
 let a=word(bytes,0);let b=word(bytes,4);let c=word(bytes,8);let d=word(bytes,12);
 if a>=0x7fffffff||b>=0x7fffffff||c>=0x7fffffff||d>=0x7fffffff{return None;}
 Some(QM31{c0:aspis_core::field::CM31{a:aspis_core::field::M31(a),b:aspis_core::field::M31(b)},c1:aspis_core::field::CM31{a:aspis_core::field::M31(c),b:aspis_core::field::M31(d)}})
}
'''
# Preserve all original harness/function names after K035; change only child cut.
s=s.replace('fn $name(){decode_one::<$b>($r)}};}', '#[kani::stub(QM31::from_le_bytes,NGD_decode_le)]\nfn $name(){decode_one::<$b>($r)}};}')
assert '#[kani::stub(QM31::from_le_bytes,NGD_decode_le)]'in s
update({p:s+code},'NGD_qdecode_cut')
