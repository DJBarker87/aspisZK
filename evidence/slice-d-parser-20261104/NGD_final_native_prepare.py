from pathlib import Path
import json
from NGD_add_inputs import update
E=Path(__file__).resolve().parent;p='crates/aspis-r1-cost-probe/src/NGD_compact.rs';s=json.loads((E/'NGD_NATIVE_INPUTS.json').read_text())[p]
s+='''
#[kani::proof]#[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn semantic_low_all(){let row:u8=kani::any();kani::assume(row<14);semantic_cut(row,2);}
fn copy_frame<const N:usize>(){let input:[u8;N]=kani::any();let mut output:[u8;96]=kani::any();let at:usize=kani::any();kani::assume(at<=96-N);let j:usize=kani::any();kani::assume(j<96);let old=output[j];let ptr=output.as_ptr();output[at..at+N].copy_from_slice(&input);let expected=if at<=j&&j<at+N{input[j-at]}else{old};assert!((output[j]==expected&&output.as_ptr()==ptr) != cfg!(NGD_invert));}
macro_rules! copyframe{($name:ident,$n:expr)=>{#[kani::proof]#[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]fn $name(){copy_frame::<$n>()}};}
copyframe!(semantic_header5_frame,5);copyframe!(semantic_payload32_frame,32);
'''
update({p:s},'NGD_final_native_windows')
q=[];i=90
for module,name in [('compact','semantic_low_all'),('compact','semantic_header5_frame'),('compact','semantic_payload32_frame'),('r1_wire','decode_write28'),('r1_wire','decode_write29')]:
 for inv in [0,1]:
  q.append(dict(attempt=f'NGD_K{i:03}',kind='kani',target=module+'::NGD_'+('compact'if module=='compact'else'wire')+'::'+name,exit=inv,env={'NGD_INVERT':'1'}if inv else{}));i+=1
q.append(dict(attempt='NGD_K100',kind='kani',target='r1_wire::NGD_wire::at_invalid_row_panics',exit=1))
(E/'NGD_QUEUE_FINAL_NATIVE.json').write_text(json.dumps(q,indent=2)+'\n')
