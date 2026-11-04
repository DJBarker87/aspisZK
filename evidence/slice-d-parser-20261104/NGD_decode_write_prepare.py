from pathlib import Path
import json
from NGD_add_inputs import update
E=Path(__file__).resolve().parent;p='crates/aspis-r1-cost-probe/src/NGD_wire.rs';s=json.loads((E/'NGD_NATIVE_INPUTS.json').read_text())[p]
s+='''
fn decode_source_step<const N:usize>(out:&mut[QM31;N],part:&[u8],row:u8,offset_values:usize,value:usize)->Result<(),Error>{
 out[value]=QM31::from_le_bytes(&part[..16]).ok_or(Error::NonCanonical{row,value:offset_values+value})?;Ok(())
}
fn observe_write<const N:usize>(out:&mut[QM31;N]){
 let part:[u8;32]=kani::any();let row:u8=kani::any();kani::assume(row>=14);let offset:usize=kani::any();let index:usize=kani::any();kani::assume(index<N&&offset<=116&&offset+index<116);
 let j:usize=kani::any();kani::assume(j<N);let old=out[j];let expect=NGD_decode_le(&part[..16]);let result=decode_source_step(out,&part,row,offset,index);
 let good=match(result,expect){(Ok(()),Some(q))=>same_q(out[j],if j==index{q}else{old}),(Err(Error::NonCanonical{row:r,value:v}),None)=>r==row&&v==offset+index&&same_q(out[j],old),_=>false};assert!(good != cfg!(NGD_invert));
}
'''
for n in [28,29]:
 s+=f'''#[kani::proof]#[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(QM31::from_le_bytes,NGD_decode_le)]
fn decode_write{n}(){{let mut out=[{','.join('raw_q()'for _ in range(n))}];observe_write(&mut out);}}
'''
s+='''
#[kani::proof]#[kani::unwind(2)]
fn at_invalid_row_panics(){let bytes:[u8;32]=kani::any();let row:u8=kani::any();kani::assume(row>=27);let _=parse_record_at(&bytes,row,0);}
'''
update({p:s},'NGD_decode_array_steps')
