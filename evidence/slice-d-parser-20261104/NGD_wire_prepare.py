from pathlib import Path
import json,subprocess
from NGD_add_inputs import update
E=Path(__file__).resolve().parent;C='crates/aspis-r1-cost-probe/src/'
source=subprocess.check_output(['git','show','4bb3b3f:'+C+'r1_wire.rs'],text=True)
code='''use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
#[kani::proof] #[kani::unwind(2)]
fn parse_low_valid(){
 let mut bytes:[u8;37]=kani::any();let row:u8=kani::any();kani::assume(row<14);
 let (tag,size)=row_shape(row).unwrap();bytes[0]=tag;bytes[1]=size as u8;bytes[2]=0;bytes[3]=0;bytes[4]=0;
 let record=&bytes[..5+size];let result=parse_record(row,record);
 let good=match result{Ok(payload)=>payload.as_ptr()==record.as_ptr().wrapping_add(5)&&payload.len()==size,Err(_)=>false};
 assert!(good != cfg!(NGD_invert));
}
fn decode_guard<const N:usize>(which:u8){
 let bytes:[u8;37]=kani::any();let row:u8=kani::any();let offset:usize=kani::any();
 let record=ValidatedRecord{row,framed:&bytes};
 match which{
 0=>kani::assume(row<14),
 1=>kani::assume(row>=14&&offset>usize::MAX/32),
 2=>kani::assume(row>=14&&offset<=usize::MAX/32&&offset*32>usize::MAX-32*N),
 _=>kani::assume(row>=14&&offset<=usize::MAX/32&&offset*32<=usize::MAX-32*N&&offset*32+32*N>32)
 }
 let result=record.decode_k::<N>(offset);
 let good=if row<14{matches!(result,Err(Error::InvalidRow))}else{matches!(result,Err(Error::Length{row:r})if r==row)};
 assert!(good != cfg!(NGD_invert));
}
macro_rules! guard{($name:ident,$n:expr,$w:expr)=>{#[kani::proof]#[kani::unwind(2)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn $name(){decode_guard::<$n>($w)}};}
'''
for n in [1,28,29]:
 for i in range(4):code+=f'guard!(decode{n}_guard{i},{n},{i});\n'
update({C+'r1_wire.rs':source+'\n#[cfg(kani)] #[path="NGD_wire.rs"] mod NGD_wire;\n',C+'NGD_wire.rs':code},'NGD_wire_guards')
