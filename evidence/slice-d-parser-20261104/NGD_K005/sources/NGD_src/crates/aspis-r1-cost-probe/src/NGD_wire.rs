use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
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
guard!(decode1_guard0,1,0);
guard!(decode1_guard1,1,1);
guard!(decode1_guard2,1,2);
guard!(decode1_guard3,1,3);
guard!(decode28_guard0,28,0);
guard!(decode28_guard1,28,1);
guard!(decode28_guard2,28,2);
guard!(decode28_guard3,28,3);
guard!(decode29_guard0,29,0);
guard!(decode29_guard1,29,1);
guard!(decode29_guard2,29,2);
guard!(decode29_guard3,29,3);

fn decode_one<const B:usize>(row:u8){
 let bytes:[u8;B]=kani::any();let offset:usize=kani::any();kani::assume(offset<(B-5)/32);
 let record=ValidatedRecord{row,framed:&bytes};let result=record.decode_k::<1>(offset);
 let part=&bytes[5+32*offset..5+32*offset+16];
 let a=u32::from_le_bytes([part[0],part[1],part[2],part[3]]);let b=u32::from_le_bytes([part[4],part[5],part[6],part[7]]);
 let c=u32::from_le_bytes([part[8],part[9],part[10],part[11]]);let d=u32::from_le_bytes([part[12],part[13],part[14],part[15]]);
 let canonical=a<0x7fffffff&&b<0x7fffffff&&c<0x7fffffff&&d<0x7fffffff;
 let good=match result{Ok(q)=>canonical&&q[0].c0.a.0==a&&q[0].c0.b.0==b&&q[0].c1.a.0==c&&q[0].c1.b.0==d,Err(Error::NonCanonical{row:r,value:v})=>!canonical&&r==row&&v==offset,_=>false};
 assert!(good != cfg!(NGD_invert));
}
macro_rules! one{($name:ident,$b:expr,$r:expr)=>{#[kani::proof]#[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn $name(){decode_one::<$b>($r)}};}
one!(decode_one14,37,14);one!(decode_one15,901,15);one!(decode_one25,3717,25);one!(decode_one26,933,26);
