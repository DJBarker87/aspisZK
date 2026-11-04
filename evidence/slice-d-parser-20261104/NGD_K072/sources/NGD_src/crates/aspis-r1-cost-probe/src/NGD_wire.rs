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
#[kani::stub(QM31::from_le_bytes,NGD_decode_le)]
fn $name(){decode_one::<$b>($r)}};}
one!(decode_one14,37,14);one!(decode_one15,901,15);one!(decode_one25,3717,25);one!(decode_one26,933,26);

// CLOSED opaque-Q child, exact natural four-word spec; no multiplication.
fn NGD_decode_le(bytes:&[u8])->Option<QM31>{
 assert_eq!(bytes.len(),16);
 fn word(b:&[u8],i:usize)->u32{u32::from(b[i])|(u32::from(b[i+1])<<8)|(u32::from(b[i+2])<<16)|(u32::from(b[i+3])<<24)}
 let a=word(bytes,0);let b=word(bytes,4);let c=word(bytes,8);let d=word(bytes,12);
 if a>=0x7fffffff||b>=0x7fffffff||c>=0x7fffffff||d>=0x7fffffff{return None;}
 Some(QM31{c0:aspis_core::field::CM31{a:aspis_core::field::M31(a),b:aspis_core::field::M31(b)},c1:aspis_core::field::CM31{a:aspis_core::field::M31(c),b:aspis_core::field::M31(d)}})
}

#[derive(Clone,Copy)]
struct ParseLog{reply:Result<(),Error>,row:u8,ptr:*const u8,len:usize,calls:usize}
fn validate_capture(row:u8,payload:&[u8],log:&mut ParseLog)->Result<(),Error>{log.row=row;log.ptr=payload.as_ptr();log.len=payload.len();log.calls+=1;log.reply}
fn arbitrary_error()->Error{match kani::any::<u8>()%11{
 0=>Error::Allocation,1=>Error::RowOrder{expected:kani::any(),actual:kani::any()},2=>Error::InvalidRow,
 3=>Error::Tag{row:kani::any()},4=>Error::Length{row:kani::any()},5=>Error::NonCanonical{row:kani::any(),value:kani::any()},
 6=>Error::Boundary{round:kani::any()},7=>Error::Terminal,8=>Error::EqualCirclePoints,9=>Error::TrailingBytes,_=>Error::Public}}
fn native_parse_record<'a>(row: u8, record: &'a [u8], log: &mut ParseLog) -> Result<&'a [u8], Error> {
    let (tag, size) = row_shape(row).ok_or(Error::InvalidRow)?;
    if record.len() != 5 + size {
        return Err(Error::Length { row });
    }
    if record[0] != tag {
        return Err(Error::Tag { row });
    }
    if u32::from_le_bytes([record[1], record[2], record[3], record[4]]) as usize != size {
        return Err(Error::Length { row });
    }
    let payload = &record[5..];
    if row >= 14 {
        validate_capture(row, payload, log)?;
    }
    Ok(payload)
}
fn parse_valid(group:u8){
 let mut bytes:[u8;3717]=kani::any();let row:u8=kani::any();kani::assume(row<27);
 let(tag,size)=row_shape(row).unwrap();bytes[0]=tag;bytes[1]=size as u8;bytes[2]=(size>>8)as u8;bytes[3]=0;bytes[4]=0;
 let reply=if kani::any(){Ok(())}else{Err(arbitrary_error())};
 let mut log=ParseLog{reply,row:0,ptr:core::ptr::null(),len:0,calls:0};
 let record=&bytes[..5+size];let observed:usize=kani::any();kani::assume(observed<5+size);let old=bytes[observed];
 let result=native_parse_record(row,record,&mut log);
 let expected=if row>=14{reply}else{Ok(())};
 let result_ok=match(expected,result){(Ok(()),Ok(payload))=>payload.as_ptr()==bytes.as_ptr().wrapping_add(5)&&payload.len()==size,(Err(e),Err(r))=>e==r,_=>false};
 let call_ok=if row>=14{log.calls==1&&log.row==row&&log.ptr==bytes.as_ptr().wrapping_add(5)&&log.len==size}else{log.calls==0};
 let good=match group{0=>result_ok,1=>call_ok,2=>bytes[observed]==old,_=>false};assert!(good != cfg!(NGD_invert));
}
macro_rules! parsegate{($name:ident,$g:expr)=>{#[kani::proof]#[kani::unwind(35)]#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]fn $name(){parse_valid($g)}};}
parsegate!(parse_valid_result,0);parsegate!(parse_valid_calls,1);parsegate!(parse_valid_frame,2);

// Isolated exact scalar prefix; no value decoding or buffer traversal.
#[kani::proof] #[kani::unwind(2)]
fn decode_scalar_all(){
 let b:[u8;3717]=kani::any();let len:usize=kani::any();kani::assume(5<=len&&len<=3717);
 let row:u8=kani::any();let off:usize=kani::any();let n:usize=kani::any();kani::assume(n==1||n==28||n==29);
 let actual=(||->Result<(),Error>{
  if row<14{return Err(Error::InvalidRow);}
  let byte_offset=off.checked_mul(32).ok_or(Error::Length{row})?;
  let byte_len=n.checked_mul(32).ok_or(Error::Length{row})?;
  let end=byte_offset.checked_add(byte_len).ok_or(Error::Length{row})?;
  let _bytes=ValidatedRecord{row,framed:&b[..len]}.payload().get(byte_offset..end).ok_or(Error::Length{row})?;
  Ok(())})();
 let fits=(off as u128)*32+(n as u128)*32<=(len-5)as u128;
 let expected=if row<14{Err(Error::InvalidRow)}else if fits{Ok(())}else{Err(Error::Length{row})};
 assert!((actual==expected) != cfg!(NGD_invert));
}
#[kani::proof] #[kani::unwind(2)]
fn decode_iterator(){
 let b:[u8;3717]=kani::any();let len:usize=kani::any();kani::assume(5<=len&&len<=3717);
 let n:usize=kani::any();kani::assume(n==1||n==28||n==29);let off:usize=kani::any();kani::assume(off<=116&&32*(off+n)<=len-5);
 let i:usize=kani::any();kani::assume(i<=n);
 let record=ValidatedRecord{row:25,framed:&b[..len]};let payload=record.payload();let selected=&payload[32*off..32*(off+n)];
 let mut it=selected.chunks_exact(32).enumerate();if i>0{let(j,_)=it.nth(i-1).unwrap();assert_eq!(j,i-1);}
 let before=it.len();let good=match it.next(){None=>i==n&&before==0,Some((value,part))=>i<n&&value==i&&part.len()==32&&part.as_ptr()==b.as_ptr().wrapping_add(5+32*(off+i))&&before==n-i&&it.len()==n-i-1&&off+value<116};
 assert!(good != cfg!(NGD_invert));
}
fn raw_q()->QM31{QM31{c0:aspis_core::field::CM31{a:aspis_core::field::M31(kani::any()),b:aspis_core::field::M31(kani::any())},c1:aspis_core::field::CM31{a:aspis_core::field::M31(kani::any()),b:aspis_core::field::M31(kani::any())}}}
fn same_q(a:QM31,b:QM31)->bool{a.c0.a.0==b.c0.a.0&&a.c0.b.0==b.c0.b.0&&a.c1.a.0==b.c1.a.0&&a.c1.b.0==b.c1.b.0}
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(QM31::from_le_bytes,NGD_decode_le)]
fn decode_typed_write(){
 let b:[u8;37]=kani::any();let row:u8=kani::any();kani::assume(row>=14);
 let mut out=[raw_q(),raw_q(),raw_q()];let j:usize=kani::any();kani::assume(j<3);let old=out[j];
 let actual=ValidatedRecord{row,framed:&b}.decode_k::<1>(0);let expected=NGD_decode_le(&b[5..21]);
 let good=match(actual,expected){(Ok([q]),Some(v))=>{out[1]=q;same_q(q,v)&&same_q(out[j],if j==1{v}else{old})},(Err(Error::NonCanonical{row:r,value:0}),None)=>r==row&&same_q(out[j],old),_=>false};
 assert!(good != cfg!(NGD_invert));
}

fn parse_capture<'a>(row:u8,framed:&'a[u8],log:&mut ParseLog)->Result<&'a[u8],Error>{
 log.row=row;log.ptr=framed.as_ptr();log.len=framed.len();log.calls+=1;
 match log.reply{Ok(())=>Ok(&framed[5..]),Err(e)=>Err(e)}
}
fn native_parse_at<'a>(bytes:&'a[u8],row:u8,offset:usize,log:&mut ParseLog)->Result<(&'a[u8],usize),Error> {
    let length = 5 + row_shape(row).unwrap().1;
    let framed = bytes
        .get(offset..offset + length)
        .ok_or(Error::Length { row })?;
    parse_capture(row, framed, log)?;
    Ok((framed, offset + length))
}
fn at_g(group:u8){
 let bytes:[u8;13831]=kani::any();let n:usize=kani::any();kani::assume(n<=13831);
 let row:u8=kani::any();kani::assume(row<27);let offset:usize=kani::any();let length=5+row_shape(row).unwrap().1;kani::assume(offset<=usize::MAX-length);
 let reply=if kani::any(){Ok(())}else{Err(arbitrary_error())};let mut log=ParseLog{reply,row:0,ptr:core::ptr::null(),len:0,calls:0};
 let result=native_parse_at(&bytes[..n],row,offset,&mut log);let fits=offset<=n&&length<=n-offset;
 let good_result=if fits{match(reply,result){(Ok(()),Ok((framed,end)))=>framed.as_ptr()==bytes.as_ptr().wrapping_add(offset)&&framed.len()==length&&end==offset+length,(Err(e),Err(r))=>e==r,_=>false}}else{matches!(result,Err(Error::Length{row:r})if r==row)};
 let good_call=if fits{log.calls==1&&log.row==row&&log.ptr==bytes.as_ptr().wrapping_add(offset)&&log.len==length}else{log.calls==0};
 assert!((if group==0{good_result}else{good_call}) != cfg!(NGD_invert));
}
macro_rules! atgate{($name:ident,$g:expr)=>{#[kani::proof]#[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]fn $name(){at_g($g)}};}
atgate!(at_full_result,0);atgate!(at_original_window,1);

fn decode_source_step<const N:usize>(out:&mut[QM31;N],part:&[u8],row:u8,offset_values:usize,value:usize)->Result<(),Error>{
 out[value]=QM31::from_le_bytes(&part[..16]).ok_or(Error::NonCanonical{row,value:offset_values+value})?;Ok(())
}
fn observe_write<const N:usize>(out:&mut[QM31;N]){
 let part:[u8;32]=kani::any();let row:u8=kani::any();kani::assume(row>=14);let offset:usize=kani::any();let index:usize=kani::any();kani::assume(index<N&&offset<=116&&offset+index<116);
 let j:usize=kani::any();kani::assume(j<N);let old=out[j];let expect=NGD_decode_le(&part[..16]);let result=decode_source_step(out,&part,row,offset,index);
 let good=match(result,expect){(Ok(()),Some(q))=>same_q(out[j],if j==index{q}else{old}),(Err(Error::NonCanonical{row:r,value:v}),None)=>r==row&&v==offset+index&&same_q(out[j],old),_=>false};assert!(good != cfg!(NGD_invert));
}
#[kani::proof]#[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(QM31::from_le_bytes,NGD_decode_le)]
fn decode_write28(){let mut out=[raw_q(),raw_q(),raw_q(),raw_q(),raw_q(),raw_q(),raw_q(),raw_q(),raw_q(),raw_q(),raw_q(),raw_q(),raw_q(),raw_q(),raw_q(),raw_q(),raw_q(),raw_q(),raw_q(),raw_q(),raw_q(),raw_q(),raw_q(),raw_q(),raw_q(),raw_q(),raw_q(),raw_q()];observe_write(&mut out);}
#[kani::proof]#[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(QM31::from_le_bytes,NGD_decode_le)]
fn decode_write29(){let mut out=[raw_q(),raw_q(),raw_q(),raw_q(),raw_q(),raw_q(),raw_q(),raw_q(),raw_q(),raw_q(),raw_q(),raw_q(),raw_q(),raw_q(),raw_q(),raw_q(),raw_q(),raw_q(),raw_q(),raw_q(),raw_q(),raw_q(),raw_q(),raw_q(),raw_q(),raw_q(),raw_q(),raw_q(),raw_q()];observe_write(&mut out);}

#[kani::proof]#[kani::unwind(2)]
fn at_invalid_row_panics(){let bytes:[u8;32]=kani::any();let row:u8=kani::any();kani::assume(row>=27);let _=parse_record_at(&bytes,row,0);}
