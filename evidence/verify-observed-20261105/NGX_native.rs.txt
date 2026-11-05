use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
#[derive(Clone,Copy)]
struct Hash(u64);
impl aspis_core::Digest32 for Hash { fn digest(&self,_parts:&[&[u8]])->[u8;32] { panic!("state accessor must not hash") } }
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn state_value() {
 let state:[u8;32]=kani::any(); let hash:u64=kani::any(); let next:u8=kani::any();
 let t=SemanticTranscript{state,hash:Hash(hash),next_row:next};
 let out=t.state();let i:usize=kani::any();kani::assume(i<32);
 assert!((out[i]==state[i])!=cfg!(NGX_invert));
 assert_eq!(t.state[i],state[i]);assert_eq!(t.hash.0,hash);assert_eq!(t.next_row,next);
}

struct Oracle { calls:usize, row:u8, initial:[u8;32], replies:[[u8;32];3], payload:*const u8, length:usize }
#[derive(Clone,Copy)]
struct OracleHash<'a>(&'a core::cell::RefCell<Oracle>);
impl aspis_core::Digest32 for OracleHash<'_> {
 fn digest(&self,parts:&[&[u8]])->[u8;32] {
  let mut o=self.0.borrow_mut();let n=o.calls;assert!(n<3);
  if n==0 {
   assert_eq!(parts.len(),3);assert_eq!(parts[0],&o.initial);
   assert_eq!(parts[1],&[0,160+o.row]);assert_eq!(parts[2].as_ptr(),o.payload);assert_eq!(parts[2].len(),o.length);
  } else {
   assert_eq!(parts.len(),2);assert_eq!(parts[0],&o.replies[0]);assert_eq!(parts[1],&[n as u8]);
  }
  o.calls+=1;o.replies[n]
 }
}
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn sample_value() {
 let state:[u8;32]=kani::any();let replies:[[u8;32];3]=kani::any();let row:u8=kani::any();kani::assume(row<=26);
 let next:u8=kani::any();let length:usize=kani::any();kani::assume(length<=3717);
 let mut payload=alloc::vec![0u8;length];let k:usize=kani::any();
 if length>0 {kani::assume(k<length);payload[k]=kani::any();}
 let oldbyte=if length>0 {payload[k]}else{0};
 let local=core::cell::RefCell::new(Oracle{calls:0,row,initial:state,replies,payload:payload.as_ptr(),length});
 let mut t=SemanticTranscript{state,hash:OracleHash(&local),next_row:next};
 let out=t.sample_block_validated(row,&payload);
 let i:usize=kani::any();kani::assume(i<32);
 if row!=next {assert!(matches!(out,Err(Error::RowOrder{expected,actual}) if expected==next&&actual==row));assert_eq!(local.borrow().calls,0);assert_eq!(t.state[i],state[i]);assert_eq!(t.next_row,next);}
 else {let out=out.unwrap();assert!((out[i]==replies[1][i])!=cfg!(NGX_invert));assert_eq!(t.state[i],replies[2][i]);assert_eq!(t.next_row,row+1);assert_eq!(local.borrow().calls,3);}
 assert!(core::ptr::eq(t.hash.0,&local));if length>0 {assert_eq!(payload[k],oldbyte);}
}

struct NewOracle { calls:usize, root:[u8;32],reply:[u8;32],payload:*const u8,length:usize }
#[derive(Clone,Copy)] struct NewHash<'a>(&'a core::cell::RefCell<NewOracle>);
impl aspis_core::Digest32 for NewHash<'_> {
 fn digest(&self,parts:&[&[u8]])->[u8;32] {
  let mut o=self.0.borrow_mut();assert_eq!(o.calls,0);assert_eq!(parts.len(),5);
  assert_eq!(parts[0].as_ptr(),DOMAIN.as_ptr());assert_eq!(parts[0].len(),DOMAIN.len());assert_eq!(parts[1],&[0]);
  assert_eq!(parts[2],&(o.length as u32).to_le_bytes());
  assert_eq!(parts[3].as_ptr(),o.payload);assert_eq!(parts[3].len(),o.length);
  assert_eq!(parts[4],&o.root);o.calls+=1;o.reply
 }
}
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn new_value() {
 let root:[u8;32]=kani::any();let reply:[u8;32]=kani::any();let length:usize=kani::any();kani::assume(length<=57607);
 let mut public=alloc::vec![0u8;length];let k:usize=kani::any();if length>0 {kani::assume(k<length);public[k]=kani::any();}let oldbyte=if length>0 {public[k]}else{0};
 let local=core::cell::RefCell::new(NewOracle{calls:0,root,reply,payload:public.as_ptr(),length});
 let out=SemanticTranscript::new(NewHash(&local),&public,&root).unwrap();let i:usize=kani::any();kani::assume(i<32);
 assert!((out.state[i]==reply[i])!=cfg!(NGX_invert));assert_eq!(out.next_row,0);assert!(core::ptr::eq(out.hash.0,&local));assert_eq!(local.borrow().calls,1);if length>0 {assert_eq!(public[k],oldbyte);}
}
// Exact first stage of frozen new, lifted to an arbitrary length to cover the
// otherwise physically unallocatable >u32 rejection. No byte is fabricated.
fn new_length(length:usize)->Result<u32,Error> {let length=u32::try_from(length).map_err(|_|Error::Public)?;Ok(length)}
#[kani::proof]
fn new_length_value() {
 let length:usize=kani::any();let got=new_length(length);
 if length>u32::MAX as usize {assert!((matches!(got,Err(Error::Public)))!=cfg!(NGX_invert));}
 else {assert!((got==Ok(length as u32))!=cfg!(NGX_invert));}
}

#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn payload_value() {
 let backing=alloc::vec![0u8;17000];
 let records:[&[u8];27]=core::array::from_fn(|_|{let start:usize=kani::any();let length:usize=kani::any();kani::assume(start<=13000&&length>=5&&length<=3717);&backing[start..start+length]});
 let root:&[u8;32]=(&backing[..32]).try_into().unwrap();
 let p=Prefix{c1_root:root,records};let row:u8=kani::any();let got=p.payload(row);
 if row>=27 {assert!(matches!(got,Err(Error::InvalidRow)));}
 else {let original=p.records[row as usize];let out=got.unwrap();assert_eq!(out.as_ptr(),unsafe{original.as_ptr().add(5)});assert!((out.len()==original.len()-5)!=cfg!(NGX_invert));}
}

fn any_error()->Error {let tag:u8=kani::any();kani::assume(tag<=10);let row:u8=kani::any();let actual:u8=kani::any();let n:usize=kani::any();match tag {0=>Error::Allocation,1=>Error::RowOrder{expected:row,actual},2=>Error::InvalidRow,3=>Error::Tag{row},4=>Error::Length{row},5=>Error::NonCanonical{row,value:n},6=>Error::Boundary{round:n},7=>Error::Terminal,8=>Error::EqualCirclePoints,9=>Error::TrailingBytes,_=>Error::Public}}
struct ValidateLog {calls:usize,row:u8,ptr:*const u8,length:usize,fail:bool,error:Error}
fn validate_cut(row:u8,payload:&[u8],log:&mut ValidateLog)->Result<(),Error> {log.calls+=1;log.row=row;log.ptr=payload.as_ptr();log.length=payload.len();if log.fail {Err(log.error)}else{Ok(())}}
fn parse_control<'a>(row:u8,record:&'a[u8],log:&mut ValidateLog)->Result<&'a[u8],Error>
{
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
        validate_cut(row, payload, log)?;
    }
    Ok(payload)
}
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn parse_record_value() {
 let row:u8=kani::any();let length:usize=kani::any();kani::assume(length<=3717);let header:[u8;5]=kani::any();
 let mut record=alloc::vec![0u8;length];if length>=5 {let mut i=0;while i<5 {record[i]=header[i];i+=1;}}
 let fail:bool=kani::any();let error=any_error();let mut log=ValidateLog{calls:0,row:255,ptr:core::ptr::null(),length:0,fail,error};
 let out=parse_control(row,&record,&mut log);let mut validation=false;
 let expected=match row_shape(row) {None=>Some(Error::InvalidRow),Some((tag,size))=> {
  if length!=5+size {Some(Error::Length{row})}else if header[0]!=tag {Some(Error::Tag{row})}
  else if u32::from_le_bytes([header[1],header[2],header[3],header[4]]) as usize!=size {Some(Error::Length{row})}
  else if row>=14 {validation=true;if fail {Some(error)}else{None}} else {None}
 }};
 let correct=match(out,expected) {(Err(a),Some(b))=>a==b,(Ok(payload),None)=>payload.as_ptr()==unsafe{record.as_ptr().add(5)}&&payload.len()==length-5,_=>false};
 assert!(correct!=cfg!(NGX_invert));assert_eq!(log.calls,validation as usize);
 if validation {assert_eq!(log.row,row);assert_eq!(log.ptr,unsafe{record.as_ptr().add(5)});assert_eq!(log.length,length-5);assert!(log.length<=3712);}
}

struct RecordLog {calls:usize,row:u8,ptr:*const u8,length:usize,fail:bool,error:Error}
fn record_cut<'a>(row:u8,framed:&'a[u8],log:&mut RecordLog)->Result<&'a[u8],Error> {log.calls+=1;log.row=row;log.ptr=framed.as_ptr();log.length=framed.len();if log.fail {Err(log.error)}else{Ok(&framed[5..])}}
fn record_at_control<'a>(bytes:&'a[u8],row:u8,offset:usize,log:&mut RecordLog)->Result<(&'a[u8],usize),Error>
{
    let length = 5 + row_shape(row).unwrap().1;
    let framed = bytes
        .get(offset..offset + length)
        .ok_or(Error::Length { row })?;
    record_cut(row, framed, log)?;
    Ok((framed, offset + length))
}
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn record_at_value() {
 let n:usize=kani::any();kani::assume(n<=57607);let bytes=alloc::vec![0u8;n];let offset:usize=kani::any();kani::assume(offset<=57607);let row:u8=kani::any();kani::assume(row<=26);
 let fail:bool=kani::any();let error=any_error();let mut log=RecordLog{calls:0,row:255,ptr:core::ptr::null(),length:0,fail,error};let out=record_at_control(&bytes,row,offset,&mut log);
 let length=5+row_shape(row).unwrap().1;let end=offset+length;let inside=end<=n;
 let correct=match out {Err(e)=>e==if !inside {Error::Length{row}}else{error}&&(!inside||fail),Ok((frame,next))=>inside&&!fail&&next==end&&frame.len()==length&&frame.as_ptr()==unsafe{bytes.as_ptr().add(offset)}};
 assert!(correct!=cfg!(NGX_invert));assert_eq!(log.calls,inside as usize);
 if inside {assert_eq!(log.row,row);assert_eq!(log.ptr,unsafe{bytes.as_ptr().add(offset)});assert_eq!(log.length,length);assert!(log.length<=3717&&log.length>=5);}
}

#[kani::proof]
fn domain_value() {
 let expected:&[u8]=b"UNPROVED:R1:PRIVATE-SALTED:SEMANTIC:P3";let i:usize=kani::any();kani::assume(i<38);
 assert_eq!(DOMAIN.len(),38);assert!((DOMAIN[i]==expected[i])!=cfg!(NGX_invert));
}

struct PrefixLog {calls:usize,fail_at:usize,error:Error,rows:[u8;27],offsets:[usize;27],lengths:[usize;27]}
fn prefix_at_cut<'a>(bytes:&'a[u8],row:u8,offset:usize,log:&mut PrefixLog)->Result<(&'a[u8],usize),Error> {
 let call=log.calls;assert!(call<27);log.calls+=1;log.rows[call]=row;log.offsets[call]=offset;
 assert!(row<=26&&offset<=57607&&bytes.len()<=57607);
 let length=5+row_shape(row).unwrap().1;log.lengths[call]=length;let end=offset+length;
 let frame=bytes.get(offset..end).ok_or(Error::Length{row})?;
 if call==log.fail_at {Err(log.error)}else{Ok((frame,end))}
}
fn prefix_control<'a>(bytes:&'a[u8],log:&mut PrefixLog)->Result<Prefix<'a>,Error>
{
        if bytes.len() < 32 {
            return Err(Error::Length { row: 0 });
        }
        let c1_root = match bytes[..32].try_into() {
            Ok(root) => root,
            Err(_) => return Err(Error::Length { row: 0 }),
        };
        let (r0, offset) = prefix_at_cut(bytes, 0, 32, log)?;
        let (r1, offset) = prefix_at_cut(bytes, 1, offset, log)?;
        let (r2, offset) = prefix_at_cut(bytes, 2, offset, log)?;
        let (r3, offset) = prefix_at_cut(bytes, 3, offset, log)?;
        let (r4, offset) = prefix_at_cut(bytes, 4, offset, log)?;
        let (r5, offset) = prefix_at_cut(bytes, 5, offset, log)?;
        let (r6, offset) = prefix_at_cut(bytes, 6, offset, log)?;
        let (r7, offset) = prefix_at_cut(bytes, 7, offset, log)?;
        let (r8, offset) = prefix_at_cut(bytes, 8, offset, log)?;
        let (r9, offset) = prefix_at_cut(bytes, 9, offset, log)?;
        let (r10, offset) = prefix_at_cut(bytes, 10, offset, log)?;
        let (r11, offset) = prefix_at_cut(bytes, 11, offset, log)?;
        let (r12, offset) = prefix_at_cut(bytes, 12, offset, log)?;
        let (r13, offset) = prefix_at_cut(bytes, 13, offset, log)?;
        let (r14, offset) = prefix_at_cut(bytes, 14, offset, log)?;
        let (r15, offset) = prefix_at_cut(bytes, 15, offset, log)?;
        let (r16, offset) = prefix_at_cut(bytes, 16, offset, log)?;
        let (r17, offset) = prefix_at_cut(bytes, 17, offset, log)?;
        let (r18, offset) = prefix_at_cut(bytes, 18, offset, log)?;
        let (r19, offset) = prefix_at_cut(bytes, 19, offset, log)?;
        let (r20, offset) = prefix_at_cut(bytes, 20, offset, log)?;
        let (r21, offset) = prefix_at_cut(bytes, 21, offset, log)?;
        let (r22, offset) = prefix_at_cut(bytes, 22, offset, log)?;
        let (r23, offset) = prefix_at_cut(bytes, 23, offset, log)?;
        let (r24, offset) = prefix_at_cut(bytes, 24, offset, log)?;
        let (r25, offset) = prefix_at_cut(bytes, 25, offset, log)?;
        let (r26, offset) = prefix_at_cut(bytes, 26, offset, log)?;
        if offset != bytes.len() {
            return Err(Error::TrailingBytes);
        }
        Ok(Prefix {
            c1_root,
            records: [
                r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17,
                r18, r19, r20, r21, r22, r23, r24, r25, r26,
            ],
        })
    }
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn prefix_value() {
 let n:usize=kani::any();kani::assume(n<=57607);let bytes=alloc::vec![0u8;n];let fail_at:usize=kani::any();kani::assume(fail_at<=27);let error=any_error();
 let starts:[usize;27]=[32,37,42,79,84,89,94,99,104,109,114,119,124,129,134,171,1072,1973,2874,3775,4676,5577,6478,7379,8280,9181,12898];let widths:[usize;27]=[5,5,37,5,5,5,5,5,5,5,5,5,5,5,37,901,901,901,901,901,901,901,901,901,901,3717,933];
 let mut log=PrefixLog{calls:0,fail_at,error,rows:[255;27],offsets:[0;27],lengths:[0;27]};let out=prefix_control(&bytes,&mut log);
 let mut stop=0usize;if n>=32 {while stop<27 {if starts[stop]+widths[stop]>n||stop==fail_at {break;}stop+=1;}}
 let expected_calls=if n<32 {0}else if stop<27 {stop+1}else{27};assert_eq!(log.calls,expected_calls);
 let k:usize=kani::any();kani::assume(k<27);
 let correct=if n<32 {matches!(out,Err(Error::Length{row:0}))}
 else if stop<27 {let expected=if starts[stop]+widths[stop]>n {Error::Length{row:stop as u8}}else{error};matches!(out,Err(e) if e==expected)}
 else if n!=13831 {matches!(out,Err(Error::TrailingBytes))}
 else {match out {Ok(prefix)=>prefix.c1_root.as_ptr()==bytes.as_ptr()&&prefix.records[k].as_ptr()==unsafe{bytes.as_ptr().add(starts[k])}&&prefix.records[k].len()==widths[k],Err(_)=>false}};
 assert!(correct!=cfg!(NGX_invert));if k<log.calls {assert_eq!(log.rows[k],k as u8);assert_eq!(log.offsets[k],starts[k]);assert_eq!(log.lengths[k],widths[k]);}
}
