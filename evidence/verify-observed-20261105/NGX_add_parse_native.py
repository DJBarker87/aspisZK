from pathlib import Path
import json,hashlib,subprocess
E=Path(__file__).resolve().parent;p=E/'NGX_native.rs.txt';s=p.read_text();assert 'fn parse_control' not in s
frozen=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:crates/aspis-r1-cost-probe/src/r1_wire.rs'],text=True)
def body(name):
 start=frozen.index('pub fn '+name+'(');at=frozen.index('{',start);d=1;i=at+1
 while d:
  d+=(frozen[i]=='{')-(frozen[i]=='}');i+=1
 return frozen[start:i],frozen[at:i]
original,b=body('parse_record');assert b.count('validate_record_fields(row, payload)?;')==1
cut=b.replace('validate_record_fields(row, payload)?;','validate_cut(row, payload, log)?;')
s+='''
fn any_error()->Error {let tag:u8=kani::any();kani::assume(tag<=10);let row:u8=kani::any();let actual:u8=kani::any();let n:usize=kani::any();match tag {0=>Error::Allocation,1=>Error::RowOrder{expected:row,actual},2=>Error::InvalidRow,3=>Error::Tag{row},4=>Error::Length{row},5=>Error::NonCanonical{row,value:n},6=>Error::Boundary{round:n},7=>Error::Terminal,8=>Error::EqualCirclePoints,9=>Error::TrailingBytes,_=>Error::Public}}
struct ValidateLog {calls:usize,row:u8,ptr:*const u8,length:usize,fail:bool,error:Error}
fn validate_cut(row:u8,payload:&[u8],log:&mut ValidateLog)->Result<(),Error> {log.calls+=1;log.row=row;log.ptr=payload.as_ptr();log.length=payload.len();if log.fail {Err(log.error)}else{Ok(())}}
fn parse_control<'a>(row:u8,record:&'a[u8],log:&mut ValidateLog)->Result<&'a[u8],Error>
'''+cut+'''
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
'''
p.write_text(s)
o=json.loads((E/'NGX_OVERLAY.json').read_text());(E/'NGX_SOURCE_PINS.json').write_text(json.dumps({p:hashlib.sha256((E/n).read_bytes()).hexdigest() for p,n in o.items()},indent=1))
(E/'NGX_PARSE_CUT.json').write_text(json.dumps(dict(frozen_body_sha256=hashlib.sha256(original.encode()).hexdigest(),original_body=original,cut_body=cut,only_substitution='validate_record_fields(row,payload) -> validate_cut(row,payload,log)',callee='TX1:154',domain='payload length<=3712, all raw bytes; domain follows actual row_shape and passing length gate',native_domain='arbitrary u8 row; record length0..3717; header fully arbitrary; child full Error including every u8/usize payload'),indent=1))
