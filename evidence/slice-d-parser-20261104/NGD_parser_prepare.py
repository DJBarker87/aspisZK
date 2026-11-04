"""Prepare full-carrier local-record caller candidates; source-erasure checked."""
from pathlib import Path
import subprocess,json,re,hashlib
from NGD_add_inputs import update
E=Path(__file__).resolve().parent;C='crates/aspis-r1-cost-probe/src/';I=json.loads((E/'NGD_NATIVE_INPUTS.json').read_text());frozen=subprocess.check_output(['git','show','4bb3b3f:'+C+'r1_wire.rs'],text=True)
def function(name):
 a=frozen.index(('pub fn 'if name=='parse_record'else'fn ')+name+'(');start=frozen.index('{',a);depth=1;j=start+1
 while depth:depth+=(frozen[j]=='{')-(frozen[j]=='}');j+=1
 return frozen[a:j]
# Preserve the complete frozen caller, change only the explicit child cut to a
# local-record oracle. Exact erasure and corruptions are a separate checked gate.
original=function('parse_record');native=original.replace('pub fn parse_record(row: u8, record: &[u8]) -> Result<&[u8], Error>',"fn native_parse_record<'a>(row: u8, record: &'a [u8], log: &mut ParseLog) -> Result<&'a [u8], Error>").replace('validate_record_fields(row, payload)?','validate_capture(row, payload, log)?')
assert 'fn native_parse_record' in native and 'validate_capture' in native
code='''
#[derive(Clone,Copy)]
struct ParseLog{reply:Result<(),Error>,row:u8,ptr:*const u8,len:usize,calls:usize}
fn validate_capture(row:u8,payload:&[u8],log:&mut ParseLog)->Result<(),Error>{log.row=row;log.ptr=payload.as_ptr();log.len=payload.len();log.calls+=1;log.reply}
fn arbitrary_error()->Error{match kani::any::<u8>()%11{
 0=>Error::Allocation,1=>Error::RowOrder{expected:kani::any(),actual:kani::any()},2=>Error::InvalidRow,
 3=>Error::Tag{row:kani::any()},4=>Error::Length{row:kani::any()},5=>Error::NonCanonical{row:kani::any(),value:kani::any()},
 6=>Error::Boundary{round:kani::any()},7=>Error::Terminal,8=>Error::EqualCirclePoints,9=>Error::TrailingBytes,_=>Error::Public}}
'''+native+'''
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
'''
update({C+'NGD_wire.rs':I[C+'NGD_wire.rs']+code},'NGD_parser_candidates')
# Do not call these candidate results closure without the emitted/native join.
(E/'NGD_PARSE_SOURCE_ERASURE.json').write_text(json.dumps(dict(frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',frozen_body=original,frozen_body_sha256=hashlib.sha256(original.encode()).hexdigest(),instrumented_body=native,transform='Explicit local-record child cut, complete full Error reply; immutable borrowed payload original place; no body/guard/order change',status='CANDIDATE; exact emitted model and source-erasure transport are required before closure'),indent=2)+'\n')
