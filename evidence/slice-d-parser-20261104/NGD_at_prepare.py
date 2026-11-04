from pathlib import Path
import json,subprocess,hashlib
from NGD_add_inputs import update
E=Path(__file__).resolve().parent;p='crates/aspis-r1-cost-probe/src/NGD_wire.rs';s=json.loads((E/'NGD_NATIVE_INPUTS.json').read_text())[p];raw=subprocess.check_output(['git','show','4bb3b3f:crates/aspis-r1-cost-probe/src/r1_wire.rs'],text=True)
a=raw.index("fn parse_record_at<'a>");b=raw.index('{',a);depth=1;i=b+1
while depth:depth+=(raw[i]=='{')-(raw[i]=='}');i+=1
original=raw[a:i];body=raw[b:i].replace('parse_record(row, framed)?','parse_capture(row, framed, log)?')
native="fn native_parse_at<'a>(bytes:&'a[u8],row:u8,offset:usize,log:&mut ParseLog)->Result<(&'a[u8],usize),Error> "+body
s+='''
fn parse_capture<'a>(row:u8,framed:&'a[u8],log:&mut ParseLog)->Result<&'a[u8],Error>{
 log.row=row;log.ptr=framed.as_ptr();log.len=framed.len();log.calls+=1;
 match log.reply{Ok(())=>Ok(&framed[5..]),Err(e)=>Err(e)}
}
'''+native+'''
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
'''
update({p:s},'NGD_at_candidates')
(E/'NGD_AT_SOURCE_ERASURE.json').write_text(json.dumps(dict(frozen_body=original,frozen_body_sha256=hashlib.sha256(original.encode()).hexdigest(),instrumented_body=native,status='CANDIDATE; original get and unchecked-add sequence retained, arbitrary full Error child reply, borrowed success place fixed to child frame contract',root_domain='row<27 and offset<=usize::MAX-(5+row_shape(row).unwrap().1); cursor bound must be derived by each actual caller'),indent=2)+'\n')
