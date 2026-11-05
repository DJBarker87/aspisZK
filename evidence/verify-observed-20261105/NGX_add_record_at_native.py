from pathlib import Path
import subprocess,json,hashlib
E=Path(__file__).resolve().parent;p=E/'NGX_native.rs.txt';s=p.read_text();assert 'fn record_at_control' not in s
frozen=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:crates/aspis-r1-cost-probe/src/r1_wire.rs'],text=True)
start=frozen.index("fn parse_record_at<'a>(");at=frozen.index('{',start);d=1;i=at+1
while d:d+=(frozen[i]=='{')-(frozen[i]=='}');i+=1
original=frozen[start:i];body=frozen[at:i];assert body.count('parse_record(row, framed)?;')==1
cut=body.replace('parse_record(row, framed)?;','record_cut(row, framed, log)?;')
s+='''
struct RecordLog {calls:usize,row:u8,ptr:*const u8,length:usize,fail:bool,error:Error}
fn record_cut<'a>(row:u8,framed:&'a[u8],log:&mut RecordLog)->Result<&'a[u8],Error> {log.calls+=1;log.row=row;log.ptr=framed.as_ptr();log.length=framed.len();if log.fail {Err(log.error)}else{Ok(&framed[5..])}}
fn record_at_control<'a>(bytes:&'a[u8],row:u8,offset:usize,log:&mut RecordLog)->Result<(&'a[u8],usize),Error>
'''+cut+'''
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
'''
p.write_text(s);o=json.loads((E/'NGX_OVERLAY.json').read_text());(E/'NGX_SOURCE_PINS.json').write_text(json.dumps({p:hashlib.sha256((E/n).read_bytes()).hexdigest() for p,n in o.items()},indent=1))
(E/'NGX_RECORD_AT_CUT.json').write_text(json.dumps(dict(original_body=original,cut_body=cut,only_substitution='parse_record(row,framed) -> record_cut(row,framed,log)',domain='row<=26, byte length<=57607, offset<=57607; SAME live shared backing, all data arbitrary under descriptor identity/readonly frame',child_domain='5<=framed.len<=3717 at actual offset; all11 child errors and arbitrary payloads transported'),indent=1))
