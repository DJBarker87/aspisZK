"""Exact frozen frontier control, full logical Vec poststates and one observed byte."""
from pathlib import Path
import subprocess,re,json,hashlib
E=Path(__file__).resolve().parent;frozen='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
src=subprocess.check_output(['git','show',frozen+':crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs'],text=True)
start=src.index('            fn frontier(out:');end=src.index('            let p = self.semantic();',start);original=src[start:end]
a=original.index('{');body=original[a:original.rfind('}')+1]
body,count=re.subn(r'fields\(out, &values\[(\d+)\]\)\?;',r'NHG_fields_cut(out, &values[\1], log)?;',body);assert count==20
err=Path(E.parent/'verify-observed-20261105/NGX_native.rs.txt').read_text();err=err[err.index('fn any_error()'):err.index('struct ValidateLog')]
text='''use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
fn digest()->Digest{let w:[u32;8]=kani::any();core::array::from_fn(|i|M31(w[i]))}
'''+err+'''
struct FrontierLog{calls:usize,fail_at:usize,error:Error,observe:usize,word:usize,vec_places:[*const alloc::vec::Vec<u8>;20],rows:[*const M31;20],words:[u32;20],before_len:[usize;20],before_byte:[u8;20],after_len:[usize;20],after_byte:[u8;20],after_ptr:[*const u8;20]}
fn NHG_fields_cut(out:&mut alloc::vec::Vec<u8>,values:&[M31],log:&mut FrontierLog)->Result<(),Error>{
 let j=log.calls;assert!(j<20);assert_eq!(values.len(),8);assert!(out.len()>=1&&out.len()+32<=1880);
 log.calls+=1;log.vec_places[j]=out;log.rows[j]=values.as_ptr();log.words[j]=values[log.word].0;log.before_len[j]=out.len();log.before_byte[j]=if log.observe<out.len(){out[log.observe]}else{0};
 let length:usize=kani::any();kani::assume(length>=out.len()&&length<=out.len()+32);
 let mut reply=kani::vec::exact_vec::<u8,1884>();reply.truncate(length);
 log.after_len[j]=length;log.after_byte[j]=if log.observe<length{reply[log.observe]}else{0};log.after_ptr[j]=reply.as_ptr();*out=reply;
 if j==log.fail_at{Err(log.error)}else{Ok(())}
}
fn NHG_frontier_control(out:&mut alloc::vec::Vec<u8>,values:&[Digest;20],log:&mut FrontierLog)->Result<(),Error>
'''+body+'''
#[kani::proof]#[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NHG_frontier_value(){
 let values:[Digest;20]=core::array::from_fn(|_|digest());let n:usize=kani::any();kani::assume(n>=1&&n<=1240);
 let mut out=kani::vec::exact_vec::<u8,1884>();out.truncate(n);let place=&out as *const alloc::vec::Vec<u8>;
 let observe:usize=kani::any();kani::assume(observe<1880);let word:usize=kani::any();kani::assume(word<8);let old_byte=if observe<n{out[observe]}else{0};
 let fail_at:usize=kani::any();kani::assume(fail_at<=20);let error=any_error();
 let mut log=FrontierLog{calls:0,fail_at,error,observe,word,vec_places:[core::ptr::null();20],rows:[core::ptr::null();20],words:[0;20],before_len:[0;20],before_byte:[0;20],after_len:[0;20],after_byte:[0;20],after_ptr:[core::ptr::null();20]};
 let got=NHG_frontier_control(&mut out,&values,&mut log);let count=if fail_at<20{fail_at+1}else{20};assert_eq!(log.calls,count);
 let j:usize=kani::any();kani::assume(j<count);assert_eq!(log.vec_places[j],place);assert_eq!(log.rows[j],values[j].as_ptr());assert_eq!(log.words[j],values[j][word].0);
 assert_eq!(log.before_len[j],if j==0{n}else{log.after_len[j-1]});if observe<log.before_len[j]{assert_eq!(log.before_byte[j],if j==0{old_byte}else{log.after_byte[j-1]});}
 assert_eq!(out.len(),log.after_len[count-1]);assert_eq!(out.as_ptr(),log.after_ptr[count-1]);assert_eq!(got,if fail_at<20{Err(error)}else{Ok(())});
 if cfg!(NHG_invert){kani::assume(fail_at==20);kani::assume(observe<out.len());}
 if observe<out.len(){assert_eq!(out[observe],log.after_byte[count-1]^if cfg!(NHG_invert){1}else{0});}
}
'''
(E/'NHG_frontier.rs.txt').write_text(text)
p=E/'NHG_statement.rs.txt';s=p.read_text();needle='pub mod r0 {\n';assert 'mod NHG_frontier'not in s;s=s.replace(needle,needle+'    #[cfg(kani)] mod NHG_frontier {include!("NHG_frontier.rs");}\n',1);p.write_text(s)
m=json.loads((E/'NHG_OVERLAY.json').read_text());m['crates/aspis-statement/src/pool_v1/NHG_frontier.rs']='NHG_frontier.rs.txt';(E/'NHG_OVERLAY.json').write_text(json.dumps(m,indent=1));(E/'NHG_SOURCE_PINS.json').write_text(json.dumps({n:hashlib.sha256((E/v).read_bytes()).hexdigest()for n,v in m.items()},indent=1))
(E/'NHG_FRONTIER_CUT.json').write_text(json.dumps(dict(original=original,cut_body=body,calls=count,logical_poststates='Every initialized byte-vector of length oldLen..oldLen+32; native Vec capacity hidden by retained Std interpretation. Caller only forwards the SAME mutable Vec place; no pointer/capacity-dependent branch.',window='ONE arbitrary observed byte with exact lengths/owner pointers and same-place pre/post chain; all input rows arbitrary full raw U32'),indent=1))
