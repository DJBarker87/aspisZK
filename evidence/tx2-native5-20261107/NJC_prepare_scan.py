from pathlib import Path
import json,hashlib,subprocess,difflib
E=Path(__file__).resolve().parent
s='''use super::*;
use crate::{KMX_copy_nonoverlapping,KMX_copy_from_slice};
use aspis_core::field::{M31,CM31};
fn error()->Error{match kani::any::<u8>()%8{0=>Error::Parse,1=>Error::Semantic,2=>Error::Transcript,3=>Error::Relation,4=>Error::Merkle,5=>Error::Query,6=>Error::Checkpoint,_=>Error::Allocation}}
fn reply()->Option<Error>{if kani::any(){Some(error())}else{None}}
fn k()->K{let x:[u32;4]=kani::any();K{c0:CM31{a:M31(x[0]),b:M31(x[1])},c1:CM31{a:M31(x[2]),b:M31(x[3])}}}
struct SLog<'a>{q:&'a[u8],s:usize,replies:[Option<Error>;3],calls:usize}
impl SLog<'_>{fn record(&mut self,tag:usize,b:&[u8])->Result<(),Error>{let c=self.calls;assert_eq!(tag,c);let off=if c==0{120*self.s}else if c==1{120*self.s+104}else{480+32*self.s};let len=if c==0{104}else if c==1{16}else{32};assert_eq!(b.as_ptr() as usize,self.q.as_ptr() as usize+off);assert_eq!(b.len(),len^(if cfg!(NJC_invert){1}else{0}));self.calls+=1;match self.replies[c]{Some(e)=>Err(e),None=>Ok(())}}
fn m31s(&mut self,b:&[u8])->Result<(),Error>{self.record(0,b)}
fn parse_k(&mut self,b:&[u8])->Option<K>{match self.record(1,b){Ok(())=>Some(k()),Err(_)=>None}}
fn two_k(&mut self,b:&[u8])->Result<(),Error>{self.record(2,b)}}
// One actual s iteration, with its two nested loops fissioned at source cuts.
fn s_body(q:&[u8],s:usize,log:&mut SLog)->Result<usize,Error>{
 log.m31s(&q[s*120..s*120+104])?;
 log.parse_k(&q[s*120+104..s*120+120]).ok_or(Error::Parse)?;
 log.two_k(&q[480+s*32..480+s*32+32])?;
 Ok(s+1)
}
fn s_check(){let q:[u8;832]=kani::any();let s:usize=kani::any();kani::assume(s<4);let replies=[reply(),reply(),reply()];let mut log=SLog{q:&q,s,replies,calls:0};let out=s_body(&q,s,&mut log);let expected=if let Some(e)=replies[0]{Err(e)}else if replies[1].is_some(){Err(Error::Parse)}else if let Some(e)=replies[2]{Err(e)}else{Ok(s+1)};assert_eq!(out,expected);assert_eq!(log.calls,if replies[0].is_some(){1}else if replies[1].is_some(){2}else{3});}
struct KLog<'a>{q:&'a[u8],s:usize,l:usize,some:bool,calls:usize}
impl KLog<'_>{fn parse(&mut self,b:&[u8])->Option<K>{let off=480+self.s*32+self.l*16;assert_eq!(b.as_ptr() as usize,self.q.as_ptr() as usize+off);assert_eq!(b.len(),16);self.calls+=1;if self.some{Some(k())}else{None}}}
fn k_body(q:&[u8],s:usize,l:usize,log:&mut KLog)->Result<usize,Error>{if l>=2{return Ok(l);}log.parse(&q[480+s*32+l*16..480+s*32+l*16+16]).ok_or(Error::Parse)?;Ok(l+1)}
fn k_check(){let q:[u8;832]=kani::any();let s:usize=kani::any();let l:usize=kani::any();kani::assume(s<4&&l<=2);let some:bool=kani::any();let mut log=KLog{q:&q,s,l,some,calls:0};let out=k_body(&q,s,l,&mut log);let good=l==2||some;assert_eq!(out.is_ok(),good^cfg!(NJC_invert));assert_eq!(out,if l==2{Ok(l)}else if some{Ok(l+1)}else{Err(Error::Parse)});assert_eq!(log.calls,if l==2{0}else{1});}
struct QLog<'a>{proof:&'a[u8],i:usize,replies:[Option<Error>;2],calls:usize}
impl QLog<'_>{fn record(&mut self,c:usize,q:&[u8],off:usize,len:usize)->Result<(),Error>{assert_eq!(c,self.calls);assert_eq!(q.as_ptr() as usize,self.proof.as_ptr() as usize+10055+832*self.i+off);assert_eq!(q.len(),len^(if cfg!(NJC_invert){1}else{0}));self.calls+=1;match self.replies[c]{Some(e)=>Err(e),None=>Ok(())}}
fn inner(&mut self,q:&[u8])->Result<(),Error>{self.record(0,q,0,832)}
fn echeck(&mut self,q:&[u8],mode:bool)->Result<(),Error>{assert!(!mode);self.record(1,q,672,128)}}
fn q_body(proof:&[u8],i:usize,log:&mut QLog)->Result<usize,Error>{let q=opening(proof,i);log.inner(q)?;log.echeck(&q[672..800],false)?;Ok(i+1)}
fn q_check(){let proof:[u8;57607]=kani::any();let i:usize=kani::any();kani::assume(i<22);let replies=[reply(),reply()];let mut log=QLog{proof:&proof,i,replies,calls:0};let out=q_body(&proof,i,&mut log);assert_eq!(out,if let Some(e)=replies[0]{Err(e)}else if let Some(e)=replies[1]{Err(e)}else{Ok(i+1)});assert_eq!(log.calls,if replies[0].is_some(){1}else{2});}
fn end_check<const N:usize>(){let i:usize=kani::any();kani::assume(i>=N);let out:Result<(),Error>=if i<N{unreachable!()}else{Ok(())};assert_eq!(out.is_ok(),!cfg!(NJC_invert));}
'''
for name,call in [('scan_s','s_check()'),('scan_k2','k_check()'),('scan_query','q_check()'),('scan_s_end','end_check::<4>()'),('scan_query_end','end_check::<22>()')]:
 for suffix in ['','_renamed']:
  s+='''#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn '''+name+suffix+'(){'+call+';}\n'
(E/'NJC_scan.rs.txt').write_text(s);x=json.loads((E/'NJC_NATIVE_INPUTS.json').read_text());p='crates/aspis-r1-cost-probe/src/candidate.rs';rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';assert p not in x;x[p]=subprocess.check_output(['git','show',rev+':'+p],text=True)+'\n#[cfg(kani)]\n#[path="NJC_scan.rs"]\nmod NJC_scan;\n';x['crates/aspis-r1-cost-probe/src/NJC_scan.rs']=s
(E/'NJC_NATIVE_INPUTS.json').write_text(json.dumps(x,indent=1)+'\n');pins=json.loads((E/'NJC_SOURCE_PINS.json').read_text());pins.update({n:hashlib.sha256(t.encode()).hexdigest() for n,t in x.items()});(E/'NJC_SOURCE_PINS.json').write_text(json.dumps(pins,indent=1)+'\n')
patch=''
for n,t in x.items():
 z=subprocess.run(['git','show',rev+':'+n],capture_output=True,text=True);old=z.stdout if z.returncode==0 else ''
 patch+=''.join(difflib.unified_diff(old.splitlines(True),t.splitlines(True),fromfile='a/'+n,tofile='b/'+n))
(E/'NJC_native.patch').write_text(patch)
