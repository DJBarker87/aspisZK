from pathlib import Path
import json,hashlib,subprocess,difflib
E=Path(__file__).resolve().parent
s='''use super::*;
use crate::{KMX_copy_nonoverlapping,KMX_copy_from_slice};
use aspis_core::field::{M31,CM31};
fn k(x:[u32;4])->K{K{c0:CM31{a:M31(x[0]),b:M31(x[1])},c1:CM31{a:M31(x[2]),b:M31(x[3])}}}
fn e(x:[u32;8])->E{E::new(k([x[0],x[1],x[2],x[3]]),k([x[4],x[5],x[6],x[7]]))}
struct ELog<'a>{bytes:&'a[u8],at:usize,j:usize,reply:Option<E>,calls:usize}
impl ELog<'_>{fn parse(&mut self,b:&[u8])->Option<E>{assert_eq!(b.len(),32);assert_eq!(b.as_ptr() as usize,self.bytes.as_ptr() as usize+self.at);assert_eq!(b[self.j],self.bytes[self.at+self.j]^(if cfg!(NJC_invert){1}else{0}));self.calls+=1;self.reply}}
fn e_step(iter:&mut core::slice::ChunksExact<'_,u8>,mode:bool,log:&mut ELog)->Result<(),Error>{
 if let Some(c)=iter.next(){let x=log.parse(c).ok_or(Error::Parse)?;if mode&&x.c1()!=K::ZERO{return Err(Error::Parse);}}
 Ok(())
}
fn e_check(){let bytes:[u8;2272]=kani::any();let n:usize=kani::any();let i:usize=kani::any();let j:usize=kani::any();kani::assume(n<=71&&i<=n&&j<32);let mode:bool=kani::any();let q=e(kani::any());let reply=if kani::any(){Some(q)}else{None};let mut log=ELog{bytes:&bytes,at:32*i,j,reply,calls:0};let mut iter=bytes[32*i..32*n].chunks_exact(32);let result=e_step(&mut iter,mode,&mut log);let good=i==n||reply.is_some()&&(!mode||q.c1()==K::ZERO);assert_eq!(result,if good{Ok(())}else{Err(Error::Parse)});assert_eq!(log.calls,if i==n{0}else{1});assert_eq!(iter.len(),if i==n{0}else{n-i-1});}
struct KLog<'a>{bytes:&'a[u8],at:usize,j:usize,reply:Option<K>,calls:usize}
impl KLog<'_>{fn parse(&mut self,b:&[u8])->Option<K>{assert_eq!(b.len(),16);assert_eq!(b.as_ptr() as usize,self.bytes.as_ptr() as usize+self.at);assert_eq!(b[self.j],self.bytes[self.at+self.j]^(if cfg!(NJC_invert){1}else{0}));self.calls+=1;self.reply}}
fn k_step(iter:&mut core::slice::ChunksExact<'_,u8>,log:&mut KLog)->Result<(),crate::compact::CodecError>{if let Some(c)=iter.next(){log.parse(c).ok_or(crate::compact::CodecError::NonCanonical)?;}Ok(())}
fn k_check(){let bytes:[u8;464]=kani::any();let n:usize=kani::any();let i:usize=kani::any();let j:usize=kani::any();kani::assume(n<=29&&i<=n&&j<16);let reply=if kani::any(){Some(k(kani::any()))}else{None};let mut log=KLog{bytes:&bytes,at:16*i,j,reply,calls:0};let mut iter=bytes[16*i..16*n].chunks_exact(16);let result=k_step(&mut iter,&mut log);let good=i==n||reply.is_some();assert_eq!(result,if good{Ok(())}else{Err(crate::compact::CodecError::NonCanonical)});assert_eq!(log.calls,if i==n{0}else{1});assert_eq!(iter.len(),if i==n{0}else{n-i-1});}
'''
for name,call in [('echeck_step','e_check()'),('compact_step','k_check()')]:
 for suffix in ['','_renamed']:
  s+='''#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn '''+name+suffix+'(){'+call+';}\n'
(E/'NJC_chunks.rs.txt').write_text(s);x=json.loads((E/'NJC_NATIVE_INPUTS.json').read_text());p='crates/aspis-r1-cost-probe/src/verifier.rs';assert 'mod NJC_chunks;' not in x[p];x[p]+='\n#[cfg(kani)]\n#[path="NJC_chunks.rs"]\nmod NJC_chunks;\n';x['crates/aspis-r1-cost-probe/src/NJC_chunks.rs']=s
(E/'NJC_NATIVE_INPUTS.json').write_text(json.dumps(x,indent=1)+'\n');pins=json.loads((E/'NJC_SOURCE_PINS.json').read_text());pins.update({n:hashlib.sha256(t.encode()).hexdigest() for n,t in x.items()});(E/'NJC_SOURCE_PINS.json').write_text(json.dumps(pins,indent=1)+'\n')
patch='';rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
for n,t in x.items():
 z=subprocess.run(['git','show',rev+':'+n],capture_output=True,text=True);old=z.stdout if z.returncode==0 else ''
 patch+=''.join(difflib.unified_diff(old.splitlines(True),t.splitlines(True),fromfile='a/'+n,tofile='b/'+n))
(E/'NJC_native.patch').write_text(patch)
