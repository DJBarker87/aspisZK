from NCN_extend import E,extend,attrs
import json
h='''
#[cfg(kani)] mod NCN_resume {
use super::*;
use core::cell::Cell;
#[derive(Clone,Copy)]struct Request<'a>{calls:&'a Cell<usize>,stop:usize,proof:&'a[u8],public:&'a[u8],saved:&'a[u8]}
impl Digest32 for Request<'_>{fn digest(&self,parts:&[&[u8]])->[u8;32]{
let n=self.calls.get();self.calls.set(n+1);
let range=match n {
0=>{assert!(parts.len()==1&&parts[0].len()==57607&&parts[0].as_ptr()==self.proof.as_ptr());16..48},
1=>{assert!(parts.len()==1&&parts[0].len()==1880&&parts[0].as_ptr()==self.public.as_ptr());48..80},
2=>{assert!(parts.len()==2&&parts[0]==b"UNPROVED:R1:checkpoint"&&parts[1].len()==1736&&parts[1].as_ptr()==self.saved.as_ptr());1736..1768},
_=>panic!("unreached suffix digest")};
let mut reply:[u8;32]=self.saved[range].try_into().unwrap();if n==self.stop{reply[0]^=1;}reply
}}
'''
q=[]
# An outer query transition on every valid native prefix length, rejecting before contains.
h+='''fn query_step(queries:&[u32;22],mut i:usize)->Result<usize,Error>{
let q=queries[i];
if q>=1<<18||queries[..i].contains(&q){return Err(Error::Checkpoint);}
i+=1;
Ok(i)
}
'''
for neg in [False,True]:
 name='query_range_'+('wrong' if neg else 'ok')
 h+=attrs+f'''fn {name}(){{let queries:[u32;22]=kani::any();let i:usize=kani::any();kani::assume(i<22&&queries[i]>=1<<18);let out=query_step(&queries,i);assert!(matches!(out,Err(Error::Checkpoint)){'!=' if neg else '=='}true);}}\n'''
 q.append(dict(harness='verifier::NCN_resume::'+name,negative=neg))
for stop in range(3):
 for neg in [False,True]:
  name=f'stop{stop}_'+('wrong' if neg else 'ok')
  h+=attrs+f'''fn {name}(){{
let mut saved:[u8;1768]=kani::any();saved[..8].copy_from_slice(b"R1P2CKP2");saved[8]=2;saved[10]=1;
let next:u8=kani::any();kani::assume(next<=22);saved[9]=next;saved[11]=0;saved[12]=0;saved[13]=0;saved[14]=0;saved[15]=0;
let proof:[u8;57607]=kani::any();let public:[u8;1880]=kani::any();let count=Cell::new(0usize);
let hash=Request{{calls:&count,stop:{stop},proof:&proof,public:&public,saved:&saved}};
let out=resume(&saved,&proof,&public,Variant::S2,hash);
assert!(matches!(out,Err(Error::Checkpoint)));assert!(count.get(){'!=' if neg else '=='}{stop+1});
}}\n'''
  q.append(dict(harness='verifier::NCN_resume::'+name,negative=neg))
h+='}\n';extend('NCN_resume.patch',h)
for i,x in enumerate(q,65):x.update(attempt=f'NCN_K{i:03}',patch='NCN_resume.patch')
(E/'NCN_resume_queue.json').write_text(json.dumps(q,indent=2)+'\n')
