from pathlib import Path
import sys,json,difflib,hashlib
E=Path(__file__).resolve().parent;R=E.parents[1];sys.path.insert(0,str(E));import NBJ_host as h
keys=r'''
use super::*;
#[kani::proof] #[kani::unwind(2)]
fn NBJ_opening_scalar(){
 let i:usize=kani::any();kani::assume(i<22);
 let at=compact::OFF_OPENINGS+i*OPENING;let end=at+OPENING;
 assert_eq!(at,10055+832*i);assert_eq!(end,10055+832*(i+1));assert!(at<=end && end<=57607);assert_eq!(end-at,832);
}
#[kani::proof] #[kani::unwind(2)]
fn NBJ_opening_range_position(){
 // One arbitrary observed byte; no fully symbolic 57607-byte allocation.
 let i:usize=kani::any();let c:usize=kani::any();let byte:u8=kani::any();kani::assume(i<22 && c<832);
 let mut proof=[0u8;57607];let at=10055+832*i;proof[at+c]=byte;
 let q=&proof[at..at+832];assert_eq!(q.len(),832);assert_eq!(q.as_ptr(),proof[at..].as_ptr());assert_eq!(q[c],byte);
}
'''

keys+=r"""
#[kani::proof] #[kani::unwind(2)]
fn NBJ_range_window(){
 let q:[u8;832]=kani::any();let c:usize=kani::any();kani::assume(c<832);
 let view=&q[0..832];assert_eq!(view.len(),832);assert_eq!(view[c],q[c]);assert_eq!(view.as_ptr(),q.as_ptr());
}
#[kani::proof] #[kani::unwind(2)]
fn NBJ_key_iterator(){
 let j:usize=kani::any();let batch:usize=kani::any();kani::assume(batch<2);let n=if batch==0{10}else{12};let lo=if batch==0{0}else{10};kani::assume(j<=n);
 let mut it=j..n;let next=it.next();assert_eq!(next,if j<n{Some(j)}else{None});
 if let Some(k)=next{assert_eq!(it.start,k+1);assert!(lo+k<22 && k<16)}else{assert_eq!(it.start,j)}
}
#[kani::proof] #[kani::unwind(2)]
fn NBJ_key_zero(){let k:usize=kani::any();kani::assume(k<16);let keys=[0u64;16];assert_eq!(keys[k],0);}
#[kani::proof] #[kani::unwind(2)]
fn NBJ_sort_iterator(){let n:usize=kani::any();let i:usize=kani::any();kani::assume((n==10||n==12)&&i>=1&&i<=n);let mut it=i..n;let next=it.next();assert_eq!(next,if i<n{Some(i)}else{None});if let Some(j)=next{assert!(j<16);assert_eq!(it.start,j+1);}}
#[kani::proof] #[kani::unwind(2)]
fn NBJ_padding_iterator(){
 let bytes:[u8;5504]=kani::any();let count:usize=kani::any();let cap:usize=kani::any();let k:usize=kani::any();let c:usize=kani::any();kani::assume(count<=cap && cap<=172 && k<=4*(cap-count) && c<8);
 let at=32*count+8*k;let suffix=&bytes[at..32*cap];let mut chunks=suffix.chunks_exact(8);let next=chunks.next();
 if k<4*(cap-count){let q=next.unwrap();assert_eq!(q.len(),8);assert_eq!(q[c],bytes[at+c]);assert_eq!(chunks.len(),4*(cap-count)-k-1);}else{assert!(next.is_none());assert_eq!(chunks.len(),0)}
 assert_eq!(chunks.remainder().len(),0);
}
#[kani::proof] #[kani::unwind(2)]
fn NBJ_leaf_scratch_zero(){let k:usize=kani::any();let c:usize=kani::any();kani::assume(k<16&&c<32);let idx=[0u32;16];let val=[[0u8;32];16];assert_eq!(idx[k],0);assert_eq!(val[k][c],0);}
"""
mp=r"""
use super::*;
use core::cell::Cell;
#[derive(Clone,Copy)]
struct Hash<'a>{answer:[u8;32],left:&'a[u8],right:&'a[u8],c:usize,calls:&'a Cell<usize>}
impl Digest32 for Hash<'_>{fn digest(&self,p:&[&[u8]])->[u8;32]{
 assert_eq!(p.len(),3);assert_eq!(p[0],&[0x12]);assert_eq!(p[1].len(),32);assert_eq!(p[2].len(),32);
 assert_eq!(p[1][self.c],self.left[self.c]);assert_eq!(p[2][self.c],self.right[self.c]);
 self.calls.set(self.calls.get()+1);self.answer
}}
fn NBJ_row<H:Digest32>(hash:H,idx:&mut[u32;16],val:&mut[[u8;32];16],n:usize,nodes:&[u8],mut at:usize,mut w:usize,mut i:usize)->(bool,usize,usize,usize){
 let parent=index_at(idx,i)>>Arity::Two.bits();
 let digest=if i+1<n && index_at(idx,i+1)==index_at(idx,i)^1{
  let d=occupied_binary_parent(hash,val,i);i+=2;d
 }else{
  let Some(sibling)=nodes.get(at..at+32)else{return(false,at,w,i)};
  at+=32;let d=sibling_binary_parent(hash,val,i,sibling,index_at(idx,i)&1==0);i+=1;d
 };
 idx[w]=parent;val[w]=digest;w+=1;(true,at,w,i)
}
"""
# Split by source position. Each fixed position still has arbitrary scratch,
# arbitrary write position, arbitrary digest reply and arbitrary observed byte.
for pos in range(16):
 for paired in [True,False]:
  if paired and pos==15:continue
  name='NBJ_'+('pair' if paired else 'supply')+f'_{pos:02}'
  mp+=f"""\n#[kani::proof] #[kani::unwind(34)]
fn {name}(){{
 let mut idx:[u32;16]=kani::any();let mut val:[[u8;32];16]=kani::any();let old_idx=idx;let old_val=val;
 let n:usize=kani::any();let w:usize=kani::any();let k:usize=kani::any();let c:usize=kani::any();
 kani::assume(n>{pos} && n<=16 && w<={pos} && k<16 && c<32);
 let pair={pos}+1<n && idx[{pos}+1]==idx[{pos}]^1;
 kani::assume(pair=={str(paired).lower()});
 let sibling:[u8;32]=kani::any();let answer:[u8;32]=kani::any();let calls=Cell::new(0);
 let (left,right):(&[u8],&[u8])="""
  if paired:mp+=f'(&old_val[{pos}],&old_val[{pos}+1]);'
  else:mp+=f'if idx[{pos}]&1==0{{(&old_val[{pos}],&sibling)}}else{{(&sibling,&old_val[{pos}])}};'
  mp+=f"""
 let out=NBJ_row(Hash{{answer,left,right,c,calls:&calls}},&mut idx,&mut val,n,&sibling,0,w,{pos});
 assert_eq!(out,(true,{0 if paired else 32},w+1,{pos+(2 if paired else 1)}));assert_eq!(calls.get(),1);
 assert_eq!(idx[k],if k==w{{old_idx[{pos}]/2}}else{{old_idx[k]}});
 assert_eq!(val[k][c],if k==w{{answer[c]}}else{{old_val[k][c]}});
}}
"""
# The final supply position must avoid syntactically indexing idx[16].
mp=mp.replace('let pair=15+1<n && idx[15+1]==idx[15]^1;','let pair=false;')
files={'crates/aspis-r1-cost-probe/src/NBJ_keys.rs':keys,'crates/aspis-r1-cost-probe/src/NBJ_multiproof.rs':mp}
f='crates/aspis-r1-cost-probe/src/multiproof.rs';files[f]=(R/f).read_text()+'\n#[cfg(kani)]\n#[path="NBJ_multiproof.rs"]\nmod NBJ_multiproof;\n'
f='crates/aspis-r1-cost-probe/src/candidate.rs';files[f]=(R/f).read_text()+'\n#[cfg(kani)]\n#[path="NBJ_keys.rs"]\nmod NBJ_keys;\n'
patch=''
for name,new in files.items():
 old=(R/name).read_text() if (R/name).exists() else ''
 patch+=''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+name if old else '/dev/null',tofile='b/'+name))
(E/'NBJ_harness.patch').write_text(patch)
if '--upload' in sys.argv:
 h.admit('NBJ_UPLOAD')
 payload={**files,'NBJ_gate.py':(E/'NBJ_gate.py').read_text()}
 code=f'from pathlib import Path\nb=Path({h.B!r})\nfor n,s in {payload!r}.items():\n p=b/n if n=="NBJ_gate.py" else b/"NBJ_src"/n\n p.write_text(s)\n'
 r=h.remote_py(code);assert r.returncode==0,r.stderr
import re
for i,n in enumerate([('verifier::candidate::NBJ_keys::',n) for n in re.findall(r'fn (NBJ_\w+)\(\)',keys)]+[('multiproof::NBJ_multiproof::',n) for n in re.findall(r'fn (NBJ_\w+)\(\)',mp)],1):
 a=f'NBJ_K{i:03}';cfg=json.loads((R/'evidence/native-tx1b-20261027/NBI_K016.json').read_text());cfg['attempt']=a;cfg['command']=['python3','NBJ_gate.py',a,n[0]+n[1]];cfg['sources']=['NBJ_src/Cargo.lock',f,'NBJ_src/crates/aspis-r1-cost-probe/src/NBJ_keys.rs','NBJ_gate.py','NBJ_src/crates/aspis-r1-cost-probe/src/multiproof.rs','NBJ_src/crates/aspis-r1-cost-probe/src/NBJ_multiproof.rs'];cfg['sources'][1]='NBJ_src/'+f
 cfg['deps_fingerprint']['graph_receipt']=a+'-graph.json';cfg['env']['TMPDIR']=h.B+'/NBJ_tmp'
 for k in ['reservation_retries','source_revision','source_tree_dirty']:cfg.pop(k,None)
 if not (E/a/'receipt.json').exists():(E/(a+'.json')).write_text(json.dumps(cfg,indent=2)+'\n')
