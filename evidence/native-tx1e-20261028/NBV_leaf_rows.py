from pathlib import Path
import sys,json,difflib
E=Path(__file__).resolve().parent;R=E.parents[1];sys.path.insert(0,str(E));import NBV_host as h
attrs='''#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
'''
s='''use super::*;
use core::cell::Cell;
#[derive(Clone,Copy)]struct NBV_LeafPort<'a>{q:&'a[u8;832],tree:usize,c:usize,answer:[u8;32],calls:&'a Cell<usize>,wrong:bool}
impl Digest32 for NBV_LeafPort<'_>{fn digest(&self,p:&[&[u8]])->[u8;32]{let (tag,start,len,salt)=if self.tree==0{(0x71,0,480,608)}else if self.tree==1{(0xf1,480,128,640)}else{(0x72,672,128,800)};assert_eq!(p.len(),3);assert_eq!(p[0],&[0x10,tag]);assert_eq!(p[1].len(),len);assert_eq!(p[2].len(),32);assert_eq!(p[1].as_ptr(),self.q[start..].as_ptr());assert_eq!(p[1][self.c%len],self.q[start+self.c%len]);if self.wrong{assert_ne!(p[2][self.c%32],self.q[salt+self.c%32])}else{assert_eq!(p[2][self.c%32],self.q[salt+self.c%32])};self.calls.set(self.calls.get()+1);self.answer}}
'''
names=[]
for tree in range(3):
 for kind in ['new','duplicate']:
  for negative in [False,True]:
   name=f'NBV_leaf_row_{tree}_{kind}'+('_wrong' if negative else '')
   names.append(name)
   s+='\n#[kani::proof] #[kani::unwind(34)]\n'+attrs+'fn '+name+'(){'+'''
let q:[u8;832]=kani::any();let mut idx:[u32;16]=kani::any();let mut val:[[u8;32];16]=kani::any();let answer:[u8;32]=kani::any();let index:u32=kani::any();let mut d:usize=kani::any();let k:usize=kani::any();let c:usize=kani::any();kani::assume(d<12&&k<16&&c<32&&index<262144);let old_d=d;let old_i=idx[k];let old_v=val[k][c];
'''
   if kind=='new':s+='kani::assume(d==0||idx[d-1]!=index);'
   else:s+='kani::assume(d>0&&idx[d-1]==index);'
   s+='let calls=Cell::new(0);let leaf=batch_leaf(NBV_LeafPort{q:&q,tree:'+str(tree)+',c,answer,calls:&calls,wrong:'+str(negative).lower()+'},'+str(tree)+',&q);'
   s+='''let mut outcome=0u8;if d>0&&same_batch_index(&idx,d-1,index){if !same_batch_leaf(&val,d-1,leaf){outcome=1;}else{outcome=2;}}else{idx[d]=index;val[d]=leaf;d+=1;}
assert_eq!(calls.get(),1);
'''
   if kind=='new':s+='assert_eq!(outcome,0);assert_eq!(d,old_d+1);assert_eq!(idx[k],if k==old_d{index}else{old_i});assert_eq!(val[k][c],if k==old_d{answer[c]}else{old_v});'
   else:s+='assert_eq!(outcome,if val[old_d-1]==answer{2}else{1});assert_eq!(d,old_d);assert_eq!(idx[k],old_i);assert_eq!(val[k][c],old_v);'
   s+='}\n'
(E/'NBV_leaf_rows.rs.txt').write_text(s)
# No upload until all previous configured attempts are terminal.
if '--upload' not in sys.argv:raise SystemExit(0)
h.admit('NBV_UPLOAD4')
f='crates/aspis-r1-cost-probe/src/candidate.rs';old=(R/f).read_text();base=old
for m in ['NBV_keys','NBV_replay_keys','NBV_leaf_rows']:base+=f'\n#[cfg(kani)]\n#[path="{m}.rs"]\nmod {m};\n'
files={f:base,'crates/aspis-r1-cost-probe/src/NBV_leaf_rows.rs':s}
r=h.remote_py(f'from pathlib import Path\nb=Path({h.B!r})\nfor n,s in {files!r}.items():(b/"NBV_src"/n).write_text(s)');assert r.returncode==0,r.stderr
patch=''
for n,new in files.items():
 o=(R/n).read_text() if (R/n).exists() else ''
 patch+=''.join(difflib.unified_diff(o.splitlines(True),new.splitlines(True),fromfile='a/'+n if o else '/dev/null',tofile='b/'+n))
(E/'NBV_leaf_rows.patch').write_text(patch)
for num,n in enumerate(names,28):
 a=f'NBV_K{num:03}';cfg=json.loads((E/'NBV_K016.json').read_text());cfg.update(attempt=a,command=['python3','NBV_gate.py',a,'verifier::candidate::NBV_leaf_rows::'+n,'--cbmc-args','--unwinding-assertions']);cfg['sources']+=['NBV_src/crates/aspis-r1-cost-probe/src/NBV_leaf_rows.rs'];cfg['deps_fingerprint']['graph_receipt']=a+'-graph.json'
 for k in ['reservation_retries','source_revision','source_tree_dirty']:cfg.pop(k,None)
 (E/(a+'.json')).write_text(json.dumps(cfg,indent=2)+'\n')
