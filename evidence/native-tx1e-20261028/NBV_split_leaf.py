from pathlib import Path
import sys,json,difflib
E=Path(__file__).resolve().parent;R=E.parents[1];sys.path.insert(0,str(E));import NBV_host as h
attrs='''#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
'''
s='use super::*;\n';names=[]
for kind in ['decision','new','equal','unequal']:
 for negative in [False,True]:
  n='NBV_posthash_'+kind+('_wrong' if negative else '');names.append(n)
  s+='\n#[kani::proof] #[kani::unwind(34)]\n'+attrs+'fn '+n+'(){'+'''let mut idx:[u32;16]=kani::any();let mut val:[[u8;32];16]=kani::any();let leaf:[u8;32]=kani::any();let index:u32=kani::any();let mut d:usize=kani::any();let k:usize=kani::any();let c:usize=kani::any();kani::assume(d<=12&&k<16&&c<32);let old_d=d;let old_i=idx[k];let old_v=val[k][c];'''
  if kind=='decision':
   s+='let result=if d>0&&same_batch_index(&idx,d-1,index){if !same_batch_leaf(&val,d-1,leaf){1u8}else{2u8}}else{0u8};'
   s+=('assert_ne!' if negative else 'assert_eq!')+'(result,if d>0&&idx[d-1]==index{if val[d-1]!=leaf{1}else{2}}else{0});'
  elif kind=='new':
   s+='kani::assume(d<12&&(d==0||idx[d-1]!=index));idx[d]=index;val[d]=leaf;d+=1;assert_eq!(d,old_d+1);assert_eq!(idx[k],if k==old_d{index}else{old_i});'
   s+=('assert_ne!' if negative else 'assert_eq!')+'(val[k][c],if k==old_d{leaf[c]}else{old_v});'
  else:
   s+='kani::assume(d>0&&idx[d-1]==index);'
   s+='kani::assume(val[d-1]'+('==' if kind=='equal' else '!=')+'leaf);'
   s+='let result=if !same_batch_leaf(&val,d-1,leaf){Err(Error::Merkle)}else{Ok(())};'
   s+=('assert_ne!' if negative else 'assert_eq!')+'(result.is_ok(),'+str(kind=='equal').lower()+');assert_eq!(d,old_d);assert_eq!(idx[k],old_i);assert_eq!(val[k][c],old_v);'
  s+='}\n'
s+='''#[kani::proof] #[kani::unwind(2)]
fn NBV_rebased_key_domain(){let queries:[u32;22]=kani::any();let batch:usize=kani::any();let j:usize=kani::any();let tree:usize=kani::any();kani::assume(batch<2&&tree<3);let (lo,n)=if batch==0{(0,10)}else{(10,12)};kani::assume(j<n);let u=queries[lo+j];kani::assume(u<262144);let index=if tree==2{u/4}else{u};let key=(u64::from(index)<<8)|j as u64;let selected=lo+(key&255)as usize;assert_eq!(selected,lo+j);assert!(selected<22);assert_eq!((key>>8)as u32,index);assert!(index<262144);if tree==2{assert!(index<65536);}}
#[kani::proof] #[kani::unwind(2)]
fn NBV_binary_arity(){assert_eq!(Arity::Two.bits(),1);assert_eq!(Arity::Two.width(),2);assert_eq!(Arity::Two.levels(),18);}
'''
names+=['NBV_rebased_key_domain','NBV_binary_arity'];assert len(names)==10
(E/'NBV_posthash.rs.txt').write_text(s)
h.admit('NBV_UPLOAD4SPLIT')
f='crates/aspis-r1-cost-probe/src/candidate.rs';base=(R/f).read_text()
for m in ['NBV_keys','NBV_replay_keys','NBV_leaf_rows','NBV_posthash']:base+=f'\n#[cfg(kani)]\n#[path="{m}.rs"]\nmod {m};\n'
files={f:base,'crates/aspis-r1-cost-probe/src/NBV_posthash.rs':s}
r=h.remote_py(f'from pathlib import Path\nb=Path({h.B!r})\nfor n,s in {files!r}.items():(b/"NBV_src"/n).write_text(s)');assert r.returncode==0,r.stderr
patch=''
for n,new in files.items():
 o=(R/n).read_text() if (R/n).exists() else ''
 patch+=''.join(difflib.unified_diff(o.splitlines(True),new.splitlines(True),fromfile='a/'+n if o else '/dev/null',tofile='b/'+n))
(E/'NBV_posthash.patch').write_text(patch)
for num,n in enumerate(names,30):
 a=f'NBV_K{num:03}';assert not (E/a/'receipt.json').exists();cfg=json.loads((E/'NBV_K028.json').read_text());cfg.update(attempt=a,command=['python3','NBV_gate.py',a,'verifier::candidate::NBV_posthash::'+n,'--cbmc-args','--unwinding-assertions']);cfg['sources']+=['NBV_src/crates/aspis-r1-cost-probe/src/NBV_posthash.rs'];cfg['deps_fingerprint']['graph_receipt']=a+'-graph.json'
 for k in ['reservation_retries','source_revision','source_tree_dirty','deferred']:cfg.pop(k,None)
 (E/(a+'.json')).write_text(json.dumps(cfg,indent=2)+'\n')
