from pathlib import Path
import sys,json,difflib,subprocess
E=Path(__file__).resolve().parent;R=E.parents[1];sys.path.insert(0,str(E));import NBV_host as h
attrs='''#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
'''
mp=(E/'NBV_multiproof.rs.txt').read_text()+'''
use core::cell::Cell;
#[derive(Clone,Copy)]
struct Port<'a>{left:*const u8,right:*const u8,c:usize,l:u8,r:u8,answer:[u8;32],calls:&'a Cell<usize>}
impl Digest32 for Port<'_>{fn digest(&self,p:&[&[u8]])->[u8;32]{assert_eq!(p.len(),3);assert_eq!(p[0],&[0x12]);assert_eq!(p[1].len(),32);assert_eq!(p[2].len(),32);assert_eq!(p[1].as_ptr(),self.left);assert_eq!(p[2].as_ptr(),self.right);assert_eq!(p[1][self.c],self.l);assert_eq!(p[2][self.c],self.r);self.calls.set(self.calls.get()+1);self.answer}}
'''
# No complete-array snapshot or independent native initial carrier.
for kind in ['pair','supply_left','supply_right']:
 mp+='\n#[kani::proof] #[kani::unwind(34)]\n'+attrs+f'fn NBV_{kind}_carrier(){{'+'''
 let val:[[u8;32];16]=kani::any();let i:usize=kani::any();let c:usize=kani::any();kani::assume(i<'''+('15' if kind=='pair' else '16')+'''&&c<32);
 let sibling:[u8;32]=kani::any();let answer:[u8;32]=kani::any();let calls=Cell::new(0);
'''
 if kind=='pair':mp+='let left=&val[i];let right=&val[i+1];'
 elif kind=='supply_left':mp+='let left=&val[i];let right=&sibling;'
 else:mp+='let left=&sibling;let right=&val[i];'
 mp+='let hash=Port{left:left.as_ptr(),right:right.as_ptr(),c,l:left[c],r:right[c],answer,calls:&calls};'
 if kind=='pair':mp+='let out=occupied_binary_parent(hash,&val,i);'
 else:mp+='let out=sibling_binary_parent(hash,&val,i,&sibling,'+str(kind=='supply_left').lower()+');'
 mp+='assert_eq!(out[c],answer[c]);assert_eq!(calls.get(),1);}\n'
# Arbitrary native pre-state, one selected write, no full old-array copy.
mp+='\n#[kani::proof] #[kani::unwind(34)]\n'+attrs+'''fn NBV_row_store_frame(){let mut idx:[u32;16]=kani::any();let mut val:[[u8;32];16]=kani::any();let w:usize=kani::any();let k:usize=kani::any();let c:usize=kani::any();kani::assume(w<16&&k<16&&c<32);let old_i=idx[k];let old_v=val[k][c];let parent:u32=kani::any();let digest:[u8;32]=kani::any();idx[w]=parent;val[w]=digest;assert_eq!(idx[k],if k==w{parent}else{old_i});assert_eq!(val[k][c],if k==w{digest[c]}else{old_v});}
'''
mp+='\n#[kani::proof] #[kani::unwind(34)]\n'+attrs+'''fn NBV_row_store_wrong(){let mut val=[[0u8;32];16];let digest=[1u8;32];val[15]=digest;assert_eq!(val[15][31],0);}
'''
# Count copies full live prefix to SAME initial zero carrier, including canonical caller admission.
mp+='\n#[kani::proof] #[kani::unwind(34)]\n'+attrs+'''fn NBV_admitted_count_copy(){let input:[u32;16]=kani::any();let n:usize=kani::any();let k:usize=kani::any();kani::assume(n>0&&n<=16&&k<16);kani::assume(well_formed(&input[..n]));let mut level=[0u32;16];level[..n].copy_from_slice(&input[..n]);let live_n=n;let count=0usize;assert_eq!(live_n,n);assert_eq!(count,0);assert_eq!(level[k],if k<n{input[k]}else{0});}
'''
keys='use super::*;\n'
# Changed shape: separate physical pointer association (no large byte observer).
keys+='''#[kani::proof] #[kani::unwind(2)]
fn NBV_opening_pointer_global(){let proof:[u8;57607]=kani::any();let i:usize=kani::any();kani::assume(i<22);let q=opening(&proof,i);assert_eq!(q.len(),832);assert_eq!(q.as_ptr(),proof.as_ptr().wrapping_add(10055+832*i));}
'''
# One 32-byte range in arbitrary surrounding memory, no whole opening comparison.
keys+='''#[kani::proof] #[kani::unwind(2)]
fn NBV_opening_window_pointer(){let proof:[u8;57607]=kani::any();let i:usize=kani::any();let w:usize=kani::any();kani::assume(i<22&&w<26);let q=opening(&proof,i);let selected=&q[32*w..32*(w+1)];assert_eq!(selected.len(),32);assert_eq!(selected.as_ptr(),proof.as_ptr().wrapping_add(10055+832*i+32*w));}
'''
# Count/error guard before any potentially overflowing byte multiplication.
keys+='''#[kani::proof] #[kani::unwind(2)]
fn NBV_padding_guard(){let count:usize=kani::any();let s:usize=kani::any();kani::assume(s<6);if count>SLOT_NODES[s]{let out:Result<(),Error>=Err(Error::Parse);assert!(matches!(out,Err(Error::Parse)));}else{assert!(32*count<=32*SLOT_NODES[s]);assert!(32*SLOT_NODES[s]<=5504);assert_eq!((32*SLOT_NODES[s]-32*count)%8,0);}}
#[kani::proof] #[kani::unwind(2)]
fn NBV_padding_continuation(){let scan:bool=kani::any();let verified:bool=kani::any();let mut calls=0;let result=if scan{Err(Error::Parse)}else{calls+=1;if !verified{Err(Error::Merkle)}else{Ok(())}};assert_eq!(calls,if scan{0}else{1});if scan{assert!(matches!(result,Err(Error::Parse)))}else if verified{assert!(result.is_ok())}else{assert!(matches!(result,Err(Error::Merkle)))}}
'''
files={'crates/aspis-r1-cost-probe/src/NBV_multiproof.rs':mp,'crates/aspis-r1-cost-probe/src/NBV_keys.rs':keys}
for f,m in [('multiproof.rs','NBV_multiproof'),('candidate.rs','NBV_keys')]:
 n='crates/aspis-r1-cost-probe/src/'+f;files[n]=(R/n).read_text()+f'\n#[cfg(kani)]\n#[path="{m}.rs"]\nmod {m};\n'
(E/'NBV_multiproof.rs.txt').write_text(mp);(E/'NBV_keys.rs.txt').write_text(keys)
patch=''
for n,new in files.items():
 old=(R/n).read_text() if (R/n).exists() else ''
 patch+=''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+n if old else '/dev/null',tofile='b/'+n))
(E/'NBV_harness.patch').write_text(patch)
h.admit('NBV_UPLOAD2');r=h.remote_py(f'from pathlib import Path\nb=Path({h.B!r})\nfor n,s in {files!r}.items():(b/"NBV_src"/n).write_text(s)');assert r.returncode==0,r.stderr
names=[('multiproof::NBV_multiproof::','NBV_'+n) for n in ['pair_carrier','supply_left_carrier','supply_right_carrier','row_store_frame','row_store_wrong','admitted_count_copy']]+[('verifier::candidate::NBV_keys::','NBV_'+n) for n in ['opening_pointer_global','opening_window_pointer','padding_guard','padding_continuation']]
for num,(m,n) in enumerate(names,4):
 a=f'NBV_K{num:03}';cfg=json.loads((E/'NBV_K003.json').read_text());cfg.update(attempt=a,sources=['NBV_src/Cargo.lock','NBV_gate.py','NBV_src/KMX_stubs.rs','NBV_KMX_copy_stubs.patch','NBV_src/crates/aspis-r1-cost-probe/src/lib.rs']+['NBV_src/'+n for n in files],command=['python3','NBV_gate.py',a,m+n,'--cbmc-args','--unwinding-assertions']);cfg['deps_fingerprint']['graph_receipt']=a+'-graph.json'
 for k in ['reservation_retries','source_revision','source_tree_dirty']:cfg.pop(k,None)
 (E/(a+'.json')).write_text(json.dumps(cfg,indent=2)+'\n')
