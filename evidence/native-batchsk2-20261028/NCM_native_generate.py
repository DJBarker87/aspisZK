"""Emit only a reviewable scratch patch; shipped source never modified."""
from pathlib import Path
import subprocess,difflib,json
E=Path(__file__).resolve().parent
attrs='''#[kani::proof]
#[kani::unwind(40)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(<[u8]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
'''
spy='''use aspis_core::Digest32;
#[derive(Clone,Copy)]
pub struct NCM_Spy<'a> {pub expected:[&'a[u8];3],pub reply:[u8;32],pub mode:u8,pub offset:usize,pub negative:bool}
impl Digest32 for NCM_Spy<'_> {
 fn digest(&self,p:&[&[u8]])->[u8;32] {
  assert_eq!(p.len(),3,"NCM three parts");
  let geometry=p[0].len()==self.expected[0].len() && p[1].len()==self.expected[1].len() && p[2].len()==self.expected[2].len() && p[0]==self.expected[0];
  if self.mode==0 {assert!(geometry != self.negative,"NCM geometry/tag");} else {assert!(geometry,"NCM geometry/tag");}
  if self.mode==1 {assert!((p[1][self.offset]==self.expected[1][self.offset]) != self.negative,"NCM left/value byte");}
  if self.mode==2 {assert!((p[2][self.offset]==self.expected[2][self.offset]) != self.negative,"NCM right/salt byte");}
  self.reply
 }
}
pub fn NCM_reply(out:[u8;32],expected:[u8;32],mode:u8,offset:usize,negative:bool) {
 if mode==3 {assert!((out[offset]==expected[offset]) != negative,"NCM reply byte");}
}
'''
cand='use super::*;\nuse crate::NCM_spy::{NCM_Spy,NCM_reply};\n'
mp='use super::*;\nuse crate::NCM_spy::{NCM_Spy,NCM_reply};\n'
shapes=[]
# Actual source scalar accessor. No copied source-loop body.
for negative in [False,True]:
 name='NCM_key_read_'+('wrong' if negative else 'native')
 cand+=attrs+f'''fn {name}() {{let keys:[u64;16]=kani::any();let i:usize=kani::any();kani::assume(i<16);let expected:u64=kani::any();kani::assume(keys[i]==expected);let out=batch_key_at(&keys,i);assert!((out==expected) != {str(negative).lower()},"NCM selected key");}}\n'''
shapes.append(dict(shape='key_read',module='verifier::candidate::NCM_candidate',positive='NCM_key_read_native',negative='NCM_key_read_wrong',domain='arbitrary keys[16], i<16; actual scalar accessor only',fragment='KeysRead partial: cursor advance/caller frame association remains'))
for kind in ['occupied','left','right','leaf0','leaf1','leaf2']:
 for mode,label in enumerate(['geometry','first','second','reply']):
  stem=f'NCM_{kind}_{label}'
  for negative in [False,True]:
   name=stem+('_wrong' if negative else '_native');neg=str(negative).lower()
   if kind.startswith('leaf'):
    t=int(kind[-1]);tag=['merkle::C1_TAG','merkle::C2_TAG','0x72'][t];a,z,s,e=[(0,480,608,640),(480,608,640,672),(672,800,800,832)][t]
    length=[1,z-a,32,32][mode]
    body=f'''let q:[u8;832]=kani::any();let reply:[u8;32]=kani::any();let pos:usize=kani::any();kani::assume(pos<{length});let h=NCM_Spy{{expected:[&[0x10,{tag}],&q[{a}..{z}],&q[{s}..{e}]],reply,mode:{mode},offset:pos,negative:{neg}}};let out=batch_leaf(h,{t},&q);NCM_reply(out,reply,{mode},pos,{neg});'''
    cand+=attrs+f'fn {name}(){{{body}}}\n'
    module='verifier::candidate::NCM_candidate';frag='Leaf partial: exact request grammar/one byte or reply; no post/carrier association'
   else:
    length=1 if mode==0 else 32
    setup=f'''let values:[[u8;32];16]=kani::any();let reply:[u8;32]=kani::any();let pos:usize=kani::any();kani::assume(pos<{length});let i:usize=kani::any();'''
    if kind=='occupied':
     setup+='kani::assume(i<15);';expected='[&[BINARY_NODE_TAG],&values[i],&values[i+1]]';call='occupied_binary_parent(h,&values,i)'
    else:
     setup+='kani::assume(i<16);let sibling:[u8;32]=kani::any();';expected='[&[BINARY_NODE_TAG],&values[i],&sibling]' if kind=='left' else '[&[BINARY_NODE_TAG],&sibling,&values[i]]';call=f'sibling_binary_parent(h,&values,i,&sibling,{str(kind=="left").lower()})'
    body=setup+f'''let h=NCM_Spy{{expected:{expected},reply,mode:{mode},offset:pos,negative:{neg}}};let out={call};NCM_reply(out,reply,{mode},pos,{neg});'''
    mp+=attrs+f'fn {name}(){{{body}}}\n';module='multiproof::NCM_multiproof';frag='Row partial: actual hash helper only; row PC/cursors/writes/frame remain'
  shapes.append(dict(shape=kind+'_'+label,module=module,positive=stem+'_native',negative=stem+'_wrong',domain=f'actual {kind} helper, symbolic source arrays, index bound, arbitrary offset in selected part; concrete data observer without function pointer',fragment=frag))
files={'crates/aspis-r1-cost-probe/src/NCM_spy.rs':spy,'crates/aspis-r1-cost-probe/src/NCM_candidate.rs':cand,'crates/aspis-r1-cost-probe/src/NCM_multiproof.rs':mp}
patch=''
for path,text in files.items():
 patch+=''.join(difflib.unified_diff([],text.splitlines(True),fromfile='/dev/null',tofile='b/'+path))
for path,extra in [('crates/aspis-r1-cost-probe/src/lib.rs','\n#[cfg(kani)]\n#[path="../../../KMX_stubs.rs"]\n#[allow(non_snake_case)]\npub mod KMX_stubs;\n#[cfg(kani)]\n#[allow(non_snake_case)]\npub mod NCM_spy;\n'),('crates/aspis-r1-cost-probe/src/candidate.rs','\n#[cfg(kani)]\n#[allow(non_snake_case)]\n#[path="NCM_candidate.rs"]\nmod NCM_candidate;\n'),('crates/aspis-r1-cost-probe/src/multiproof.rs','\n#[cfg(kani)]\n#[allow(non_snake_case)]\n#[path="NCM_multiproof.rs"]\nmod NCM_multiproof;\n')]:
 old=subprocess.check_output(['git','show','4bb3b3f:'+path],text=True);new=old+extra
 if path.endswith('/lib.rs'):new=new.replace('#![no_std]','#![no_std]\n#![cfg_attr(kani, feature(allocator_api))]')
 patch+=''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+path,tofile='b/'+path))
(E/'NCM_native.patch').write_text(patch)
(E/'NCM_NATIVE_SHAPES.json').write_text(json.dumps(shapes,indent=2)+'\n')
assert len(shapes)==25
