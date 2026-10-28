from NCD_generate import *
import re,json
source=subprocess.check_output(['git','show','4bb3b3f5:crates/aspis-r1-cost-probe/src/transcript.rs'],text=True)
checks=[]
for i in range(8):
 fragment=f'blocks[{i}]=self.hash.digest(&[&state,&[1]]);\n        advances[{i}]=self.hash.digest(&[&state,&[2]]);'+(f'state=advances[{i}];' if i<7 else '')
 assert fragment in source,fragment
 checks.append(dict(pair=i,state_update=i<7,source_fragment=fragment,sha256=hashlib.sha256(fragment.encode()).hexdigest()))
(E/'NCD_PAIR_SOURCE.json').write_text(json.dumps(dict(frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',fragments=checks),indent=2)+'\n')
t='''
#[cfg(kani)] mod NCD_query_pair {
 use super::*;
 #[derive(Clone,Copy)] struct Spy;
 static mut CALLS:usize=0;static mut J:usize=0;
 static mut INITIAL:[u8;32]=[0;32];static mut BLOCK:[u8;32]=[0;32];static mut ADVANCE:[u8;32]=[0;32];
 impl Digest32 for Spy{fn digest(&self,parts:&[&[u8]])->[u8;32]{unsafe{
  let c=CALLS;assert!(c<2);CALLS+=1;
  assert!(parts.len()==2&&parts[0].len()==32&&parts[0][J]==INITIAL[J]);
  assert!(parts[1].len()==1&&parts[1][0]==if c==0{1}else{2});
  if c==0{BLOCK}else{ADVANCE}
 }}}
'''
for claim in ['requests','block_cell','advance_cell','block_frame','advance_frame','state','metadata']:
 t+='#[kani::proof] #[kani::unwind(512)]\n'+attrs+'fn '+claim+'(){\n'
 t+='''let mut blocks:[[u8;32];8]=kani::any();let mut advances:[[u8;32];8]=kani::any();let mut state:[u8;32]=kani::any();
 let pair:usize=kani::any();kani::assume(pair<8);let j:usize=kani::any();kani::assume(j<32);let k:usize=kani::any();kani::assume(k<8);
 let old_block=blocks[k][j];let old_advance=advances[k][j];let old_state=state[j];let bp=blocks.as_ptr();let ap=advances.as_ptr();
 unsafe{CALLS=0;J=j;INITIAL=state;BLOCK=kani::any();ADVANCE=kani::any();}
 blocks[pair]=Spy.digest(&[&state,&[1]]);
 advances[pair]=Spy.digest(&[&state,&[2]]);if pair<7{state=advances[pair];}
'''
 t+=dict(requests='unsafe{assert!(CALLS==2);}',block_cell='unsafe{assert!(blocks[pair][j]==BLOCK[j]);}',advance_cell='unsafe{assert!(advances[pair][j]==ADVANCE[j]);}',block_frame='if k!=pair{assert!(blocks[k][j]==old_block);}',advance_frame='if k!=pair{assert!(advances[k][j]==old_advance);}',state='unsafe{assert!(state[j]==if pair<7{ADVANCE[j]}else{old_state});}',metadata='assert!(blocks.as_ptr()==bp&&advances.as_ptr()==ap&&blocks.len()==8&&advances.len()==8);')[claim]+'\n}\n'
t+='}\n';emit('crates/aspis-r1-cost-probe/src/transcript.rs',t,'NCD_pair')
