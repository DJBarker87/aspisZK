"""One frozen outer scan/advance cut with a local unconstrained child reply."""
from pathlib import Path
import json,lzma,hashlib
E=Path(__file__).resolve().parent;src=json.loads(lzma.decompress((E/'NGQ_FROZEN_INPUTS.json.xz').read_bytes()))['crates/aspis-core/src/r0_transcript.rs']
a=src.index('        if scan.scan(&blocks[k]) {',src.index('pub fn queries_from_pairs'));b=src.index('\n    }',a)
original=src[a:b];assert original.endswith('        }')
s='''#[derive(Clone,Copy)]
struct NGQ_ScanFields {accepted:[u32;22],len:usize,draws:usize}
fn NGQ_outer_step(blocks:&[[u8;32];8],advances:&[[u8;32];8],k:usize,
 before:NGQ_ScanFields,prior_state:[u8;32],reply:NGQ_ScanFields,stop:bool,j:usize,i:usize)
 ->(bool,NGQ_ScanFields,[u8;32],(u8,u32,usize,usize)) {
 // The local callee observation precedes the arbitrary full child mutation.
 let log=(blocks[k][j],before.accepted[i],before.len,before.draws);
 let after=reply;
 let mut state=prior_state;
 if stop {state=advances[k];}
 (stop,after,state,log)
}
#[kani::proof] #[kani::unwind(34)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn NGQ_outer_step_check() {
 let blocks:[[u8;32];8]=kani::any();let advances:[[u8;32];8]=kani::any();
 let k:usize=kani::any();let j:usize=kani::any();let i:usize=kani::any();kani::assume(k<8 && j<32 && i<22);
 let before=NGQ_ScanFields{accepted:kani::any(),len:kani::any(),draws:kani::any()};
 kani::assume(before.len<=22 && before.draws<=64);
 let reply=NGQ_ScanFields{accepted:kani::any(),len:kani::any(),draws:kani::any()};
 let prior_state:[u8;32]=kani::any();let stop:bool=kani::any();
 let (halt,after,state,log)=NGQ_outer_step(&blocks,&advances,k,before,prior_state,reply,stop,j,i);
 let correct=halt==stop && after.accepted[i]==reply.accepted[i] && after.len==reply.len && after.draws==reply.draws
  && state[j]==if stop {advances[k][j]}else{prior_state[j]}
  && log==(blocks[k][j],before.accepted[i],before.len,before.draws);
 #[cfg(not(NGQ_invert))] assert!(correct);
 #[cfg(NGQ_invert)] assert!(!correct);
}
#[kani::proof] #[kani::unwind(34)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn NGQ_default() {
 let s=QueryScan::default();let j:usize=kani::any();kani::assume(j<22);
 let correct=s.accepted[j]==0 && s.accepted_len==0 && s.draws==0;
 #[cfg(not(NGQ_invert))] assert!(correct);
 #[cfg(NGQ_invert)] assert!(!correct);
}
'''
(E/'NGQ_driver_step.rs.txt').write_text(s)
(E/'NGQ_OUTER_CUT.json').write_text(json.dumps(dict(start=a,end=b,sha256=hashlib.sha256(original.encode()).hexdigest(),substitutions=['scan.scan borrowed block and SAME prestate -> local log + arbitrary full reply and modifies','break -> returned halt flag'],qualification='SOURCE-FISSION SUPPORT; model/iteration association required before closure'),indent=1)+'\n')
p=E/'NGQ_core_harness.rs.txt';t=p.read_text();t=t.split('// NGQ generated outer cut')[0];p.write_text(t+'// NGQ generated outer cut\n'+s)
