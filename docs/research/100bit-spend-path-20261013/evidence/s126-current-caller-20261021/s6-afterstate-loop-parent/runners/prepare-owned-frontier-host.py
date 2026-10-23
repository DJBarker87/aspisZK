#!/usr/bin/env python3
from pathlib import Path
import json,shutil,sys
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021');O=H/sys.argv[1];O.mkdir(exist_ok=False);base=H/'aspis-s6-native-afterstate-loop-v1'
shutil.copytree(base/'frozen-source',O/'frozen-source')
for name in ['Cargo.toml','frozen-statement-binding.json']:shutil.copyfile(base/name,O/name)
p=O/'Cargo.toml';p.write_text(p.read_text().replace('aspis-s6-native-afterstate-loop','aspis-s6-native-owned-frontier'))
m=json.loads((base/'source-manifest.json').read_text());reference=m['reference'];fragment=m['original_loop_fragment']
step="""pub fn frontier_step(afterstate:&Afterstate,mut output:[u8;688],level:usize)->[u8;688] {
 let start=48+32*level;
 output[start..start+32].copy_from_slice(&encode_digest_canonical(&afterstate.next_frontier[level]));
 output
}
"""
loop="""pub fn frontier_owned(afterstate:&Afterstate,mut output:[u8;688])->[u8;688] {
 for level in 0..20 {output=frontier_step(afterstate,output,level);}
 output
}
"""
(O/'src').mkdir();(O/'src/lib.rs').write_text("""#![allow(unexpected_cfgs)]
use aspis_statement::{atomic_statement::encode_digest_canonical,pool_v1::pair_terminal::PoolV1PairVerifiedAfterstateV1 as Afterstate};
"""+step+loop+"""
#[cfg(kani)] mod proofs {
 use super::*;
 use aspis_statement::poseidon2::Digest;
"""+reference+'\nfn original_loop(afterstate:&Afterstate,output:&mut[u8;688]) {'+fragment+"""}
 #[kani::proof]
 #[kani::stub(aspis_statement::atomic_statement::encode_digest_canonical, reference)]
 #[kani::unwind(128)]
 fn original_frontier_matches_owned_loop() {
  let afterstate:Afterstate=unsafe{core::mem::transmute(kani::any::<[u8;core::mem::size_of::<Afterstate>()]>())};
  let before:[u8;688]=kani::any();let mut left=before;
  let index:usize=kani::any();kani::assume(index<688);
  original_loop(&afterstate,&mut left);let right=frontier_owned(&afterstate,before);
  assert_eq!(left[index],right[index]);
 }
}
""")
m.update(owned_step=step,owned_loop=loop,scope='Complete native Afterstate, arbitrary688-byte initial frame, every output byte: original frozen foreach versus owned-buffer helper loop. Only digest encoding uses its previously checked exact concrete equivalent. No simplified carrier, child-success or canonicality assumption.',qualification='Isolated proof reference, not production adoption. Native whole-fragment equivalence must pass, then focused extraction and step/loop induction. Enclosing source/contextual, runtime/SDK and re-pin gates remain explicit.')
(O/'source-manifest.json').write_text(json.dumps(m,indent=2)+'\n')
print(O)
