#!/usr/bin/env python3
from pathlib import Path
import json,shutil,sys
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021');O=H/sys.argv[1];O.mkdir(exist_ok=False);base=H/'aspis-s6-native-frontier-loop-v1'
shutil.copytree(base/'frozen-source',O/'frozen-source')
for name in ['Cargo.toml','frozen-statement-binding.json']:shutil.copyfile(base/name,O/name)
p=O/'Cargo.toml';p.write_text(p.read_text().replace('aspis-s6-native-frontier-loop','aspis-s6-native-snapshot-step-loop'))
m=json.loads((base/'source-manifest.json').read_text());reference=m['reference'];fragment=m['original_loop_fragment']
step="""pub fn frontier_step(snapshot:&Snapshot,output:&mut[u8],level:usize) {
 let start=160+32*level;
 output[start..start+32].copy_from_slice(&encode_digest_canonical(&snapshot.frontier[level]));
}
"""
loop="""pub fn frontier_loop(snapshot:&Snapshot,output:&mut[u8]) {
 for level in 0..20 {frontier_step(snapshot,output,level);}
}
"""
(O/'src').mkdir();(O/'src/lib.rs').write_text("""#![allow(unexpected_cfgs)]
use aspis_statement::{atomic_statement::encode_digest_canonical,pool_v1::pair_tree_profile::PoolV1PairLiveSnapshotV1 as Snapshot};
"""+step+loop+"""
#[cfg(kani)] mod proofs {
 use super::*;
 use aspis_statement::poseidon2::Digest;
"""+reference+'\nfn original_loop(snapshot:&Snapshot,output:&mut[u8]) {'+fragment+"""}
 #[kani::proof]
 #[kani::stub(aspis_statement::atomic_statement::encode_digest_canonical, reference)]
 #[kani::unwind(128)]
 fn original_frontier_matches_helper_loop() {
  let snapshot:Snapshot=unsafe{core::mem::transmute(kani::any::<[u8;core::mem::size_of::<Snapshot>()]>())};
  let before:[u8;800]=kani::any();let mut left=before;let mut right=before;
  let index:usize=kani::any();kani::assume(index<800);
  original_loop(&snapshot,&mut left);frontier_loop(&snapshot,&mut right);
  assert_eq!(left[index],right[index]);
 }
}
""")
m.update(step_helper=step,helper_loop=loop,scope='Complete native Snapshot and original mutable Slice carrier, arbitrary800-byte initial frame and every output byte: frozen foreach versus helper loop. Only digest uses its separately checked concrete equivalent. No canonicality or child-success assumptions.',qualification='Proof reference only. Native equivalence must precede focused extraction and loop induction. Enclosing runtime/source transport, standalone wrong-length control, SDK and any artifact re-pin gates remain explicit.')
(O/'source-manifest.json').write_text(json.dumps(m,indent=2)+'\n');print(O)
