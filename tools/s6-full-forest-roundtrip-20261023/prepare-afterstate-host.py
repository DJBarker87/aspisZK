#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,shutil,sys
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021');O=H/sys.argv[1];O.mkdir(exist_ok=False)
source=H/'aspis-s6-native-digest-codec-v2'
shutil.copytree(source/'frozen-source',O/'frozen-source')
for n in ['Cargo.toml','frozen-statement-binding.json']:shutil.copyfile(source/n,O/n)
p=O/'Cargo.toml';p.write_text(p.read_text().replace('aspis-s6-native-digest-codec','aspis-s6-native-afterstate-loop'))
reference=json.loads((source/'source-manifest.json').read_text())['reference']
rust=(O/'frozen-source/crates/aspis-statement/src/pool_v1/pair_terminal.rs').read_text()
marker='for (level, node) in afterstate.next_frontier.iter().enumerate() {';a=rust.index(marker);b=rust.index('\n    }',a)+len('\n    }');original=rust[a:b]
unrolled='\n'.join(f'output[{48+32*i}..{80+32*i}].copy_from_slice(&encode_digest_canonical(&afterstate.next_frontier[{i}]));' for i in range(20))
(O/'src').mkdir();(O/'src/lib.rs').write_text('''#![allow(unexpected_cfgs)]
#[cfg(kani)]
mod proofs {
 use aspis_statement::{poseidon2::Digest,atomic_statement::encode_digest_canonical,pool_v1::pair_terminal::PoolV1PairVerifiedAfterstateV1 as Afterstate};
'''+reference+'''
 fn original_loop(afterstate:&Afterstate,output:&mut[u8;688]) {'''+original+'''}
 fn unrolled_loop(afterstate:&Afterstate,output:&mut[u8;688]) {'''+unrolled+'''}
 #[kani::proof]
 #[kani::stub(aspis_statement::atomic_statement::encode_digest_canonical, reference)]
 #[kani::unwind(128)]
 fn afterstate_loop_matches_unrolled_on_exact_frame() {
  // Complete original native afterstate, no fabricated enum/pointer/reference.
  let afterstate:Afterstate=unsafe{core::mem::transmute(kani::any::<[u8;core::mem::size_of::<Afterstate>()]>())};
  let before:[u8;688]=kani::any();let mut left=before;let mut right=before;
  let index:usize=kani::any();kani::assume(index<688);
  original_loop(&afterstate,&mut left);unrolled_loop(&afterstate,&mut right);
  assert_eq!(left[index],right[index]);
 }
}
''')
(O/'source-manifest.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',reference=reference,original_loop_fragment=original,unrolled_loop_fragment=unrolled,native_reference_predecessor='s6-native-digest-encoder-v2',scope='Full original native Afterstate, arbitrary688-byte initial mutable frame, all output indexes. Exact source frontier foreach versus fixed20 writes. Surrounding validator/header and native SDK execution are not replaced or claimed proved.',qualification='Only digest encode uses the complete checked concrete equivalent. No opaque/arbitrary output stub, simplified afterstate carrier or success/canonicality assumption. Exact688-byte caller frame only, not standalone serializer equivalence at arbitrary slice lengths.'),indent=2)+'\n')
print(O)
