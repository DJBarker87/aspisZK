#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,shutil,sys
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021');O=H/sys.argv[1];O.mkdir(exist_ok=False)
source=H/'aspis-s6-native-digest-codec-v2';shutil.copytree(source/'frozen-source',O/'frozen-source')
for n in ['Cargo.toml','frozen-statement-binding.json']:shutil.copyfile(source/n,O/n)
p=O/'Cargo.toml';p.write_text(p.read_text().replace('aspis-s6-native-digest-codec','aspis-s6-native-validators'))
def item(text,marker):
 a=text.index(marker);i=text.index('{',a);j=i+1;depth=1
 while depth:depth+=(text[j]=='{')-(text[j]=='}');j+=1
 return text[a:j]
def replace_loop(text,field,error):
 a=text.index('    let mut level = 0;');loop=item(text[a:],f'while level < {field}.len()');b=text.index(loop,a)+len(loop)
 unrolled='\n'.join(f'    if !digest_is_canonical(&{field}[{i}]) {{return Err({error});}}' for i in range(20))
 return text[:a]+unrolled+text[b:]
root=O/'frozen-source/crates/aspis-statement/src/pool_v1'
tree=(root/'pair_tree_profile.rs').read_text();terminal=(root/'pair_terminal.rs').read_text()
snapshot=item(tree,'fn validate_pool_v1_pair_live_snapshot_v1(')
afterstate=item(terminal,'fn validate_verified_afterstate(')
sref=replace_loop(snapshot,'snapshot.frontier','PoolV1PairLiveSnapshotErrorV1::NonCanonicalDigest').replace('fn validate_pool_v1_pair_live_snapshot_v1','fn reference_snapshot',1)
aref=replace_loop(afterstate,'afterstate.next_frontier','PoolV1PairVerifierTransportErrorV1::NonCanonicalAfterstate').replace('fn validate_verified_afterstate','fn reference_afterstate',1).replace('super::pair_tree_profile::digest_is_canonical','digest_is_canonical').replace('super::POOL_V1_PAIR_CAPACITY','POOL_V1_PAIR_CAPACITY')
extra_tree='''\n#[cfg(kani)]
pub fn kani_validate_snapshot(s:&PoolV1PairLiveSnapshotV1)->Result<(),PoolV1PairLiveSnapshotErrorV1>{validate_pool_v1_pair_live_snapshot_v1(s)}
#[cfg(kani)]
pub fn kani_digest_canonical(d:&Digest)->bool{digest_is_canonical(d)}
'''
extra_terminal='''\n#[cfg(kani)]
pub fn kani_validate_afterstate(s:&PoolV1PairVerifiedAfterstateV1)->Result<(),PoolV1PairVerifierTransportErrorV1>{validate_verified_afterstate(s)}
'''
(root/'pair_tree_profile.rs').write_text(tree+extra_tree);(root/'pair_terminal.rs').write_text(terminal+extra_terminal)
(O/'src').mkdir();(O/'src/lib.rs').write_text('''#![allow(unexpected_cfgs)]
#[cfg(kani)]
mod proofs {
 use aspis_statement::pool_v1::{
  pair_tree_profile::{PoolV1PairLiveSnapshotV1,PoolV1PairLiveSnapshotErrorV1,kani_validate_snapshot,kani_digest_canonical as digest_is_canonical},
  pair_terminal::{PoolV1PairVerifiedAfterstateV1,PoolV1PairVerifierTransportErrorV1,kani_validate_afterstate},
  POOL_V1_PAIR_CAPACITY};
'''+sref+'\n'+aref+'''
 #[kani::proof]
 #[kani::unwind(128)]
 fn snapshot_validator_matches_unrolled() {
  let value:PoolV1PairLiveSnapshotV1=unsafe{core::mem::transmute(kani::any::<[u8;core::mem::size_of::<PoolV1PairLiveSnapshotV1>()]>())};
  assert_eq!(kani_validate_snapshot(&value),reference_snapshot(&value));
 }
 #[kani::proof]
 #[kani::unwind(128)]
 fn afterstate_validator_matches_unrolled() {
  let value:PoolV1PairVerifiedAfterstateV1=unsafe{core::mem::transmute(kani::any::<[u8;core::mem::size_of::<PoolV1PairVerifiedAfterstateV1>()]>())};
  assert_eq!(kani_validate_afterstate(&value),reference_afterstate(&value));
 }
}
''')
(O/'source-binding.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',original_snapshot=snapshot,reference_snapshot=sref,original_afterstate=afterstate,reference_afterstate=aref,proof_only_wrappers={'pair_tree_profile.rs':extra_tree,'pair_terminal.rs':extra_terminal},original_file_hashes={'pair_tree_profile.rs':hashlib.sha256(tree.encode()).hexdigest(),'pair_terminal.rs':hashlib.sha256(terminal.encode()).hexdigest()},qualification='Complete actual native validators via proof-only private-API exposure wrappers; original bodies unchanged. Concrete unrolled references retain every input field and exact Rust Err variants. No child stubs or canonicality/success/output assumptions. Ordinary release sources unchanged after stripping cfg(kani) wrappers.'),indent=2)+'\n')
print(O)
