"""Check the ordered digest-decode cut of the actual planner account codecs.
Additional native account metadata/semantic rejection paths remain in place.
"""
from pathlib import Path
import re,json,hashlib,subprocess
R=Path(__file__).resolve().parents[2]; E=R/'evidence/pv-l2c-20261028/resume-d371'
def compact(s): return re.sub(r'\s+','',s)
def sha(s): return hashlib.sha256(s.encode()).hexdigest()
def body(text,marker):
    a=text.index('{',text.index(marker));b=a+1;depth=1
    while depth:
        depth+=(text[b]=='{')-(text[b]=='}');b+=1
    return text[a+1:b-1]
native=(R/'crates/aspis-statement/src/pool_v1/incremental_merkle.rs').read_text()
probe=(R/'tools/pv-l2c-20261028/decoder-probe/main.rs').read_text()
original=body(native,'fn decode_tree_image_unvalidated(')
reference=body(probe,'fn tree_fields(')
root='''let root = decode_digest_canonical(bytes[16..48].try_into().unwrap())
    .map_err(|_| PoolV1TreeError::NonCanonicalDigest)?;'''
assert compact(root) in compact(original) and compact(root) in compact(reference)
loop_marker='for (level, node) in frontier.iter_mut().enumerate()'
actual_loop=body(original,loop_marker)
reference_loop=body(reference,'for (level,node) in frontier.iter_mut().enumerate()')
assert compact(actual_loop.replace('POOL_V1_TREE_STATE_HEADER_BYTES','48'))==compact(reference_loop)
assert compact('Ok(IncrementalMerkleTreeV1{next_leaf_index,root,frontier,})') in compact(original)
assert compact('Ok((root,frontier))') in compact(reference)
assert 'if bytes.len() != POOL_V1_TREE_STATE_ACCOUNT_BYTES' in original
assert 'pub const POOL_V1_TREE_STATE_HEADER_BYTES: usize = 48;' in native
format_source=(R/'crates/aspis-statement/src/pool_v1/format.rs').read_text()
assert 'pub const POOL_V1_TREE_DEPTH: usize = 20;' in format_source
poseidon=(R/'crates/aspis-statement/src/poseidon2.rs').read_text()
assert 'pub const DIGEST_ELEMS: usize = 8;' in poseidon
sealed=body(native,'    pub fn decode(\n        bytes: &[u8],\n        empty:')
assert compact(sealed)==compact('''let inner = decode_tree_image_unvalidated(bytes)?;
Self::from_parts(inner.next_leaf_index, inner.root, inner.frontier, empty)''')
parts=body(native,'    pub fn from_parts(\n        next_leaf_index: u64,\n        root: Digest,\n        frontier: [Digest; POOL_V1_TREE_DEPTH],\n        empty: &\'a')
assert compact(parts)==compact('''let inner = IncrementalMerkleTreeV1 { next_leaf_index, root, frontier, };
inner.validate_with_empty_roots(empty)?; Ok(Self { inner, empty })''')
accounts=(R/'crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs').read_text()
lane=body(accounts,'pub fn decode_pool_v1_pair_forest_lane_state_v1(')
assert compact('''let tree = IncrementalMerkleTreeV1::decode_with_empty_roots(&bytes[LANE_TREE_OFFSET..],pair_empty_roots,)?;''') in compact(lane)
assert 'const LANE_TREE_OFFSET: usize = POOL_V1_PAIR_FOREST_LANE_HEADER_BYTES;' in accounts
assert 'pub const POOL_V1_PAIR_FOREST_LANE_HEADER_BYTES: usize = 80;' in accounts
checkpoint=body(accounts,'pub fn decode_pool_v1_pair_forest_checkpoint_v1(')
assert compact('''let global_root = decode_digest_canonical(bytes[CHECKPOINT_GLOBAL_ROOT_OFFSET..CHECKPOINT_LANE_SEQUENCES_OFFSET].try_into().unwrap(),).map_err(|_| PoolV1PairForestAccountErrorV1::NonCanonicalDigest)?;''') in compact(checkpoint)
assert 'const CHECKPOINT_GLOBAL_ROOT_OFFSET: usize = 80;' in accounts
assert 'const CHECKPOINT_LANE_SEQUENCES_OFFSET: usize = 112;' in accounts
out={'revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),
 'classification':'structural (K-1 substitute), ordered digest field cut of account decoding; native differential pending',
 'native_tree_sha256':sha(native),'native_accounts_sha256':sha(accounts),'reference_main_sha256':sha(probe),
 'native_tree_field_loop_sha256':sha(actual_loop),'reference_tree_field_loop_sha256':sha(reference_loop),
 'field_order':'root 16..48 then frontier[level] at 48+32*level for every level 0..19, irrespective of active frontier bits',
 'lane_region':'80-byte lane header then all 688 tree bytes',
 'checkpoint_region':'80..112 global_root',
 'complete_result_reference':'PV_L2C_DigestList.run (ordered decoder calls, first error and all successful outputs retained)',
 'laws':['PV_L2C_DigestRange.digest_success','PV_L2C_DigestList.success','PV_L2C_DigestList.field',
   'PV_L2C_AccountLayout.bounds','PV_L2C_AccountLayout.frontier_offset','PV_L2C_AccountLayout.lane_bounds',
   'PV_L2C_AccountLayout.frontier'],
 'differences':[
   'The field cut begins after the native fixed-length/header checks; those may reject before the cut.',
   'The owned native comparison returns (root,frontier); native returns these identical fields alongside next_leaf_index.',
   'Lean records the ordered successful digest fields in a list; success proves length and same-position lookup, with root at 0 and frontier[j] at j+1.',
   'Native maps the fixed-array digest error to NonCanonicalDigest; the reference retains the underlying digest error. This changes only the error enum name at this cut, not which field rejects or its order.',
   'After parsing, from_parts validates by immutable borrow and returns the same inner tree, and into_inner returns that tree unchanged. Additional semantic/account checks may reject; no additional successful raw field constructor appears.'],
 'D188':'No account-codec Aeneas mutable-iterator emission is credited. The native field loop is checked directly against the owned native comparison, and the list reference law supplies the ordered range invariant.',
 'scope':'successful raw digest-field provenance only, not all account-error equality or a deployed observation theorem',
 'Kani':'none'}
root_source=(R/'programs/aspis-pool/src/empty_roots.rs').read_text()
assert (R/'tools/pv-l2c-20261028/decoder-probe/frozen_empty_roots.rs').read_text()==root_source.split('#[cfg(test)]')[0]
assert all(int(v.replace('_',''),0)<2147483647 for v in re.findall(r'M31\(([^)]+)\)',root_source.split('#[cfg(test)]')[0]))
out['frozen_empty_roots_source_sha256']=sha(root_source)
receipt=E/'account-probe4/receipt.json'
if receipt.exists():
    r=json.loads(receipt.read_text());assert r['exit']==0
    assert r['source_sha256']['main.rs']==sha(probe)
    assert 'noncanonical_account_rejections=704' in (E/'account-probe4/out.log').read_text()
    out['classification']='structural (K-1 substitute), ordered digest field cut of account decoding'
    out['native_differential']={'receipt':str(receipt.relative_to(R)),'receipt_sha256':hashlib.sha256(receipt.read_bytes()).hexdigest(),
       'label':'finite native validation: four successful lane field comparisons, four checkpoint roundtrips, 704 raw-P field rejections'}
(E/'account-source-check.json').write_text(json.dumps(out,indent=2)+'\n')
print('Checked native tree root/frontier field order, loop body, immutable validation return and lane/checkpoint composition')
