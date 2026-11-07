from pathlib import Path
import re,json,hashlib
E=Path(__file__).resolve().parent
frozen=Path('programs/r1-cost-probe/src/r1_pool_adapter.rs').read_text()
s=frozen[frozen.index('    if bytes.len() != POOL_V1_PAIR_FOREST_LANE_ACCOUNT_BYTES'):]
s=s[:s.index('    let root = decode_digest_canonical(')]
assert s.count('bytes.len()')==1
source=s.replace('bytes.len()','logical_len')
stubs='\n'.join(x for x in (E/'NMX_217_iteration.rs').read_text().splitlines() if x.startswith('#[kani::stub('))
stubs='\n'.join(dict.fromkeys(stubs.splitlines()))
prefix='''
// Complete frozen entry-to-first-digest segment. The borrowed prefix contains
// exactly original bytes[0..128]; logical_len is the original slice metadata.
struct NMX_prefix_state { master:[u8;32], lane:u8, bump:u8, next:u64, root_window:[u8;32] }
fn NMX_prefix_observe(p:&NMX_prefix_state,j:usize)->u64 {
 match j {0=>p.lane as u64,1=>p.bump as u64,2=>p.next,
  3..=34=>p.master[j-3] as u64,_=>p.root_window[j-35] as u64}
}
fn NMX_prefix_reference(b:&[u8;128],n:usize)->Option<NMX_prefix_state>{
 if n!=768{return None}
 if !R::equal(&b[..4],b"ASL8")||b[4]!=2||b[5]>=8||b[6]!=8||b[7]!=20||!R::equal(&b[8..40],&R::BINDING)||!R::zero(&b[73..80]){return None}
 let master=R::bytes32(b,40);if R::zero(&master){return None}
 let t=&b[80..];if !R::equal(&t[..4],b"ASPT")||t[4]!=1||t[5]!=20||t[6]!=3||t[7]!=1{return None}
 let next=R::word64(t,8);if next>1048576{return None}
 Some(NMX_prefix_state{master,lane:b[5],bump:b[72],next,root_window:R::bytes32(t,16)})
}
fn NMX_prefix_post(r:bool)->bool {r != INVERSE}
#[kani::requires(j<67)]
#[kani::modifies()]
#[kani::ensures(|r:&bool| NMX_prefix_post(*r))]
fn NMX_prefix(bytes:&[u8;128],logical_len:usize,j:usize)->bool {
 let actual:Result<NMX_prefix_state,ProgramError>=(||{
'''+source+'''
    let root_window:[u8;32]=tree[16..48].try_into().map_err(|_|ProgramError::InvalidAccountData)?;
    Ok(NMX_prefix_state{master,lane:bytes[5],bump:bytes[72],next:next_leaf_index,root_window})
 })();
 match (actual,NMX_prefix_reference(bytes,logical_len)) {
  (Err(ProgramError::InvalidAccountData),None)=>true,
  (Ok(a),Some(b))=>NMX_prefix_observe(&a,j)==NMX_prefix_observe(&b,j),
  _=>false,
 }
}
#[kani::proof_for_contract(NMX_prefix)]
'''+stubs+'''
#[kani::unwind(34)]
fn NMX_prefix_contract(){let bytes:[u8;128]=kani::any();let logical_len:usize=kani::any();let j:usize=kani::any();kani::assume(j<67);let _=NMX_prefix(&bytes,logical_len,j);}
'''
p=E/'NMX_217_iteration.rs';old=p.read_text();assert 'fn NMX_prefix(' not in old;p.write_text(old+prefix)
(E/'NMX_217_PREFIX_CUT.json').write_text(json.dumps({'source':'programs/r1-cost-probe/src/r1_pool_adapter.rs','source_revision':'4bb3b3f51e16b4525f1d10336e2b0bcbbd775387','source_sha256':hashlib.sha256(frozen.encode()).hexdigest(),'segment':'entry to immediately before first decode_digest_canonical child','substitutions':{'bytes.len()':'logical_len'},'borrowed_window':'original bytes[0..128]','logical_len':'original bytes.len(), every usize','native_outcomes':'all errors are exact InvalidAccountData; success records exact next call window, master, lane, bump and counter','observations':67,'source_segment_sha256':hashlib.sha256(s.encode()).hexdigest()},indent=2)+'\n')
