"""Full frozen1520-byte late parent, with actual Box/error child carriers."""
from NEX_native_patch import E,frozen,helpers
from NEX_source_tools import calls
import subprocess,sys,json,difflib
mode=sys.argv[1];assert mode in ['positive','value','allocation','argument','reply','index']
subprocess.run([sys.executable,str(E/'NEX_prepare_window.py'),'1','positive'],check=True)
p='crates/aspis-statement/src/pool_v1/pair_tree_profile.rs';f=frozen(p);name='decode_pool_v1_pair_late_public_statement_boxed_v1';a=f.index('pub(crate) fn '+name+'(');z=f.index('\n}',a)+2;original=f[a:z]
native=original.replace('pub(crate) fn '+name+'(','fn native(').replace('    bytes: &[u8],','    bytes: &[u8],f:&mut Frame,')
native=calls(native,'decode_pair_live_snapshot_boxed_v1','snapshot','f');native=calls(native,'decode_pair_afterstate_boxed_v1','afterstate','f')
native=native.replace('Ok(Box::new(PoolV1PairLatePublicStatementV1 {','let out=Box::new(PoolV1PairLatePublicStatementV1 {').replace('    }))','    });\n    f.allocated=&*out;\n    Ok(out)')
if mode=='allocation':native=native.replace('Ok(out)','Ok(Box::new(*out))')
if mode=='argument':native=native.replace('bytes[32..32 + POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES]','bytes[33..32 + POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES]')
if mode=='index':native=native.replace('.checked_add(1)','.checked_add(2)')
fields=['live_snapshot.pool[j] as u64','live_snapshot.deployment_domain[j] as u64','live_snapshot.sequence','live_snapshot.next_pair_index','live_snapshot.current_root[i].0 as u64','live_snapshot.frontier[k][i].0 as u64','candidate_afterstate.next_pair_index','candidate_afterstate.next_root[i].0 as u64','candidate_afterstate.next_frontier[k][i].0 as u64']
left='match slot{'+','.join(str(i)+'=>out.'+x for i,x in enumerate(fields))+',_=>0}';right=left.replace('out.','expected.')
if mode=='value':right='('+right+')^1'
body=helpers().replace('aspis_statement::','crate::')+'''
struct Frame<'a>{bytes:&'a [u8;1520],live:Result<PoolV1PairLiveSnapshotV1,PoolV1PairLatePublicStatementErrorV1>,after:Result<PoolV1PairVerifiedAfterstateV1,PoolV1PairLatePublicStatementErrorV1>,calls:u8,allocated:*const PoolV1PairLatePublicStatementV1}
fn snapshot(bytes:&[u8],f:&mut Frame)->Result<Box<PoolV1PairLiveSnapshotV1>,PoolV1PairLatePublicStatementErrorV1>{assert!(f.calls==0&&bytes.len()==800&&core::ptr::eq(bytes.as_ptr(),f.bytes[32..].as_ptr()));f.calls=1;f.live.map(Box::new)}
fn afterstate(bytes:&[u8],f:&mut Frame)->Result<Box<PoolV1PairVerifiedAfterstateV1>,PoolV1PairLatePublicStatementErrorV1>{assert!(f.calls==1&&bytes.len()==688&&core::ptr::eq(bytes.as_ptr(),f.bytes[832..].as_ptr()));f.calls=2;f.after.map(Box::new)}
'''+native+f'''
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
fn late(){{let bytes:[u8;1520]=kani::any();let c=NEE_common();let live=if kani::any(){{Ok(c.lane_transition.live_snapshot)}}else{{Err(NEE_any_PoolV1PairLatePublicStatementErrorV1())}};let after=if kani::any(){{Ok(c.lane_transition.candidate_afterstate)}}else{{Err(NEE_any_PoolV1PairLatePublicStatementErrorV1())}};let mut f=Frame{{bytes:&bytes,live,after,calls:0,allocated:core::ptr::null()}};let i:usize=kani::any();let j:usize=kani::any();let k:usize=kani::any();let slot:usize=kani::any();kani::assume(i<8&&j<32&&k<20&&slot<9);let actual=native(&bytes,&mut f);
let header=if @MAGIC@{{Err(PoolV1PairLatePublicStatementErrorV1::WrongMagic)}}else if bytes[8]!=POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_VERSION{{Err(PoolV1PairLatePublicStatementErrorV1::WrongVersion)}}else if bytes[9]!=POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_ITEM_COUNT{{Err(PoolV1PairLatePublicStatementErrorV1::WrongItemCount)}}else if u16::from_le_bytes(bytes[10..12].try_into().unwrap()) as usize !=32{{Err(PoolV1PairLatePublicStatementErrorV1::WrongHeaderLength)}}else if u32::from_le_bytes(bytes[12..16].try_into().unwrap()) as usize !=800{{Err(PoolV1PairLatePublicStatementErrorV1::WrongSnapshotLength)}}else if u32::from_le_bytes(bytes[16..20].try_into().unwrap()) as usize !=688{{Err(PoolV1PairLatePublicStatementErrorV1::WrongAfterstateLength)}}else if u32::from_le_bytes(bytes[20..24].try_into().unwrap()) as usize !=1520{{Err(PoolV1PairLatePublicStatementErrorV1::WrongTotalLength)}}else if @RESERVED@{{Err(PoolV1PairLatePublicStatementErrorV1::NonZeroReserved)}}else{{Ok(())}};
match header{{Err(e)=>{{assert!(f.calls==0&&f.allocated.is_null());assert!(matches!(actual,Err(x) if x==e));}},Ok(())=>match live{{Err(e)=>{{assert!(f.calls==1&&f.allocated.is_null());assert!(matches!(actual,Err(x) if x==e));}},Ok(live)=>match after{{Err(e)=>{{assert!(f.calls==2&&f.allocated.is_null());assert!(matches!(actual,Err(x) if x==e));}},Ok(after)=>{{assert!(f.calls==2);if live.next_pair_index.checked_add(1)!=Some(after.next_pair_index){{assert!(f.allocated.is_null());assert!(matches!(actual,Err(PoolV1PairLatePublicStatementErrorV1::AfterstateIndexMismatch)));}}else{{let out=actual.unwrap();let expected=PoolV1PairLatePublicStatementV1{{live_snapshot:live,candidate_afterstate:after}};assert!(core::ptr::eq(&*out,f.allocated));assert!(({left})==({right}));}}}}}}}}}}}}
'''
body=body.replace('@MAGIC@','||'.join(f'bytes[{i}]!=POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_MAGIC[{i}]' for i in range(8))).replace('@RESERVED@','||'.join(f'bytes[{i}]!=0' for i in range(24,32)))
if mode=='reply':body=body.replace('f.after.map(Box::new)','f.after.map(|mut a|{a.next_root=[aspis_core::field::M31(0);8];Box::new(a)})')
h=f+'\n#[cfg(kani)]\n#[path="NEX_late.rs"]\nmod NEX_late;\n';patch=''.join(difflib.unified_diff(f.splitlines(True),h.splitlines(True),fromfile='a/'+p,tofile='b/'+p))+'--- /dev/null\n+++ b/crates/aspis-statement/src/pool_v1/NEX_late.rs\n@@ -0,0 +1,'+str(len(body.splitlines()))+' @@\n'+''.join('+'+l+'\n' for l in body.splitlines());(E/'NEX_native_contracts.patch').write_text(patch)
(E/'NEX_LATE_CURRENT.json').write_text(json.dumps(dict(mode=mode,full_child_Result=True,frozen_body=original,native=native,source=body,fields=fields,domain='all live1520 bytes and all typed child boxed Results/errors; arbitrary observed fields; no index or header restriction',classification='ruling y typed Box/error callbacks, aa same allocation and error frames, exact two child slices, ordered headers and checked-add guard'),indent=1))
