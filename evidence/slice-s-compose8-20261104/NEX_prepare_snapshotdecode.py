"""Frozen unrolled800 decoder, with full local digest/validator replies."""
from NEX_native_patch import E,frozen,helpers
from NEX_source_tools import calls
import subprocess,sys,json,difflib,re
mode=sys.argv[1];slot=int(sys.argv[2]);assert mode in ['positive','value','argument','reply','error'] and slot in range(6)
subprocess.run([sys.executable,str(E/'NEX_prepare_window.py'),'1','positive'],check=True)
p='crates/aspis-statement/src/pool_v1/pair_tree_profile.rs';f=frozen(p);name='decode_pool_v1_pair_live_snapshot_v1';a=f.index('pub fn '+name+'(');z=f.index('\n}',a)+2;original=f[a:z]
native=original.replace('pub fn '+name+'(','fn native(').replace('    bytes: &[u8],','    bytes: &[u8], f:&mut Frame,')
native=calls(native,'decode_digest_canonical','digest','f');native=calls(native,'validate_pool_v1_pair_live_snapshot_v1','validate','f')
if mode=='argument':native=native.replace('bytes[128..160]','bytes[129..161]')
if mode=='reply':native=native.replace('current_root,','current_root: [aspis_core::field::M31(0);8],',1)
if mode=='error':native=native.replace('::NonCanonicalDigest','::WrongMagic')
fields=['pool[j] as u64','deployment_domain[j] as u64','sequence','next_pair_index','current_root[i].0 as u64','frontier[k][i].0 as u64']
expected=['f.bytes[48+j] as u64','f.bytes[80+j] as u64','u64::from_le_bytes(f.bytes[112..120].try_into().unwrap())','u64::from_le_bytes(f.bytes[120..128].try_into().unwrap())','f.replies[0][i].0 as u64','f.replies[1+k][i].0 as u64']
check='assert!(s.'+fields[slot]+'=='+expected[slot]+('^1' if mode=='value' else '')+');'
base=helpers().replace('aspis_statement::','crate::')+(E/'NEX_atom_error.rs.txt').read_text()
body=base+f'''
struct Frame<'a>{{bytes:&'a [u8;800],replies:&'a [Digest;21],fail_at:usize,reply:Result<(),PoolV1PairLiveSnapshotErrorV1>,digests:usize,validations:u8,i:usize,k:usize,j:usize}}
fn digest(bytes:&[u8;32],f:&mut Frame)->Result<Digest,crate::AtomicStatementError>{{let n=f.digests;assert!(n<21);assert!(bytes[f.j]==f.bytes[128+32*n+f.j]);f.digests+=1;if n==f.fail_at{{Err(NEX_atom_error())}}else{{Ok(f.replies[n])}}}}
fn validate(s:&PoolV1PairLiveSnapshotV1,f:&mut Frame)->Result<(),PoolV1PairLiveSnapshotErrorV1>{{assert!(f.digests==21&&f.validations==0);let i=f.i;let k=f.k;let j=f.j;{check}f.validations=1;f.reply}}
'''+native+f'''
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
fn snapshotdecode(){{let bytes:[u8;800]=kani::any();let replies:[Digest;21]=core::array::from_fn(|_|NEE_digest());let fail_at:usize=kani::any();let i:usize=kani::any();let k:usize=kani::any();let j:usize=kani::any();kani::assume(fail_at<=21&&i<8&&k<20&&j<32);let reply=if kani::any(){{Ok(())}}else{{Err(NEE_any_PoolV1PairLiveSnapshotErrorV1())}};let mut f=Frame{{bytes:&bytes,replies:&replies,fail_at,reply,digests:0,validations:0,i,k,j}};let result=native(&bytes,&mut f);
let header=if @MAGIC@{{Err(PoolV1PairLiveSnapshotErrorV1::WrongMagic)}}else if bytes[8]!=POOL_V1_PAIR_LIVE_SNAPSHOT_VERSION{{Err(PoolV1PairLiveSnapshotErrorV1::WrongVersion)}}else if @RESERVED@{{Err(PoolV1PairLiveSnapshotErrorV1::NonZeroReserved)}}else if @BINDING@{{Err(PoolV1PairLiveSnapshotErrorV1::WrongFormatBinding)}}else{{Ok(())}};
match header{{Err(e)=>{{assert!(f.digests==0&&f.validations==0);assert!(matches!(result,Err(x) if x==e));}},Ok(())=>if fail_at<21{{assert!(f.digests==fail_at+1&&f.validations==0);assert!(matches!(result,Err(PoolV1PairLiveSnapshotErrorV1::NonCanonicalDigest)));}}else{{assert!(f.digests==21&&f.validations==1);match (result,reply){{(Ok(s),Ok(()))=>{{{check}}},(Err(x),Err(e))=>assert!(x==e),_=>assert!(false)}}}}}}}}
'''
body=body.replace('@MAGIC@','||'.join(f'bytes[{i}]!=POOL_V1_PAIR_LIVE_SNAPSHOT_MAGIC[{i}]' for i in range(8))).replace('@RESERVED@','||'.join(f'bytes[{i}]!=0' for i in range(9,16))).replace('@BINDING@','||'.join(f'bytes[{16+i}]!=POOL_V1_PAIR_TREE_FORMAT_BINDING[{i}]' for i in range(32)))
h=f+'\n#[cfg(kani)]\n#[path="NEX_snapshotdecode.rs"]\nmod NEX_snapshotdecode;\n';patch=''.join(difflib.unified_diff(f.splitlines(True),h.splitlines(True),fromfile='a/'+p,tofile='b/'+p))+'--- /dev/null\n+++ b/crates/aspis-statement/src/pool_v1/NEX_snapshotdecode.rs\n@@ -0,0 +1,'+str(len(body.splitlines()))+' @@\n'+''.join('+'+l+'\n' for l in body.splitlines());(E/'NEX_native_contracts.patch').write_text(patch)
(E/'NEX_SNAPSHOTDECODE_CURRENT.json').write_text(json.dumps(dict(mode=mode,full_child_Result=True,slot=slot,frozen_body=original,native=native,source=body,domain='all live800-byte slices; arbitrary full digest values, earliest failure index0..21; every validation Result/error; arbitrary indices',classification='ruling y frozen unrolled21 calls, exact read windows, header rejection order, complete returned fields; no native loop, no arithmetic stub'),indent=1))
