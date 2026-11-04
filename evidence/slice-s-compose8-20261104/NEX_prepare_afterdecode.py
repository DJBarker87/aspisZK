"""Unrolled frozen 688-byte decoder with full local child-reply interface."""
from NEX_native_patch import E,frozen,helpers
import subprocess,sys,json,difflib,hashlib
mode=sys.argv[1];slot=int(sys.argv[2]);assert mode in ['positive','value','argument','reply','error'] and slot in range(3)
subprocess.run([sys.executable,str(E/'NEX_prepare_window.py'),'1','positive'],check=True)
p='crates/aspis-statement/src/pool_v1/pair_terminal.rs';f=frozen(p);name='decode_pool_v1_pair_verified_afterstate_v1';a=f.index('pub fn '+name+'(');z=f.index('\n}',a)+2;original=f[a:z]
native=original.replace('pub fn '+name+'(','fn native(').replace('    bytes: &[u8],','    bytes: &[u8], f:&mut Frame,').replace('decode_digest_canonical(&exact(', 'digest(&exact(').replace('])?)','])?,f)').replace('validate_verified_afterstate(&afterstate)','validate(&afterstate,f)')
# The scalar exact(&bytes[8..16]) is not a digest call.
native=native.replace('u64::from_le_bytes(exact(&bytes[8..16])?,f)','u64::from_le_bytes(exact(&bytes[8..16])?)')
if mode=='argument':native=native.replace('exact(&bytes[16..48])','exact(&bytes[17..49])')
if mode=='reply':native=native.replace('next_root,','next_root: [aspis_core::field::M31(0);8],',1)
if mode=='error':native=native.replace('::NonCanonicalAfterstate','::WrongMagic')
fields=['next_pair_index','next_root[i].0 as u64','next_frontier[k][i].0 as u64'];expected=['u64::from_le_bytes(f.bytes[8..16].try_into().unwrap())','f.replies[0][i].0 as u64','f.replies[1+k][i].0 as u64']
check='assert!(s.'+fields[slot]+'=='+expected[slot]+('^1' if mode=='value' else '')+');'
base=helpers().replace('aspis_statement::','crate::')
body=base+f'''
struct Frame<'a>{{bytes:&'a [u8;688],replies:&'a [Digest;21],fail_at:usize,reply:Result<(),PoolV1PairVerifierTransportErrorV1>,digests:usize,validations:u8,i:usize,k:usize,j:usize}}
fn digest(bytes:&[u8;32],f:&mut Frame)->Result<Digest,()>{{let n=f.digests;assert!(n<21);assert!(bytes[f.j]==f.bytes[16+32*n+f.j]);f.digests+=1;if n==f.fail_at{{Err(())}}else{{Ok(f.replies[n])}}}}
fn validate(s:&PoolV1PairVerifiedAfterstateV1,f:&mut Frame)->Result<(),PoolV1PairVerifierTransportErrorV1>{{assert!(f.digests==21&&f.validations==0);let i=f.i;let k=f.k;{check}f.validations=1;f.reply}}
'''+native+f'''
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
fn afterdecode(){{let bytes:[u8;688]=kani::any();let replies:[Digest;21]=core::array::from_fn(|_|NEE_digest());let fail_at:usize=kani::any();let i:usize=kani::any();let k:usize=kani::any();let j:usize=kani::any();kani::assume(fail_at<=21&&i<8&&k<20&&j<32);let reply=if kani::any(){{Ok(())}}else{{Err(NEE_any_PoolV1PairVerifierTransportErrorV1())}};let mut f=Frame{{bytes:&bytes,replies:&replies,fail_at,reply,digests:0,validations:0,i,k,j}};let result=native(&bytes,&mut f);
let header=if bytes[0]!=65||bytes[1]!=83||bytes[2]!=86||bytes[3]!=49{{Err(PoolV1PairVerifierTransportErrorV1::WrongMagic)}}else if bytes[4]!=POOL_V1_PAIR_VERIFIER_TRANSPORT_VERSION{{Err(PoolV1PairVerifierTransportErrorV1::WrongVersion)}}else if bytes[5]!=super::super::POOL_V1_PAIR_TREE_STORAGE_FORMAT_VERSION{{Err(PoolV1PairVerifierTransportErrorV1::WrongPairFormat)}}else if bytes[6]!=POOL_V1_DIGEST_ENCODING_VERSION{{Err(PoolV1PairVerifierTransportErrorV1::WrongDigestEncoding)}}else if bytes[7]!=1{{Err(PoolV1PairVerifierTransportErrorV1::WrongSuccessCode)}}else{{Ok(())}};
match header{{Err(e)=>{{assert!(f.digests==0&&f.validations==0);assert!(matches!(result,Err(x) if x==e));}},Ok(())=>if fail_at<21{{assert!(f.digests==fail_at+1&&f.validations==0);assert!(matches!(result,Err(PoolV1PairVerifierTransportErrorV1::NonCanonicalAfterstate)));}}else{{assert!(f.digests==21&&f.validations==1);match (result,reply){{(Ok(s),Ok(()))=>{{{check}}},(Err(x),Err(e))=>assert!(x==e),_=>assert!(false)}}}}}}}}
'''
# Pin the exact deployed magic rather than using a fixture.
import re
magic=re.search(r'POOL_V1_PAIR_VERIFIED_AFTERSTATE_MAGIC[^=]*=\s*\*b"([^"]+)"',f).group(1).encode();body=body.replace('bytes[0]!=65||bytes[1]!=83||bytes[2]!=86||bytes[3]!=49','||'.join(f'bytes[{i}]!={v}' for i,v in enumerate(magic)))
h=f+'\n#[cfg(kani)]\nmod NEX_afterdecode;\n';patch=''.join(difflib.unified_diff(f.splitlines(True),h.splitlines(True),fromfile='a/'+p,tofile='b/'+p))+'--- /dev/null\n+++ b/crates/aspis-statement/src/pool_v1/NEX_afterdecode.rs\n@@ -0,0 +1,'+str(len(body.splitlines()))+' @@\n'+''.join('+'+l+'\n' for l in body.splitlines());(E/'NEX_native_contracts.patch').write_text(patch)
(E/'NEX_AFTERDECODE_CURRENT.json').write_text(json.dumps(dict(mode=mode,slot=slot,frozen_body=original,native=native,source=body,domain='all live688-byte slices; arbitrary complete digest values, earliest failure index 0..21, every validation Result/error, arbitrary indices',classification='ruling y exact frozen unrolled calls; no native loop, no multiplication; exact 8/32 actual bodies; full read/result/error/ordered local call log'),indent=1))
