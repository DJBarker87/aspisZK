"""Exact one-call helper cut, with local encoder/allocation observation closures."""
from pathlib import Path
import json,sys,subprocess,difflib,hashlib
E=Path(__file__).resolve().parent;mode=sys.argv[1]
assert mode in ['byte','byte-negative','error','error-negative','place-negative','allocation-negative']
base=json.loads((E.parent/'pool-retdata2-20261104/NFR_K034-shape.json').read_text())['source'];s=base[:base.index('#[kani::proof]')]
source=json.loads((E.parent/'pool-retdata2-20261104/NFR_C_SOURCE_CUT.json').read_text())['encoder_helper']
body=source[source.index('    Ok(Box::new('):source.rindex('}')]
cut=body.replace('Box::new(','allocate(').replace('encode_pool_v1_pair_forest_terminal_result_v1(result)','encode(result)')
assert cut.replace('allocate(','Box::new(').replace('encode(result)','encode_pool_v1_pair_forest_terminal_result_v1(result)')==body
s+='''fn helper<E,A>(result:&PoolV1PairForestTerminalResultV1,encode:E,allocate:A)->Result<Box<[u8;792]>,ProgramError>
where E:FnOnce(&PoolV1PairForestTerminalResultV1)->Result<[u8;792],PoolV1PairForestTerminalFormatErrorV1>,A:FnOnce([u8;792])->Box<[u8;792]>{
'''+cut+'}\n'
s+='''#[kani::proof]
#[kani::unwind(793)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFO_KMX::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,crate::NFO_KMX::KMX_copy_from_slice)]
#[kani::stub(alloc::alloc::realloc,crate::NFO_KMX::KMX_realloc)]
fn association(){
 let original=result(); let other=result();let ptr=&original as *const PoolV1PairForestTerminalResultV1;
 let j:usize=kani::any();kani::assume(j<792);
 let child:Result<[u8;792],PoolV1PairForestTerminalFormatErrorV1>=if kani::any(){Ok(kani::any())}else{Err(any_error())};
 let expected=child.as_ref().ok().map(|bytes|bytes[j]);
 let mut encoded=0u8;let mut allocated=0u8;let mut allocation=core::ptr::null();let mut parked=None;
 let actual=helper(&original,|arg|{encoded+=1;assert!(core::ptr::eq(arg,ptr));child},|bytes|{
  allocated+=1;let boxed=Box::new(bytes);allocation=boxed.as_ptr();RETURN_BOX
 });
 assert!(encoded==1);
 match (expected,actual){
  (Some(byte),Ok(boxed))=>{assert!(allocated==1);assert!(boxed.as_ptr()==allocation);CHECK_BYTE},
  (None,Err(error))=>{assert!(allocated==0);CHECK_ERROR},
  _=>panic!("native helper changed Result variant")
 }
 let _:Option<Box<[u8;792]>>=parked;
}
'''
s=s.replace('RETURN_BOX','let second=Box::new(*boxed);parked=Some(boxed);second' if mode=='allocation-negative' else 'boxed')
s=s.replace('CHECK_BYTE','assert!(boxed[j]==(byte^1));' if mode=='byte-negative' else 'assert!(boxed[j]==byte);')
s=s.replace('CHECK_ERROR','assert!(error!=PoolV1ProgramError::InvalidVerifierReturnData.into());' if mode=='error-negative' else 'assert!(error==PoolV1ProgramError::InvalidVerifierReturnData.into());')
if mode=='place-negative':s=s.replace('helper(&original,','helper(&other,')
patch=''
for p in ['programs/aspis-pool/src/pair_forest.rs','programs/aspis-pool/src/lib.rs']:
 f=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+p],text=True)
 hook=f+'\n#[cfg(kani)]\n#[path="NFV_Helper.rs"]\nmod NFV_Helper;\n' if p.endswith('pair_forest.rs') else '#![cfg_attr(kani, feature(allocator_api))]\n'+f+'\n#[cfg(kani)]\nextern crate alloc;\n#[cfg(kani)]\n#[path="../../../KMX_stubs.rs"]\npub mod NFO_KMX;\n'
 patch+=''.join(difflib.unified_diff(f.splitlines(True),hook.splitlines(True),fromfile='a/'+p,tofile='b/'+p))
p='programs/aspis-pool/src/NFV_Helper.rs';patch+='--- /dev/null\n+++ b/'+p+'\n@@ -0,0 +1,'+str(len(s.splitlines()))+' @@\n'+''.join('+'+l+'\n' for l in s.splitlines())
(E/'NFV_native.patch').write_text(patch);(E/'NFV_CURRENT.json').write_text(json.dumps(dict(mode='helper-log-'+mode,source=s,classification='source-exact helper native cut, child/full-Result oracle and real Box local observation; erasure identity checked; requires semantic-transport review before production credit',body_sha256=hashlib.sha256(body.encode()).hexdigest(),erasure_exact=True,excluded='no real encoder loop, no repr(C) trailing frame, no custom allocator implementation'),indent=1)+'\n')
