"""Ruling-(t) controls for the exact return carriers used by direct leaf frames."""
from pathlib import Path
import difflib,hashlib,json,subprocess,sys
from NEE_patch_inputs import oracle_parts
E=Path(__file__).resolve().parent
shape=sys.argv[1];assert shape in {'fixed4','common','tuple','borrowed'}
base,hook=oracle_parts()
utilities=base[base.index('fn NEE_digest()'):]
# Only the typed record constructors are needed by the borrowed-carrier control.
utilities=utilities[:utilities.index('fn NEE_statement()')] if 'fn NEE_statement()' in utilities else utilities
imports='''#![allow(non_snake_case,unused_variables)]
use super::*;
use crate::pool_v1::{PoolV1PairForestTerminalCommonV1,PoolV1PairLatePublicStatementV1,PoolV1PairVerifiedAfterstateV1};
'''
extra=''
if shape=='fixed4':
 typ='[u8;4]';factory='kani::any::<A>()';same='*x==*y';owned=True
elif shape=='common':
 typ='CommonPublicV1';factory='make()';same='x.pool==y.pool&&x.deployment_domain==y.deployment_domain&&x.anchor_sequence==y.anchor_sequence&&x.anchor_root==y.anchor_root&&x.nullifier==y.nullifier&&x.asset_id==y.asset_id';owned=True
 extra='''fn make()->A {CommonPublicV1{pool:kani::any(),deployment_domain:kani::any(),anchor_sequence:kani::any(),anchor_root:NEE_digest(),nullifier:NEE_digest(),asset_id:M31(kani::any())}}
impl kani::Arbitrary for CommonPublicV1 {fn any()->Self {make()}}
'''
elif shape=='tuple':
 typ='([u8;32],[u8;32],u64,Digest,Digest,M31)';factory='make()';same='*x==*y';owned=True
 extra='fn make()->A {(kani::any(),kani::any(),kani::any(),NEE_digest(),NEE_digest(),M31(kani::any()))}\n'
else:
 typ='PoolV1PairForestTerminalCommonV1';factory='NEE_common()';same='core::ptr::eq(x,y)';owned=False
module=imports+utilities+'\ntype A='+typ+';\n'+extra+'fn same(x:&A,y:&A)->bool{'+same+'}\n'
if owned:
 module+='''#[kani::modifies()]
#[kani::ensures(|_| true)]
fn weak(x:A)->A {x}
#[kani::modifies(&mut buf[0])]
#[kani::ensures(|_| true)]
fn bad_frame(buf:&mut[u8;2],x:A)->A {buf[1]=buf[1].wrapping_add(1);x}
'''
 native='let x=FACTORY;let r=weak(x);assert!(same(&r,&x),"NEE weak real-body identity");'
 unimplied='let x=FACTORY;let r=weak(x);assert!(same(&r,&x),"NEE weak replacement cannot imply identity");'
 frame='let mut b:[u8;2]=kani::any();let x=FACTORY;let _=bad_frame(&mut b,x);'
else:
 module+='''#[kani::modifies()]
#[kani::ensures(|_| true)]
fn weak(x:&A)->&A {x}
#[kani::modifies(&mut buf[0])]
#[kani::ensures(|_| true)]
fn bad_frame<'a>(buf:&mut[u8;2],x:&'a A)->&'a A {buf[1]=buf[1].wrapping_add(1);x}
'''
 native='let x=FACTORY;let r=weak(&x);assert!(same(r,&x),"NEE weak real-body reference identity");'
 unimplied='let x=FACTORY;let r=weak(&x);assert!(same(r,&x),"NEE weak reference replacement cannot imply identity");'
 frame='let mut b:[u8;2]=kani::any();let x=FACTORY;let _=bad_frame(&mut b,&x);'
if owned:
 module+='#[kani::modifies()]\n#[kani::ensures(|r| !same(r,&x))]\nfn inverted(x:A)->A {x}\n'
 inverse='let x=FACTORY;let _=inverted(x);'
else:
 module+='#[kani::modifies()]\n#[kani::ensures(|r| !same(*r,x))]\nfn inverted(x:&A)->&A {x}\n'
 inverse='let x=FACTORY;let _=inverted(&x);'
kmx='''#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
#[kani::stub(alloc::vec::Vec::<u8>::extend_from_slice,crate::KMX_stubs::KMX_extend_from_slice)]
#[kani::stub(<[u8]>::to_vec,crate::KMX_stubs::KMX_to_vec)]
#[kani::stub(alloc::alloc::realloc,crate::KMX_stubs::KMX_realloc)]
'''
module+='#[kani::proof_for_contract(inverted)]\n'+kmx+'fn inverted_contract(){'+inverse.replace('FACTORY',factory)+'}\n'
module+='#[kani::proof_for_contract(weak)]\n'+kmx+'fn native_weak(){'+native.replace('FACTORY',factory)+'}\n'
module+='#[kani::proof]\n#[kani::stub_verified(weak)]\n'+kmx+'fn unimplied(){'+unimplied.replace('FACTORY',factory)+'}\n'
module+='#[kani::proof_for_contract(bad_frame)]\n'+kmx+'fn frame_violation(){'+frame.replace('FACTORY',factory)+'}\n'
path='crates/aspis-statement/src/pool_v1/payment_relation.rs'
get=lambda p:subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+p],text=True)
frozen=get(path);changed=frozen+'\n#[cfg(kani)]\n#[path="NEE_shape.rs"]\nmod NEE_shape;\n'
patch=''.join(difflib.unified_diff(frozen.splitlines(True),changed.splitlines(True),fromfile='a/'+path,tofile='b/'+path))
if shape=='tuple':
 p='crates/aspis-core/src/field.rs';s=get(p)
 # Full raw-word Arbitrary for the existing POD M31 type; never a carrier swap,
 # no references/allocator/function pointers, and no protocol implementation change.
 t=s+'\n#[cfg(kani)]\nmod NEE_shape_arbitrary {use super::M31; impl kani::Arbitrary for M31 {fn any()->Self {M31(kani::any())}}}\n'
 patch+=''.join(difflib.unified_diff(s.splitlines(True),t.splitlines(True),fromfile='a/'+p,tofile='b/'+p))
name='crates/aspis-statement/src/pool_v1/NEE_shape.rs'
patch+='--- /dev/null\n+++ b/'+name+'\n@@ -0,0 +1,'+str(len(module.splitlines()))+' @@\n'+''.join('+'+l+'\n' for l in module.splitlines())
(E/'NEE_native_contracts.patch').write_text(patch)
(E/'NEE_oracle.patch').write_text('--- /dev/null\n+++ b/crates/aspis-statement/src/pool_v1/NEE_oracle.rs\n@@ -0,0 +1,'+str(len(base.splitlines()))+' @@\n'+''.join('+'+l+'\n' for l in base.splitlines())+hook)
(E/('NEE_SHAPE_'+shape+'.json')).write_text(json.dumps(dict(shape=shape,return_type=typ if owned else '&'+typ,weak_native_includes_real_body_assertion=True,stub_verified_control='unimplied',modifies_violation='write byte1 with only byte0 declared',no_return_carrier_replacement=True,full_pod_arbitrary_impl=shape in ['common','tuple'],borrowed_arbitrary_workaround=False,patch_sha256=hashlib.sha256(patch.encode()).hexdigest()),indent=1)+'\n')
print('pool_v1::payment_relation::NEE_shape::')
