"""NFR settlement suffix/capacity cuts. Never writes shipped repository sources."""
from pathlib import Path
import subprocess,difflib,json,sys,hashlib
E=Path(__file__).resolve().parent
O=E.parent/'pool-retdata-20261104'
REV='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
mode=sys.argv[1]
original=json.loads((O/'NFO_K007-shape.json').read_text())['source']
helpers=original[original.index('fn digest()'):original.index('struct Runtime {')]
source='use super::*;\nuse aspis_statement::pool_v1::*;\nuse aspis_core::field::M31;\n'+helpers
params='let family:u8=kani::any();kani::assume(family<8);let row:usize=kani::any();kani::assume(row<20);let word:usize=kani::any();kani::assume(word<8);let index:usize=kani::any();kani::assume(index<32);'
attrs='''#[kani::proof]
#[kani::unwind(34)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFO_KMX::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,crate::NFO_KMX::KMX_copy_from_slice)]
'''
if mode.startswith('carrier'):
 source+=attrs+'fn association(){\n'+params+r'''
 let raw:[u8;792]=kani::any();let j:usize=kani::any();kani::assume(j<792);
 let boxed:Box<[u8]>=Box::new(raw);let data=boxed.into_vec();
 assert!(data.capacity()==792&&data.len()==792);
 let ptr=data.as_ptr();let expected=data[j];
 let original=result();let field=observe(&original,family,row,word,index);
 let authenticated=AuthenticatedPairForestResultV1{value:Box::new(original),exact_bytes:data.into_boxed_slice()};
 assert!(authenticated.exact_bytes().len()==792&&authenticated.exact_bytes()[j]==expected);
 assert!(core::ptr::eq(authenticated.exact_bytes().as_ptr(),ptr));
 assert!(observe(authenticated.value(),family,row,word,index)==field);
}
'''
 if mode=='carrier-byte':source=source.replace('exact_bytes()[j]==expected','exact_bytes()[j]==(expected^1)')
 if mode=='carrier-pointer':source=source.replace('assert!(core::ptr::eq(authenticated.exact_bytes().as_ptr(),ptr))','assert!(!core::ptr::eq(authenticated.exact_bytes().as_ptr(),ptr))')
 if mode=='carrier-value':source=source.replace('==field);','==(field^1));')
 classification='ACTUAL getter and Vec::into_boxed_slice at caller-established capacity=len=792; arbitrary byte and all eight result projections; no arbitrary-capacity pointer claim'
elif mode.startswith('getter'):
 source+=attrs+'fn association(){\n'+params+r'''
 let original=result();let expected=observe(&original,family,row,word,index);
 let auth=AuthenticatedPairForestResultV1{value:Box::new(original),exact_bytes:Box::new([0u8;792])};
 let ptr=&*auth.value as *const PoolV1PairForestTerminalResultV1;
 let consumed=auth.value();
 assert!(core::ptr::eq(consumed,ptr));
 assert!(observe(consumed,family,row,word,index)==expected);
}
'''
 if mode.startswith('getter-field-'):
  field=mode.removeprefix('getter-field-');mutations={
   'kind':'changed.transition_kind=match changed.transition_kind{PoolV1TransitionKind::PrivateTransfer=>PoolV1TransitionKind::Withdrawal,_=>PoolV1TransitionKind::PrivateTransfer};',
   'master':'changed.master_account[index]^=1;', 'selected':'changed.selected_lane_account[index]^=1;', 'lane':'changed.output_lane^=1;',
   'nullifier':'changed.nullifier[word].0^=1;', 'index':'changed.verified_afterstate.next_pair_index^=1;',
   'root':'changed.verified_afterstate.next_root[word].0^=1;', 'frontier':'changed.verified_afterstate.next_frontier[row][word].0^=1;'}
  source=source.replace('value:Box::new(original)','value:Box::new({let mut changed=original;'+mutations[field]+'changed})')
 classification='ACTUAL AuthenticatedPairForestResultV1::value getter, allocation identity and arbitrary result projection; no settlement-prefix claim'
elif mode.startswith('suffix'):
 source+=r'''
struct Frame{calls:u8,expected:*const PoolV1PairForestTerminalResultV1,family:u8,row:usize,word:usize,index:usize,field:u64,valid:bool,next:bool,encoded:bool,validation_error:u64,next_error:u64,reply:[u8;792]}
fn argument(r:&PoolV1PairForestTerminalResultV1,f:&Frame){
 assert!(core::ptr::eq(r,f.expected));
 assert!(observe(r,f.family,f.row,f.word,f.index)==f.field);
}
fn validate(r:&PoolV1PairForestTerminalResultV1,f:&mut Frame)->ProgramResult{
 assert!(f.calls==0);argument(r,f);f.calls=1;
 if f.valid{Ok(())}else{Err(ProgramError::from(f.validation_error))}
}
fn lane(r:&PoolV1PairForestTerminalResultV1,f:&mut Frame)->Result<Box<[u8;aspis_statement::pool_v1::POOL_V1_PAIR_FOREST_LANE_ACCOUNT_BYTES]>,ProgramError>{
 assert!(f.calls==1);argument(r,f);f.calls=2;
 if f.next{Ok(Box::new(kani::any()))}else{Err(ProgramError::from(f.next_error))}
}
fn encode(r:&PoolV1PairForestTerminalResultV1,f:&mut Frame)->Result<[u8;792],PoolV1PairForestTerminalFormatErrorV1>{
 assert!(f.calls==2);argument(r,f);f.calls=3;
 if f.encoded{Ok(f.reply)}else{Err(any_error())}
}
fn terminal_bytes(r:&PoolV1PairForestTerminalResultV1,f:&mut Frame)->Result<Box<[u8;792]>,ProgramError>{
 Ok(Box::new(encode(r,f).map_err(|_| PoolV1ProgramError::InvalidVerifierReturnData)?))
}
fn continuation(authenticated:&AuthenticatedPairForestResultV1,f:&mut Frame)->Result<Box<[u8;792]>,ProgramError>{
 let result=authenticated.value();
 validate(result,f)?;
 let _next_lane_image=lane(result,f)?;
 let result_bytes=terminal_bytes(result,f)?;
 Ok(result_bytes)
}
'''
 source+=attrs+'fn association(){\n'+params+r'''
 let original=result();let field=observe(&original,family,row,word,index);
 let raw:[u8;792]=kani::any();let j:usize=kani::any();kani::assume(j<792);
 let bytes:Box<[u8]>=Box::new(raw);let data=bytes.into_vec();assert!(data.capacity()==792&&data.len()==792);
 let auth=AuthenticatedPairForestResultV1{value:Box::new(original),exact_bytes:data.into_boxed_slice()};
 let ptr=&*auth.value as *const PoolV1PairForestTerminalResultV1;
 let reply:[u8;792]=kani::any();let expected=reply[j];
 let validation_error:u64=kani::any();kani::assume(validation_error!=0);let next_error:u64=kani::any();kani::assume(next_error!=0);
 let valid:bool=kani::any();let next:bool=kani::any();let encoded:bool=kani::any();
 let mut f=Frame{calls:0,expected:ptr,family,row,word,index,field,valid,next,encoded,validation_error,next_error,reply};
 let answer=continuation(&auth,&mut f);
 if !valid{assert!(f.calls==1&&matches!(answer,Err(e) if e==ProgramError::from(validation_error)));}
 else if !next{assert!(f.calls==2&&matches!(answer,Err(e) if e==ProgramError::from(next_error)));}
 else if !encoded{assert!(f.calls==3&&matches!(answer,Err(e) if e==PoolV1ProgramError::InvalidVerifierReturnData.into()));}
 else{let out=answer.unwrap();assert!(f.calls==3&&out.len()==792&&out[j]==expected);}
 assert!(observe(auth.value(),family,row,word,index)==field&&auth.exact_bytes()[j]==raw[j]);
}
'''
 if mode=='suffix-byte':source=source.replace('out[j]==expected','out[j]==(expected^1)')
 if mode=='suffix-error':source=source.replace('e==PoolV1ProgramError::InvalidVerifierReturnData.into()','e==ProgramError::InvalidArgument')
 if mode=='suffix-order':source=source.replace('assert!(f.calls==2);argument(r,f);f.calls=3;','assert!(f.calls==1);argument(r,f);f.calls=3;')
 if mode=='suffix-validator':source=source.replace('assert!(f.calls==0);argument(r,f);','assert!(f.calls==0);let changed=result();argument(&changed,f);')
 if mode=='suffix-lane':source=source.replace('assert!(f.calls==1);argument(r,f);','assert!(f.calls==1);let changed=result();argument(&changed,f);')
 if mode=='suffix-encoder':source=source.replace('assert!(f.calls==2);argument(r,f);','assert!(f.calls==2);let changed=result();argument(&changed,f);')
 if mode=='suffix-frame':source=source.replace('auth.exact_bytes()[j]==raw[j]','auth.exact_bytes()[j]==(raw[j]^1)')
 classification='SOURCE-EXACT settlement value/helper continuation with local full encoder/validation/lane Result oracles; validates same decoded allocation at every child and immutable frame; process admission/prefix remains separate'
else:raise AssertionError(mode)
patch=''
for p in ['programs/aspis-pool/src/pair_forest_dispatch.rs','programs/aspis-pool/src/lib.rs']:
 frozen=subprocess.check_output(['git','show',REV+':'+p],text=True)
 hook=frozen+'\n#[cfg(kani)]\n#[path="NFR_C.rs"]\nmod NFR_C;\n' if p.endswith('pair_forest_dispatch.rs') else '#![cfg_attr(kani, feature(allocator_api))]\n'+frozen+'\n#[cfg(kani)]\nextern crate alloc;\n#[cfg(kani)]\n#[path="../../../KMX_stubs.rs"]\npub mod NFO_KMX;\n'
 patch+=''.join(difflib.unified_diff(frozen.splitlines(True),hook.splitlines(True),fromfile='a/'+p,tofile='b/'+p))
p='programs/aspis-pool/src/NFR_C.rs';patch+='--- /dev/null\n+++ b/'+p+'\n@@ -0,0 +1,'+str(len(source.splitlines()))+' @@\n'+''.join('+'+l+'\n' for l in source.splitlines())
(E/'NFR_C_native.patch').write_text(patch)
(E/'NFR_C_CURRENT.json').write_text(json.dumps(dict(mode=mode,source=source,classification=classification,harness='pair_forest_dispatch::NFR_C::association'),indent=1)+'\n')
