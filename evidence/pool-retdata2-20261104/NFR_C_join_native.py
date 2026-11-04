"""One accepted native read/Box/getter/settlement continuation, no ghost geometry."""
from pathlib import Path
import json,subprocess,difflib,re,sys
E=Path(__file__).resolve().parent;O=E.parent/'pool-retdata-20261104';REV='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
mode=sys.argv[1];assert mode in ['join','join-byte','join-decoder','join-saved','join-context','join-validator','join-lane','join-encoder','join-error']
original=json.loads((O/'NFO_K007-shape.json').read_text())['source']
# Generate the same suffix, then embed it into the NFO read-cut harness.
subprocess.run([sys.executable,str(E/'NFR_C_native.py'),'suffix'],check=True)
suffix=json.loads((E/'NFR_C_CURRENT.json').read_text())['source']
suffix=suffix[suffix.index('struct Frame{calls:u8,expected:'):suffix.index('#[kani::proof]')]
suffix=re.sub(r'\bFrame\b','SettlementFrame',suffix)
pos=original.index('#[kani::proof]')
source=original[:pos]+suffix+original[pos:]
source=source.replace('let returned_program=Pubkey::new_from_array(kani::any());','let returned_program=selected;')
source=source.replace('let present:bool=kani::any();let cpi_ok:bool=kani::any();let decode_ok:bool=kani::any();','let present:bool=true;let cpi_ok:bool=true;let decode_ok:bool=true;')
old='else {let a=actual.unwrap();assert!(runtime.calls==3&&frame.calls==1&&observe(a.value(),family,row,word,index)==observe(&reply,family,row,word,index));assert!(a.exact_bytes().len()==792&&a.exact_bytes()[j]==byte&&core::ptr::eq(a.exact_bytes().as_ptr(),ptr));}'
new=r'''else {
 let a=actual.unwrap();
 assert!(runtime.calls==3&&frame.calls==1&&observe(a.value(),family,row,word,index)==observe(&reply,family,row,word,index));
 assert!(a.exact_bytes().len()==792&&a.exact_bytes()[j]==byte&&core::ptr::eq(a.exact_bytes().as_ptr(),ptr));
 let field=observe(&reply,family,row,word,index);
 let expected=a.value() as *const PoolV1PairForestTerminalResultV1;
 let validation_error:u64=kani::any();kani::assume(validation_error!=0);let next_error:u64=kani::any();kani::assume(next_error!=0);
 let valid:bool=kani::any();let next:bool=kani::any();let encoded:bool=kani::any();
 let encoded_reply:[u8;792]=kani::any();let expected_byte=encoded_reply[j];
 let mut settlement=SettlementFrame{calls:0,expected,family,row,word,index,field,valid,next,encoded,validation_error,next_error,reply:encoded_reply};
 let answer=continuation(&a,&mut settlement);
 if !valid{assert!(settlement.calls==1&&matches!(answer,Err(e) if e==ProgramError::from(validation_error)));}
 else if !next{assert!(settlement.calls==2&&matches!(answer,Err(e) if e==ProgramError::from(next_error)));}
 else if !encoded{assert!(settlement.calls==3&&matches!(answer,Err(e) if e==PoolV1ProgramError::InvalidVerifierReturnData.into()));}
 else{let out=answer.unwrap();assert!(settlement.calls==3&&out.len()==792&&out[j]==expected_byte);}
 assert!(runtime.calls==3&&frame.calls==1&&observe(a.value(),family,row,word,index)==field&&a.exact_bytes()[j]==byte);
}'''
assert old in source
source=source.replace(old,new)
if mode=='join-byte':source=source.replace('out[j]==expected_byte','out[j]==(expected_byte^1)')
if mode=='join-decoder':source=source.replace('value: Box::new(result)','value: Box::new({let mut changed=result;changed.output_lane^=1;changed})')
if mode=='join-saved':source=source.replace('a.exact_bytes()[j]==byte','a.exact_bytes()[j]==(byte^1)')
if mode=='join-context':source=source.replace('runtime.invoke(&instruction, &infos)?;','runtime.clear_return_data();')
if mode=='join-validator':source=source.replace('assert!(f.calls==0);argument(r,f);','assert!(f.calls==0);let changed=result();argument(&changed,f);')
if mode=='join-lane':source=source.replace('assert!(f.calls==1);argument(r,f);','assert!(f.calls==1);let changed=result();argument(&changed,f);')
if mode=='join-encoder':source=source.replace('assert!(f.calls==2);argument(r,f);','assert!(f.calls==2);let changed=result();argument(&changed,f);')
if mode=='join-error':source=source.replace('settlement.calls==3&&matches!(answer,Err(e) if e==PoolV1ProgramError::InvalidVerifierReturnData.into())','settlement.calls==3&&matches!(answer,Err(e) if e==ProgramError::InvalidArgument)')
patch=''
for p in ['programs/aspis-pool/src/pair_forest_dispatch.rs','programs/aspis-pool/src/lib.rs']:
 frozen=subprocess.check_output(['git','show',REV+':'+p],text=True)
 hook=frozen+'\n#[cfg(kani)]\n#[path="NFR_CJoin.rs"]\nmod NFR_CJoin;\n' if p.endswith('pair_forest_dispatch.rs') else '#![cfg_attr(kani, feature(allocator_api))]\n'+frozen+'\n#[cfg(kani)]\nextern crate alloc;\n#[cfg(kani)]\n#[path="../../../KMX_stubs.rs"]\npub mod NFO_KMX;\n'
 patch+=''.join(difflib.unified_diff(frozen.splitlines(True),hook.splitlines(True),fromfile='a/'+p,tofile='b/'+p))
p='programs/aspis-pool/src/NFR_CJoin.rs';patch+='--- /dev/null\n+++ b/'+p+'\n@@ -0,0 +1,'+str(len(source.splitlines()))+' @@\n'+''.join('+'+l+'\n' for l in source.splitlines())
(E/'NFR_C_native.patch').write_text(patch)
(E/'NFR_C_CURRENT.json').write_text(json.dumps(dict(mode=mode,source=source,classification='ONE native accepted read-cut -> SAME returned Authenticated object -> actual getter -> three exact settlement-value oracle arguments -> reencode Box; full child Results/local frames, production capacity=len792; outer process admission/prefix remains separate',harness='pair_forest_dispatch::NFR_CJoin::association',accepted_domain='CPI succeeded, reply present/from selected program,792bytes,decoder succeeded: all necessary consequences of a successful authenticated dispatcher return, not a stronger precondition'),indent=1)+'\n')
