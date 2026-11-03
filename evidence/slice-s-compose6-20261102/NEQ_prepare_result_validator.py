"""Frozen validate_result with local full-Result child oracles."""
from pathlib import Path
import subprocess,sys,json,difflib,hashlib
E=Path(__file__).resolve().parent;mode=sys.argv[1];assert mode in ['positive','wrong_lane','wrong_after','wrong_reply']
subprocess.run([sys.executable,str(E/'NEQ_prepare_root_prefix.py'),'positive'],check=True)
p='crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs';f=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+p],text=True)
seed=(E/'NEQ_native_contracts.patch').read_text();_,rest=seed.split('--- /dev/null\n+++ b/crates/aspis-statement/src/pool_v1/NEQ_root_prefix.rs\n',1);raw=''.join(l[1:]+'\n' for l in rest.splitlines()[1:] if l.startswith('+'));raw=raw[:raw.index('struct Frame')]
a=f.index('fn validate_result(');z=f.index('\n}',a)+2;original=f[a:z]
changedbody=original.replace('fn validate_result(', 'fn native(').replace('    result: &PoolV1PairForestTerminalResultV1,','    result: &PoolV1PairForestTerminalResultV1,\n    frame: &mut Frame,').replace('pool_v1_pair_forest_output_lane_v1(&result.nullifier)','lane('+('&result.verified_afterstate.next_root' if mode=='wrong_lane' else '&result.nullifier')+',frame)').replace('encode_pool_v1_pair_verified_afterstate_v1(&result.verified_afterstate)','after('+('&frame.other' if mode=='wrong_after' else '&result.verified_afterstate')+',frame)')
body=raw+'''
struct Frame<'a>{expected:&'a PoolV1PairForestTerminalResultV1,other:PoolV1PairVerifiedAfterstateV1,lane:Result<u8,PoolV1PairForestAccountErrorV1>,after:Result<[u8;688],PoolV1PairVerifierTransportErrorV1>,calls:u8}
fn lane(d:&Digest,f:&mut Frame)->Result<u8,PoolV1PairForestAccountErrorV1>{assert!(f.calls==0&&core::ptr::eq(d,&f.expected.nullifier));f.calls=1;LANEREPLY}
fn after(a:&PoolV1PairVerifiedAfterstateV1,f:&mut Frame)->Result<[u8;688],PoolV1PairVerifierTransportErrorV1>{assert!(f.calls==1&&core::ptr::eq(a,&f.expected.verified_afterstate));f.calls=2;f.after}
'''.replace('LANEREPLY','match f.lane{Ok(x)=>Ok(x^1),Err(e)=>Err(e)}' if mode=='wrong_reply' else 'f.lane')+changedbody+'''
fn reference(r:&PoolV1PairForestTerminalResultV1,f:&Frame)->Result<(),PoolV1PairForestTerminalFormatErrorV1>{if r.master_account==[0u8;32]||r.selected_lane_account==[0u8;32]{return Err(PoolV1PairForestTerminalFormatErrorV1::NonZeroBinding)}let lane=f.lane.map_err(PoolV1PairForestTerminalFormatErrorV1::Account)?;if r.output_lane!=lane{return Err(PoolV1PairForestTerminalFormatErrorV1::OutputLaneMismatch)}f.after.map_err(PoolV1PairForestTerminalFormatErrorV1::Afterstate)?;Ok(())}
fn result()->PoolV1PairForestTerminalResultV1{PoolV1PairForestTerminalResultV1{transition_kind:if kani::any(){PoolV1TransitionKind::PrivateTransfer}else{PoolV1TransitionKind::Withdrawal},master_account:kani::any(),selected_lane_account:kani::any(),output_lane:kani::any(),nullifier:NEE_digest(),verified_afterstate:NEE_common().lane_transition.candidate_afterstate}}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
fn result_validator(){let r=result();let mut f=Frame{expected:&r,other:NEE_common().lane_transition.candidate_afterstate,lane:if kani::any(){Ok(kani::any())}else{Err(NEE_any_PoolV1PairForestAccountErrorV1())},after:if kani::any(){Ok(kani::any())}else{Err(NEE_any_PoolV1PairVerifierTransportErrorV1())},calls:0};let expected=reference(&r,&f);let actual=native(&r,&mut f);assert!(actual==expected,"full result validator Result");let reached=r.master_account!=[0u8;32]&&r.selected_lane_account!=[0u8;32];let after_reached=reached&&match f.lane{Ok(l)=>r.output_lane==l,Err(_)=>false};assert!(f.calls==if after_reached{2}else if reached{1}else{0},"exact reached child prefix and order");}
'''
# Wrong-place control must borrow a disjoint local place without aliasing the log.
body=body.replace('after(&frame.other,frame)','after(&frame.other.clone(),frame)') if mode=='wrong_after' else body
changed=f+'\n#[cfg(kani)]\n#[path="NEQ_result_validator.rs"]\nmod NEQ_result_validator;\n';patch=''.join(difflib.unified_diff(f.splitlines(True),changed.splitlines(True),fromfile='a/'+p,tofile='b/'+p))+'--- /dev/null\n+++ b/crates/aspis-statement/src/pool_v1/NEQ_result_validator.rs\n@@ -0,0 +1,'+str(len(body.splitlines()))+' @@\n'+''.join('+'+l+'\n' for l in body.splitlines());(E/'NEQ_native_contracts.patch').write_text(patch)
(E/'NEQ_RESULT_VALIDATOR_CURRENT.json').write_text(json.dumps(dict(mode=mode,frozen_body=original,frozen_body_sha256=hashlib.sha256(original.encode()).hexdigest(),instrumented_body=changedbody,full_lane_and_after_Results=True,all_typed_inputs=True,modifies='local call log only; immutable input',classification='ruling y exact frozen caller with local oracle records; no inner acceptance assumption'),indent=1)+'\n')
