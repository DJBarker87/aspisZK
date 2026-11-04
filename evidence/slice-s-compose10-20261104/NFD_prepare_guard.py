"""Source-shaped guard cuts after K069 timeout; no aggregate guard replay."""
from NFD_native_patch import E,frozen,program,helpers
import sys,subprocess,json
shape,mode=sys.argv[1:];assert shape in ['add','asset','requested','joined'] and mode in ['positive','negative']
subprocess.run([sys.executable,str(E/'NFD_prepare_window.py'),'1','positive'],check=True)
p='programs/r1-cost-probe/src/r1_pool_adapter.rs';f=frozen(p);a=f.index('fn reconstruct_asq8_statement(');original=f[a:f.index('\n}',a)+2]
if shape=='add':
 expr='authenticated.live_snapshot.next_pair_index.checked_add(1)\n        != Some(candidate_afterstate.next_pair_index)';assert expr in original
 code='let live:u64=kani::any();let next:u64=kani::any();let native=live.checked_add(1)!=Some(next);let expected=live==u64::MAX||live.wrapping_add(1)!=next;assert!(native=='+('!expected' if mode=='negative' else 'expected')+');'
elif shape=='asset':
 expr='authenticated.master.identity.asset_id != requested_asset_id';assert expr in original
 code='let a:u32=kani::any();let b:u32=kani::any();let native=M31(a)!=M31(b);assert!(native=='+('!' if mode=='negative' else '')+'(a!=b));'
elif shape=='requested':
 expr=original[original.index('    let requested_asset_id ='):original.index('    if authenticated.master')]
 code='let s=NEE_statement();let request=PoolV1PairForestTerminalRequestV1{verifier_profile:kani::any(),verifier_release:kani::any(),pool_program:kani::any(),public:match s{PoolV1PairForestTerminalStatementV1::PrivateTransfer{public,..}=>PoolV1PairForestTerminalPaymentV1::PrivateTransfer(public),PoolV1PairForestTerminalStatementV1::Withdrawal{public,..}=>PoolV1PairForestTerminalPaymentV1::Withdrawal(public)}};'+expr+'let expected=match s{PoolV1PairForestTerminalStatementV1::PrivateTransfer{public,..}=>public.asset_id.0,PoolV1PairForestTerminalStatementV1::Withdrawal{public,..}=>public.asset_id.0};assert!(requested_asset_id.0==expected'+('^1' if mode=='negative' else '')+');'
else:
 expr=original[:original.index('    let common =')]
 code='let add_reject:bool=kani::any();let asset_reject:bool=kani::any();let native:ProgramResult=if add_reject{Err(ProgramError::InvalidAccountData)}else if asset_reject{Err(ProgramError::InvalidInstructionData)}else{Ok(())};match native{Ok(())=>assert!(!add_reject&&!asset_reject),Err(ProgramError::InvalidAccountData)=>assert!('+('add_reject&&!asset_reject' if mode=='negative' else 'add_reject')+'),Err(ProgramError::InvalidInstructionData)=>assert!(!add_reject&&asset_reject),Err(_)=>assert!(false)}'
attrs='''#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFD_KMX::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,crate::NFD_KMX::KMX_copy_from_slice)]
'''
body=helpers()+attrs+'fn guard_cut(){'+code+'}\n';program(body,'NFD_guard')
(E/'NFD_GUARD_CURRENT.json').write_text(json.dumps(dict(shape=shape,mode=mode,source=body,frozen_body=original,frozen_expression=expr,domain='every raw scalar and every valid typed public record; Boolean guard results arbitrary at the final control join',classification='one exact native scalar/field/control source cut; source argument projection and model control theorem are required for root association'),indent=1)+'\n')
