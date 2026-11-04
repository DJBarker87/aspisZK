"""Read-set projection of the exact reconstruction prefix, no opaque root oracle."""
import sys,json,subprocess,re
from NEU_native_patch import E,frozen,program
mode=sys.argv[1];assert mode in ['positive','negative']
subprocess.run([sys.executable,str(E/'NEU_prepare_window.py'),'1','positive'],check=True)
s=frozen('programs/r1-cost-probe/src/r1_pool_adapter.rs');a=s.index('fn reconstruct_asq8_statement(');z=s.index('    let common =',a);original=s[a:z]
replacements={'fn reconstruct_asq8_statement(':'fn prefix(', 'PoolV1PairForestTerminalRequestV1':'RequestView','AuthenticatedAsq8Accounts':'AuthView','aspis_statement::pool_v1::PoolV1PairVerifiedAfterstateV1':'CandidateView','Result<Box<PoolV1PairForestTerminalStatementV1>, ProgramError>':'ProgramResult','PoolV1PairForestTerminalPaymentV1':'PaymentView'}
native=original
for x,y in replacements.items():native=native.replace(x,y)
native+='    Ok(())\n}\n'
body='''use super::*;
#[derive(Clone,Copy)] struct PublicView{asset_id:M31}
#[derive(Clone,Copy)] enum PaymentView{PrivateTransfer(PublicView),Withdrawal(PublicView)}
struct RequestView{public:PaymentView}
struct IdentityView{asset_id:M31}
struct MasterView{identity:IdentityView}
struct LiveView{next_pair_index:u64}
struct AuthView{master:MasterView,live_snapshot:LiveView}
struct CandidateView{next_pair_index:u64}
'''+native+'''
#[kani::proof]
fn reconstruction_slice(){let live:u64=kani::any();let next:u64=kani::any();let asset:u32=kani::any();let requested:u32=kani::any();let p=PublicView{asset_id:M31(requested)};let request=RequestView{public:if kani::any(){PaymentView::PrivateTransfer(p)}else{PaymentView::Withdrawal(p)}};let a=AuthView{master:MasterView{identity:IdentityView{asset_id:M31(asset)}},live_snapshot:LiveView{next_pair_index:live}};let c=CandidateView{next_pair_index:next};let expected=if live==u64::MAX||live.wrapping_add(1)!=next{Err(ProgramError::InvalidAccountData)}else if asset!=requested@BAD@{Err(ProgramError::InvalidInstructionData)}else{Ok(())};assert!(prefix(&request,&a,&c)==expected);}
'''.replace('@BAD@','^1' if mode=='negative' else '')
program(body,'NEU_reconstruct')
(E/'NEU_GUARD_VIEW_CURRENT.json').write_text(json.dumps(dict(mode=mode,frozen_prefix=original,native=native,replacements=replacements,read_set=['authenticated.live_snapshot.next_pair_index','candidate_afterstate.next_pair_index','authenticated.master.identity.asset_id','request.public.variant','request.public.*.asset_id'],domain='all u64 live/next, all u32 assets, both payment variants; no scalar precondition',classification='exact prefix read-set projection; full input reconstruction/physical bridge is NOT claimed; unrelated fields need native noninterference association before root credit'),indent=1)+'\n')
