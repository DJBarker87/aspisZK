"""Exact frozen result initializer, observed one raw coordinate at a time."""
from NFD_native_patch import E,frozen,program,helpers
import subprocess,sys,json
slot=int(sys.argv[1]);mode=sys.argv[2]
assert 0<=slot<8 and mode in ['positive','negative']
subprocess.run([sys.executable,str(E/'NFD_prepare_window.py'),'1','positive'],check=True)
f=frozen('programs/r1-cost-probe/src/r1_pool_adapter.rs');a=f.index('fn emit_result(')
original=f[a:f.index('\n}',a)+2]
prefix=original[:original.index('    validate_pool_v1_pair_forest_terminal_result_against_statement_v1')]
native=prefix.replace('fn emit_result(','fn native(').replace('-> ProgramResult','-> PoolV1PairForestTerminalResultV1')+'    result\n}\n'
fields=['match out.transition_kind{PoolV1TransitionKind::PrivateTransfer=>1,PoolV1TransitionKind::Withdrawal=>2}', 'out.master_account[j] as u64','out.selected_lane_account[j] as u64','out.output_lane as u64','out.nullifier[i].0 as u64','out.verified_afterstate.next_pair_index','out.verified_afterstate.next_root[i].0 as u64','out.verified_afterstate.next_frontier[k][i].0 as u64']
values=['kind','common.master_account[j] as u64','common.selected_lane_account[j] as u64','common.output_lane as u64','nullifier[i].0 as u64','common.lane_transition.candidate_afterstate.next_pair_index','common.lane_transition.candidate_afterstate.next_root[i].0 as u64','common.lane_transition.candidate_afterstate.next_frontier[k][i].0 as u64']
body=helpers()+native+'''
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFD_KMX::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,crate::NFD_KMX::KMX_copy_from_slice)]
fn emit_prefix(){let s=NEE_statement();let i:usize=kani::any();let j:usize=kani::any();let k:usize=kani::any();kani::assume(i<8&&j<32&&k<20);let (kind,common,nullifier)=match &s{PoolV1PairForestTerminalStatementV1::PrivateTransfer{common,public}=>(1u64,common,&public.nullifier),PoolV1PairForestTerminalStatementV1::Withdrawal{common,public}=>(2u64,common,&public.nullifier)};let out=native(&s);assert!((@LEFT@)==(@RIGHT@)@BAD@);}
'''
body=body.replace('@LEFT@',fields[slot]).replace('@RIGHT@',values[slot]).replace('@BAD@','^1' if mode=='negative' else '')
program(body,'NFD_emit_prefix')
(E/'NFD_EMIT_PREFIX_CURRENT.json').write_text(json.dumps(dict(slot=slot,mode=mode,source=body,native=native,frozen_body=original,fields=fields,values=values,domain='all typed statements, every raw scalar independently arbitrary, i<8 j<32 k<20',classification='complete result initializer with actual getters; one coordinate observation, pure immutable source'),indent=1)+'\n')
