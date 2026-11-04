"""Actual result-encoder caller, one independently selected output window."""
from NEY_native_patch import E,frozen,helpers
from NEY_source_tools import calls
import sys,json,subprocess,difflib
slot=int(sys.argv[1]);mode=sys.argv[2];assert 0<=slot<9 and mode in ['positive','value','argument']
subprocess.run([sys.executable,str(E/'NEY_prepare_window.py'),'1','positive'],check=True)
p='crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs';f=frozen(p)
name='encode_pool_v1_pair_forest_terminal_result_v1';a=f.index('pub fn '+name+'(');z=f.index('\n}',a)+2;original=f[a:z]
native=original.replace('pub fn '+name+'(','fn native(').replace('    result: &PoolV1PairForestTerminalResultV1,','    result: &PoolV1PairForestTerminalResultV1,f:&mut Frame,')
for old,new in [('validate_result','validate'),('encode_digest_canonical','digest'),('encode_pool_v1_pair_verified_afterstate_v1','after')]:native=calls(native,old,new,'f')
starts=[0,4,5,6,7,8,40,72,104];sizes=[4,1,1,1,1,32,32,32,688]
values=['POOL_V1_PAIR_FOREST_TERMINAL_RESULT_MAGIC[j]','POOL_V1_PAIR_FOREST_TERMINAL_VERSION','r.transition_kind as u8','POOL_V1_DIGEST_ENCODING_VERSION','r.output_lane','r.master_account[j-8]','r.selected_lane_account[j-40]','d[j-72]','after_bytes[j-104]']
base=helpers().replace('aspis_statement::','crate::')
body=base+'''
struct Frame<'a>{record:&'a PoolV1PairForestTerminalResultV1,v:Result<(),PoolV1PairForestTerminalFormatErrorV1>,d:[u8;32],a:Result<[u8;688],PoolV1PairVerifierTransportErrorV1>,calls:u8}
fn validate(r:&PoolV1PairForestTerminalResultV1,f:&mut Frame)->Result<(),PoolV1PairForestTerminalFormatErrorV1>{assert!(f.calls==0&&core::ptr::eq(r,f.record));f.calls=1;f.v}
fn digest(d:&Digest,f:&mut Frame)->[u8;32]{assert!(f.calls==1&&core::ptr::eq(d,&f.record.nullifier));f.calls=2;f.d}
fn after(a:&PoolV1PairVerifiedAfterstateV1,f:&mut Frame)->Result<[u8;688],PoolV1PairVerifierTransportErrorV1>{assert!(f.calls==2&&core::ptr::eq(a,&f.record.verified_afterstate));f.calls=3;f.a}
'''+native+f'''
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
fn result_parent(){{let c=NEE_common();let r=PoolV1PairForestTerminalResultV1{{transition_kind:if kani::any(){{PoolV1TransitionKind::PrivateTransfer}}else{{PoolV1TransitionKind::Withdrawal}},master_account:c.master_account,selected_lane_account:c.selected_lane_account,output_lane:c.output_lane,nullifier:NEE_digest(),verified_afterstate:c.lane_transition.candidate_afterstate}};let d:[u8;32]=kani::any();let after_bytes:[u8;688]=kani::any();let v=if kani::any(){{Ok(())}}else{{Err(any_error())}};let a=if kani::any(){{Ok(after_bytes)}}else{{Err(NEE_any_PoolV1PairVerifierTransportErrorV1())}};let mut frame=Frame{{record:&r,v,d,a,calls:0}};let j:usize=kani::any();kani::assume({starts[slot]}<=j&&j<{starts[slot]+sizes[slot]});let out=native(&r,&mut frame);match v{{Err(e)=>{{assert!(frame.calls==1);assert!(matches!(out,Err(x) if x==e));}},Ok(())=>{{assert!(frame.calls==3);match a{{Err(e)=>assert!(matches!(out,Err(PoolV1PairForestTerminalFormatErrorV1::Afterstate(x)) if x==e)),Ok(_)=>{{let b=out.unwrap();assert!(b[j]==({values[slot]}){'^1' if mode=='value' else ''});}}}}}}}}}}
'''
# All six record fields range independently over their full typed carriers.
h=f+'\n#[cfg(kani)]\n#[path="NEY_result_parent.rs"]\nmod NEY_result_parent;\n'
patch=''.join(difflib.unified_diff(f.splitlines(True),h.splitlines(True),fromfile='a/'+p,tofile='b/'+p))+'--- /dev/null\n+++ b/crates/aspis-statement/src/pool_v1/NEY_result_parent.rs\n@@ -0,0 +1,'+str(len(body.splitlines()))+' @@\n'+''.join('+'+l+'\n' for l in body.splitlines());(E/'NEY_native_contracts.patch').write_text(patch)
(E/'NEY_RESULT_PARENT_CURRENT.json').write_text(json.dumps(dict(slot=slot,mode=mode,start=starts[slot],size=sizes[slot],frozen_body=original,native=native,source=body,domain='all typed result records; complete validator and afterstate Results; arbitrary32-byte digest and688-byte afterstate reply',classification='native actual complete encoder caller, one output window; full parent frame/domain and all afterstate errors need independent validation; no native credit on partial scope'),indent=1)+'\n')
