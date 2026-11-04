"""Derived-record binding continuation; complete typed child Results, local logs."""
from NEY_native_patch import E,frozen,helpers
from NEY_source_tools import calls
import sys,json,subprocess,difflib
mode=sys.argv[1];assert mode in ['positive','value','argument']
subprocess.run([sys.executable,str(E/'NEY_prepare_window.py'),'1','positive'],check=True)
p='crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs';f=frozen(p)
name='validate_pool_v1_pair_forest_terminal_result_against_statement_v1';a=f.index('pub fn '+name+'(');z=f.index('\n}',a)+2;original=f[a:z]
native=original.replace('pub fn '+name+'(','fn native(').replace('    result: &PoolV1PairForestTerminalResultV1,','    result: &PoolV1PairForestTerminalResultV1,f:&mut Frame,')
for old,new in [('validate_pool_v1_pair_forest_terminal_statement_v1','statement'),('validate_result','result')]:native=calls(native,old,new,'f')
body=helpers().replace('aspis_statement::','crate::')+'''
struct Frame<'a>{s:&'a PoolV1PairForestTerminalStatementV1,r:&'a PoolV1PairForestTerminalResultV1,first:Result<(),PoolV1PairForestTerminalFormatErrorV1>,second:Result<(),PoolV1PairForestTerminalFormatErrorV1>,calls:u8}
fn statement(s:&PoolV1PairForestTerminalStatementV1,f:&mut Frame)->Result<(),PoolV1PairForestTerminalFormatErrorV1>{assert!(f.calls==0&&core::ptr::eq(s,f.s));f.calls=1;f.first}
fn result(r:&PoolV1PairForestTerminalResultV1,f:&mut Frame)->Result<(),PoolV1PairForestTerminalFormatErrorV1>{assert!(f.calls==1&&core::ptr::eq(r,f.r));f.calls=2;f.second}
'''+native+'''
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
fn binding(){let s=NEE_statement();let c=s.common();let mut r=PoolV1PairForestTerminalResultV1{transition_kind:s.transition_kind(),master_account:c.master_account,selected_lane_account:c.selected_lane_account,output_lane:c.output_lane,nullifier:*s.nullifier(),verified_afterstate:c.lane_transition.candidate_afterstate};@CORRUPT@
let first=if kani::any(){Ok(())}else{Err(any_error())};let second=if kani::any(){Ok(())}else{Err(any_error())};let mut frame=Frame{s:&s,r:&r,first,second,calls:0};let out=native(&s,&r,&mut frame);let expected=match first{Err(e)=>{assert!(frame.calls==1);Err(e)},Ok(())=>{assert!(frame.calls==2);second}};assert!(out==@EXPECTED@);}
'''
body=body.replace('@CORRUPT@','r.master_account[0]^=1;' if mode=='argument' else '')
body=body.replace('@EXPECTED@','expected.map(|_|()).and(Err(PoolV1PairForestTerminalFormatErrorV1::ResultBindingMismatch))' if mode=='value' else 'expected')
h=f+'\n#[cfg(kani)]\n#[path="NEY_binding.rs"]\nmod NEY_binding;\n'
patch=''.join(difflib.unified_diff(f.splitlines(True),h.splitlines(True),fromfile='a/'+p,tofile='b/'+p))+'--- /dev/null\n+++ b/crates/aspis-statement/src/pool_v1/NEY_binding.rs\n@@ -0,0 +1,'+str(len(body.splitlines()))+' @@\n'+''.join('+'+l+'\n' for l in body.splitlines());(E/'NEY_native_contracts.patch').write_text(patch)
(E/'NEY_BINDING_CURRENT.json').write_text(json.dumps(dict(mode=mode,frozen_body=original,native=native,source=body,domain='all typed statements; result derived by exact frozen emit_result construction; arbitrary complete statement/result validator Results',classification='native caller-derived binding continuation; conditional domain must be proved by each caller, no assumption of either validator success'),indent=1)+'\n')
