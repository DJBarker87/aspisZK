"""Frozen emitter: two child cuts and trace-bearing return-data observation."""
from NEY_native_patch import E,frozen,helpers,program
from NEY_source_tools import calls
import sys,json,subprocess
mode=sys.argv[1];assert mode in ['positive','byte','order','argument']
subprocess.run([sys.executable,str(E/'NEY_prepare_window.py'),'1','positive'],check=True)
p='programs/r1-cost-probe/src/r1_pool_adapter.rs';f=frozen(p);a=f.index('fn emit_result(');z=f.index('\n}',a)+2;original=f[a:z]
native=original.replace('fn emit_result(statement: &PoolV1PairForestTerminalStatementV1) -> ProgramResult','fn native(statement: &PoolV1PairForestTerminalStatementV1,f:&mut Frame) -> ProgramResult')
for old,new in [('validate_pool_v1_pair_forest_terminal_result_against_statement_v1','binding'),('encode_pool_v1_pair_forest_terminal_result_v1','encode'),('program::set_return_data','send')]:native=calls(native,old,new,'f')
if mode=='argument':native=native.replace('send(&encoded,f)','send(&encoded[1..],f)')
body=helpers()+'''
struct Frame<'a>{s:&'a PoolV1PairForestTerminalStatementV1,b:Result<(),PoolV1PairForestTerminalFormatErrorV1>,e:Result<[u8;792],PoolV1PairForestTerminalFormatErrorV1>,record:*const PoolV1PairForestTerminalResultV1,calls:u8,j:usize,sent:Option<u8>}
fn binding(s:&PoolV1PairForestTerminalStatementV1,r:&PoolV1PairForestTerminalResultV1,f:&mut Frame)->Result<(),PoolV1PairForestTerminalFormatErrorV1>{assert!(f.calls==0&&core::ptr::eq(s,f.s));f.record=r;f.calls=1;f.b}
fn encode(r:&PoolV1PairForestTerminalResultV1,f:&mut Frame)->Result<[u8;792],PoolV1PairForestTerminalFormatErrorV1>{assert!(f.calls==1&&core::ptr::eq(r,f.record));f.calls=2;f.e}
fn send(bytes:&[u8],f:&mut Frame){assert!(f.calls==2&&bytes.len()==792);f.calls=3;f.sent=Some(bytes[f.j]);}
'''+native+'''
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NEY_KMX::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,crate::NEY_KMX::KMX_copy_from_slice)]
fn emit_parent(){let s=NEE_statement();let b=if kani::any(){Ok(())}else{Err(any_error())};let raw:[u8;792]=kani::any();let e=if kani::any(){Ok(raw)}else{Err(any_error())};let j:usize=kani::any();kani::assume(j<792);let mut frame=Frame{s:&s,b,e,record:core::ptr::null(),calls:0,j,sent:None};let actual=native(&s,&mut frame);match b{Err(_)=>{assert!(frame.calls==1&&frame.sent==None);assert!(actual==Err(ProgramError::InvalidInstructionData));},Ok(())=>match e{Err(_)=>{assert!(frame.calls==2&&frame.sent==None);assert!(actual==Err(ProgramError::InvalidInstructionData));},Ok(_)=>{let valid=raw[0]==65&&raw[1]==83&&raw[2]==82&&raw[3]==56;if valid{assert!(actual==Ok(()));assert!(frame.calls==@CALLS@&&frame.sent==Some(raw[j]@BYTE@));}else{assert!(actual==Err(ProgramError::InvalidInstructionData));assert!(frame.calls==2&&frame.sent==None);}}}}}
'''
body=body.replace('@CALLS@','2' if mode=='order' else '3').replace('@BYTE@','^1' if mode=='byte' else '')
program(body,'NEY_emit_parent')
(E/'NEY_EMIT_PARENT_CURRENT.json').write_text(json.dumps(dict(mode=mode,frozen_body=original,native=native,source=body,domain='all typed statements, arbitrary complete binding/encoder Results and every792-byte returned buffer; arbitrary observation byte',classification='complete frozen emitter with local ordered typed log and exact return-data event byte, no syscall implementation; derived-record prefix association reused separately; RuntimeReturnData under ab is ADDED trust'),indent=1)+'\n')
