"""Redesigned emission cuts: scalar log only, no retained duplicate792-byte reply."""
from NFD_native_patch import E,frozen,helpers,program
from NFD_source_tools import calls
import subprocess,sys,json,hashlib
mode=sys.argv[1];assert mode in ['positive','byte','order','argument']
subprocess.run([sys.executable,str(E/'NFD_prepare_window.py'),'1','positive'],check=True)
p='programs/r1-cost-probe/src/r1_pool_adapter.rs';f=frozen(p);a=f.index('fn emit_result(');z=f.index('\n}',a)+2;original=f[a:z]
cut=original.index('    validate_pool_v1_pair_forest_terminal_result_against_statement_v1')
native='fn native(statement:&PoolV1PairForestTerminalStatementV1,result:PoolV1PairForestTerminalResultV1,f:&mut Frame)->ProgramResult{\n'+original[cut:]
for old,new in [('validate_pool_v1_pair_forest_terminal_result_against_statement_v1','binding'),('encode_pool_v1_pair_forest_terminal_result_v1','encode'),('program::set_return_data','send')]:native=calls(native,old,new,'f')
if mode=='argument':native=native.replace('send(&encoded,f)','send(&encoded[1..],f)')
body=helpers()+'''
struct Frame<'a>{s:&'a PoolV1PairForestTerminalStatementV1,record:*const PoolV1PairForestTerminalResultV1,calls:u8,j:usize,b_ok:bool,e_ok:bool,valid:bool,byte:u8,sent:Option<u8>}
fn binding(s:&PoolV1PairForestTerminalStatementV1,r:&PoolV1PairForestTerminalResultV1,f:&mut Frame)->Result<(),PoolV1PairForestTerminalFormatErrorV1>{assert!(f.calls==0&&core::ptr::eq(s,f.s));f.record=r;f.calls=1;f.b_ok=kani::any();if f.b_ok{Ok(())}else{Err(any_error())}}
fn encode(r:&PoolV1PairForestTerminalResultV1,f:&mut Frame)->Result<[u8;792],PoolV1PairForestTerminalFormatErrorV1>{assert!(f.calls==1&&core::ptr::eq(r,f.record));f.calls=2;f.e_ok=kani::any();if f.e_ok{let raw:[u8;792]=kani::any();f.valid=raw[0]==65&&raw[1]==83&&raw[2]==82&&raw[3]==56;f.byte=raw[f.j];Ok(raw)}else{Err(any_error())}}
fn send(bytes:&[u8],f:&mut Frame){assert!(f.calls==2&&bytes.len()==792);f.calls=3;f.sent=Some(bytes[f.j]);}
'''+native+'''
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFD_KMX::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,crate::NFD_KMX::KMX_copy_from_slice)]
fn emit_continuation(){let s=NEE_statement();let r=PoolV1PairForestTerminalResultV1{transition_kind:s.transition_kind(),master_account:kani::any(),selected_lane_account:kani::any(),output_lane:kani::any(),nullifier:NEE_digest(),verified_afterstate:NEE_common().lane_transition.candidate_afterstate};let j:usize=kani::any();kani::assume(j<792);let mut frame=Frame{s:&s,record:core::ptr::null(),calls:0,j,b_ok:false,e_ok:false,valid:false,byte:0,sent:None};let actual=native(&s,r,&mut frame);if !frame.b_ok{assert!(frame.calls==1&&frame.sent==None&&matches!(actual,Err(ProgramError::InvalidInstructionData)));}else if !frame.e_ok||!frame.valid{assert!(frame.calls==2&&frame.sent==None&&matches!(actual,Err(ProgramError::InvalidInstructionData)));}else{assert!(frame.calls==@CALLS@&&frame.sent==Some(frame.byte@BYTE@)&&matches!(actual,Ok(())));}}
'''
body=body.replace('@CALLS@','2' if mode=='order' else '3').replace('@BYTE@','^1' if mode=='byte' else '')
program(body,'NFD_emit_continuation')
(E/'NFD_EMIT_CURRENT.json').write_text(json.dumps(dict(mode=mode,frozen_body=original,native=native,source=body,domain='all typed statement and result carriers; every encoder return byte; full error enum; scalar local log, no duplicate reply',classification='source suffix cut after result construction; arbitrary one byte return-data event at j<792; prefix association still required',timeout_redesign='NEY129-132 duplicated full Result792 in caller frame; new oracle generates its complete reply once and logs only five observed bytes and scalar tags'),indent=1)+'\n')
