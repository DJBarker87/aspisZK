from pathlib import Path
import subprocess,sys,json,difflib
E=Path(__file__).resolve().parent;mode=sys.argv[1];assert mode in ['positive','wrong_reply','wrong_record','wrong_zero','return','return_negative','geometry','geometry_negative']
subprocess.run([sys.executable,str(E/'NEQ_prepare_result_validator.py'),'positive'],check=True)
p='crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs';f=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+p],text=True)
seed=(E/'NEQ_native_contracts.patch').read_text();_,rest=seed.split('--- /dev/null\n+++ b/crates/aspis-statement/src/pool_v1/NEQ_result_validator.rs\n',1);raw=''.join(l[1:]+'\n' for l in rest.splitlines()[1:] if l.startswith('+'));construct=raw[:raw.index('struct Frame')];a=raw.index('fn result()->');z=raw.index('\n#[kani::proof]',a);construct+=raw[a:z]+'\n'
body=construct+'''
struct Frame<'a>{expected:&'a PoolV1PairForestTerminalResultV1,other:&'a PoolV1PairForestTerminalResultV1,reply:Result<(),PoolV1PairForestTerminalFormatErrorV1>,called:bool,reached:bool,j:usize,byte:u8}
fn child(r:&PoolV1PairForestTerminalResultV1,f:&mut Frame)->Result<(),PoolV1PairForestTerminalFormatErrorV1>{assert!(!f.called&&core::ptr::eq(r,f.expected));f.called=true;REPLY}
fn prefix(r:&PoolV1PairForestTerminalResultV1,f:&mut Frame)->Result<(),PoolV1PairForestTerminalFormatErrorV1>{child(ARG,f)?;let output=[ZEROu8;792];f.byte=output[f.j];f.reached=true;Ok(())}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn result_prefix(){let r=result();let other=result();let j:usize=kani::any();kani::assume(j<792);let mut f=Frame{expected:&r,other:&other,reply:if kani::any(){Ok(())}else{Err(any_error())},called:false,reached:false,j,byte:0};let actual=prefix(&r,&mut f);assert!(actual==f.reply&&f.called&&f.reached==actual.is_ok(),"all result validation Errors and continuation order");if f.reached{assert!(f.byte==0,"entire result output zero initialization");}}
fn finish(mut output:[u8;792])->Result<[u8;792],PoolV1PairForestTerminalFormatErrorV1>{CORRUPTOk(output)}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
fn result_return(){let output:[u8;792]=kani::any();let j:usize=kani::any();kani::assume(j<792);let old=output[j];match finish(output){Ok(bytes)=>assert!(bytes[j]==old,"complete typed792 returned byte"),Err(_)=>assert!(false)}}
#[kani::proof]
fn result_geometry(){assert!(RESULT_MASTER_OFFSET==8&&RESULT_SELECTED_LANE_OFFSET==40&&RESULT_NULLIFIER_OFFSET==72&&RESULT_AFTERSTATE_OFFSET==104&&POOL_V1_PAIR_FOREST_TERMINAL_RESULT_BYTES==SIZE);}
'''.replace('REPLY','if f.reply.is_ok(){Err(PoolV1PairForestTerminalFormatErrorV1::WrongMagic)}else{Ok(())}' if mode=='wrong_reply' else 'f.reply').replace('ARG','f.other' if mode=='wrong_record' else 'r').replace('ZERO','1' if mode=='wrong_zero' else '0').replace('CORRUPT','output[0]^=1;' if mode=='return_negative' else '').replace('SIZE','793' if mode=='geometry_negative' else '792')
changed=f+'\n#[cfg(kani)]\n#[path="NEQ_result_prefix.rs"]\nmod NEQ_result_prefix;\n';patch=''.join(difflib.unified_diff(f.splitlines(True),changed.splitlines(True),fromfile='a/'+p,tofile='b/'+p))+'--- /dev/null\n+++ b/crates/aspis-statement/src/pool_v1/NEQ_result_prefix.rs\n@@ -0,0 +1,'+str(len(body.splitlines()))+' @@\n'+''.join('+'+l+'\n' for l in body.splitlines());(E/'NEQ_native_contracts.patch').write_text(patch)
(E/'NEQ_RESULT_PREFIX_CURRENT.json').write_text(json.dumps(dict(mode=mode,all_typed_inputs=True,full_validator_Result=True,all_observed_indices=True,classification='result encoder source prefix, typed return and constant geometry; local support, no whole-root claim'),indent=1)+'\n')
