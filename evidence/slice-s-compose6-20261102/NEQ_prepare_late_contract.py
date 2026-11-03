"""Per-shape fidelity and full slice-havoc caller, only local records."""
from pathlib import Path
import sys,subprocess,difflib,json
E=Path(__file__).resolve().parent;mode=sys.argv[1];assert mode in ['support','real','unimplied','inverted','frame','oracle_support','oracle_inverted','caller','wrong_window','inside_unimplied']
subprocess.run([sys.executable,str(E/'NEQ_prepare_window.py'),'1','positive'],check=True)
p='crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs';f=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+p],text=True)
patch=(E.parent/'slice-s-compose2-20261029/NEE_K052-NEE_oracle.patch').read_text();err='PoolV1PairLatePublicStatementErrorV1';error='\n'.join(l[1:] for l in patch.splitlines() if l.startswith('+fn NEE_any_'));error=error.replace('NEE_any_'+err,'any_error')
full=mode.startswith('oracle_') or mode in ['caller','wrong_window','inside_unimplied'];expr='true' if full else '*r==if b{Ok(())}else{Err(PoolV1PairLatePublicStatementErrorV1::Snapshot(PoolV1PairLiveSnapshotErrorV1::TreeFull))}'
if mode in ['inverted','oracle_inverted']:expr='!('+expr+')'
modifies='&mut out[1]' if mode=='frame' else 'out'
result='if kani::any(){Ok(())}else{Err(any_error())}' if full else 'if b{Ok(())}else{Err(PoolV1PairLatePublicStatementErrorV1::Snapshot(PoolV1PairLiveSnapshotErrorV1::TreeFull))}'
body='''use super::*;
use crate::pool_v1::*;
use aspis_core::field::M31;
use crate::Digest;
ERRORFN
impl kani::Arbitrary for PoolV1PairLatePublicStatementErrorV1{fn any()->Self{any_error()}}
#[kani::requires(out.len()==1520)]
#[kani::modifies(MODIFIES)]
#[kani::ensures(|r| EXPR)]
fn weak(_s:&PoolV1PairLatePublicStatementV1,out:&mut[u8;1520],b:bool)->Result<(),PoolV1PairLatePublicStatementErrorV1>{out[0]=42;RESULT}
fn digest()->Digest{[M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any())]}
fn snapshot()->PoolV1PairLatePublicStatementV1{PoolV1PairLatePublicStatementV1{live_snapshot:PoolV1PairLiveSnapshotV1{pool:kani::any(),deployment_domain:kani::any(),sequence:kani::any(),next_pair_index:kani::any(),current_root:digest(),frontier:[NODES]},candidate_afterstate:PoolV1PairVerifiedAfterstateV1{next_pair_index:kani::any(),next_root:digest(),next_frontier:[NODES]}}}
#[kani::proof_for_contract(weak)]
fn support(){let s=snapshot();let mut out:[u8;1520]=kani::any();let _=weak(&s,&mut out,kani::any());}
'''.replace('ERRORFN',error).replace('MODIFIES',modifies).replace('EXPR',expr).replace('RESULT',result).replace('NODES',','.join(['digest()']*20))
if mode in ['real','unimplied']:
 body+='''#[kani::proof]
'''+('#[kani::stub_verified(weak)]\n' if mode=='unimplied' else '')+'''fn shape_control(){let s=snapshot();let mut out:[u8;1520]=kani::any();let old=out[1519];let _=weak(&s,&mut out,kani::any());assert!(out[1519]==old,"unimplied full slice mutation frame");}
'''
if mode in ['caller','wrong_window','inside_unimplied']:
 start=145 if mode=='wrong_window' else 144
 body+='''fn cut(s:&PoolV1PairLatePublicStatementV1,out:&mut[u8;1880])->(Result<(),PoolV1PairForestTerminalFormatErrorV1>,Result<(),PoolV1PairLatePublicStatementErrorV1>){
 let expected=out.as_mut_ptr().wrapping_add(144);let window=&mut out[START..START+1520];assert!(window.as_mut_ptr()==expected && window.len()==1520,"same actual late child window");
 let array:&mut[u8;1520]=window.try_into().unwrap();assert!(array.as_mut_ptr()==expected);let reply=weak(s,array,kani::any());let status=reply.map_err(|error| PoolV1PairForestTerminalFormatErrorV1::LaneTransition(error));(status,reply)
}
#[kani::proof]
#[kani::stub_verified(weak)]
fn full_mutation_caller(){let s=snapshot();let mut output:[u8;1880]=kani::any();let j:usize=kani::any();kani::assume(j<1880);kani::assume(j<144||j>=1664);let old=output[j];let inside=output[1663];let(status,reply)=cut(&s,&mut output);assert!(status==reply.map_err(|error| PoolV1PairForestTerminalFormatErrorV1::LaneTransition(error)),"full arbitrary child Result mapped unchanged");assert!(output[j]==old,"complete outside-child allocation frame");INSIDE}
'''.replace('START',str(start)).replace('INSIDE','assert!(output[1663]==inside,"unimplied caller inside window value");' if mode=='inside_unimplied' else '')
changed=f+'\n#[cfg(kani)]\n#[path="NEQ_slice_contract.rs"]\nmod NEQ_slice_contract;\n';patch=''.join(difflib.unified_diff(f.splitlines(True),changed.splitlines(True),fromfile='a/'+p,tofile='b/'+p));patch+='--- /dev/null\n+++ b/crates/aspis-statement/src/pool_v1/NEQ_slice_contract.rs\n@@ -0,0 +1,'+str(len(body.splitlines()))+' @@\n'+''.join('+'+s+'\n' for s in body.splitlines());(E/'NEQ_native_contracts.patch').write_text(patch)
(E/'NEQ_SLICE_CONTRACT_CURRENT.json').write_text(json.dumps(dict(mode=mode,interface_shape='Result<(),PoolV1PairLatePublicStatementErrorV1>; immutable LateStatement; mutable [u8;1520]; scalar Bool',all_typed_inputs=True,modifies='entire borrowed output slice' if mode!='frame' else 'wrong byte only',full_Result_havoc=full,full_output_havoc=mode in ['caller','wrong_window','inside_unimplied','unimplied'],no_copy_stub=True,rule16=True,trust_classification='P6/D188 option A reclassification; per-shape ruling t controls mandatory'),indent=1)+'\n')
