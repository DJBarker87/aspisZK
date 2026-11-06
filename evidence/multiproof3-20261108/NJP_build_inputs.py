from pathlib import Path
import subprocess,json,hashlib
E=Path(__file__).resolve().parent
rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
raw=subprocess.check_output(['git','show',rev+':crates/aspis-statement/src/poseidon2.rs']).decode()
start=raw.index('pub fn permute_optimized_with_trace<F>');end=raw.index('\n/// Domain-separated',start)
source=raw[start:end]
body=source.replace('pub fn permute_optimized_with_trace<F>(state: &mut [M31; 16], mut trace: F)', 'fn NJP_controller<F>(state: &mut [M31; 16], mut trace: F, log: &mut NJP_Control)')
body=body.replace('external_linear_lazy(state);','NJP_linear_control(log, 0);').replace('internal_linear_lazy(state);','NJP_linear_control(log, 1);')
body=body.replace('state[index] = pow5(state[index].add(M31(constants[index])));','NJP_cell_control(log, index, constants[index]);')
body=body.replace('state[0] = pow5(state[0].add(M31(constant)));','NJP_cell_control(log, 0, constant);')
body=body.replace('trace(Poseidon2RoundTransition {','NJP_callback(log, &mut trace, Poseidon2RoundTransition {')
preamble='''use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
// Ruling (ad) control only: every arithmetic body is a recording boundary.
// No data-value credit follows from this controller certificate.
struct NJP_Control { pairs:[(u8,u8);22], at:usize, cells:usize, external:usize, internal:usize }
fn NJP_linear_control(log:&mut NJP_Control, kind:u8) {
 if kind==0 {log.external+=1;} else {log.internal+=1;}
}
fn NJP_cell_control(log:&mut NJP_Control, _lane:usize, _constant:u32) { log.cells+=1; }
fn NJP_callback<F:FnMut(Poseidon2RoundTransition)>(log:&mut NJP_Control, trace:&mut F, event:Poseidon2RoundTransition) {
 let kind=match event.kind { Poseidon2RoundKind::ExternalInitial(i)=>i, Poseidon2RoundKind::Internal(i)=>32+i, Poseidon2RoundKind::ExternalFinal(i)=>64+i };
 assert!(log.at<22);
 log.pairs[log.at]=(event.round,kind);log.at+=1;trace(event);
}
'''
harness='''
fn NJP_controller_case() {
 let mut state=[M31(0);16];
 let mut log=NJP_Control{pairs:[(0,0);22],at:0,cells:0,external:0,internal:0};
 NJP_controller(&mut state, |_| {}, &mut log);
 if cfg!(NJP_bad_argument){log.pairs[9].1^=1;}
 assert_eq!(log.at,22);assert_eq!(log.cells,142);assert_eq!(log.external,9);assert_eq!(log.internal,14);
 let r:usize=kani::any();kani::assume(r<22);
 assert_eq!(log.pairs[r],(r as u8,if r<4{r as u8}else if r<18{32+(r-4) as u8}else{64+(r-18) as u8}));
}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::unwind(24)]
fn NJP_permutation_controller(){NJP_controller_case();}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::unwind(24)]
fn NJP_permutation_controller_stability(){NJP_controller_case();}
'''
compress_start=raw.index('pub fn merkle_node_compress_v3(');compress_end=raw.index('\n/// The exact sponge',compress_start)
compress=raw[compress_start:compress_end].replace('pub fn merkle_node_compress_v3(left: &Digest, right: &Digest)', 'fn NJP_compress(left: &Digest, right: &Digest, log: &mut NJP_PermutationLog)')
compress=compress.replace('permute_optimized_with_trace(&mut state, |_| {});','NJP_permutation(log, &mut state);')
extra='''
struct NJP_PermutationLog { calls:usize, seed:[M31;16], reply:[M31;16] }
fn NJP_permutation(log:&mut NJP_PermutationLog,state:&mut[M31;16]) {
 assert_eq!(log.calls,0);log.calls+=1;log.seed=*state;
 for i in 0..16 { assert!(state[i].0<2147483647); }
 *state=log.reply;
}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::unwind(40)]
fn NJP_compression_caller() {
 let left:Digest=core::array::from_fn(|_|M31(kani::any()));let right:Digest=core::array::from_fn(|_|M31(kani::any()));
 for i in 0..8 {kani::assume(left[i].0<2147483647&&right[i].0<2147483647);}
 let reply:[M31;16]=core::array::from_fn(|_|M31(kani::any()));
 let k:usize=kani::any();let j:usize=kani::any();kani::assume(k<16&&j<8);
 let l=left[j];let r=right[j];
 let mut log=NJP_PermutationLog{calls:0,seed:[M31(0);16],reply};
 let mut out=NJP_compress(&left,&right,&mut log);
 if cfg!(NJP_bad_argument){out[j].0^=1;}
 if cfg!(NJP_bad_seed){log.seed[k].0^=1;}
 assert_eq!(log.calls,1);
 let expected=if k<8{left[k]}else if k==15{right[7].add(MERKLE_NODE_COMPRESSION_V3_TWEAK)}else{right[k-8]};
 assert_eq!(log.seed[k],expected);assert_eq!(out[j],reply[j]);assert_eq!(left[j],l);assert_eq!(right[j],r);
}
'''
extra=extra.replace('#[kani::unwind(40)]\nfn NJP_compression_caller()', '#[kani::stub(<[M31]>::copy_from_slice,KMX_copy_from_slice)]\n#[kani::unwind(40)]\nfn NJP_compression_caller()')
(E/'NJP_poseidon.rs').write_text(preamble+body+harness+compress+extra)
(E/'NJP_CONTROLLER_SOURCE.json').write_text(json.dumps({'frozen_revision':rev,'frozen_file_sha256':hashlib.sha256(raw.encode()).hexdigest(),'function_sha256':hashlib.sha256(source.encode()).hexdigest(),'generated_sha256':hashlib.sha256((preamble+body+harness+compress+extra).encode()).hexdigest(),'replacements':{'scalar':'NJP_cell_control (control only)','linear':'NJP_linear_control (control only)','trace':'record actual event.round and enum variant/index before SAME trace; callback instantiated |_| {}'},'value_credit':False},indent=2)+'\n')
