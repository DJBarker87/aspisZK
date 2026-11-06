use super::*;
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
fn NJP_controller<F>(state: &mut [M31; 16], mut trace: F, log: &mut NJP_Control)
where
    F: FnMut(Poseidon2RoundTransition),
{
    let mut round = 0u8;
    let mut input = *state;
    NJP_linear_control(log, 0);
    for (index, constants) in EXTERNAL_INITIAL.iter().enumerate() {
        for index in 0..16 {
            NJP_cell_control(log, index, constants[index]);
        }
        NJP_linear_control(log, 0);
        NJP_callback(log, &mut trace, Poseidon2RoundTransition {
            round,
            kind: Poseidon2RoundKind::ExternalInitial(index as u8),
            input,
            output: *state,
        });
        round += 1;
        input = *state;
    }
    for (index, constant) in INTERNAL.into_iter().enumerate() {
        NJP_cell_control(log, 0, constant);
        NJP_linear_control(log, 1);
        NJP_callback(log, &mut trace, Poseidon2RoundTransition {
            round,
            kind: Poseidon2RoundKind::Internal(index as u8),
            input,
            output: *state,
        });
        round += 1;
        input = *state;
    }
    for (index, constants) in EXTERNAL_FINAL.iter().enumerate() {
        for index in 0..16 {
            NJP_cell_control(log, index, constants[index]);
        }
        NJP_linear_control(log, 0);
        NJP_callback(log, &mut trace, Poseidon2RoundTransition {
            round,
            kind: Poseidon2RoundKind::ExternalFinal(index as u8),
            input,
            output: *state,
        });
        round += 1;
        input = *state;
    }
    debug_assert_eq!(round as usize, POSEIDON2_ROUNDS);
}

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
fn NJP_compress(left: &Digest, right: &Digest, log: &mut NJP_PermutationLog) -> Digest {
    let mut state = [M31::ZERO; POSEIDON2_WIDTH];
    state[..DIGEST_ELEMS].copy_from_slice(left);
    state[DIGEST_ELEMS..].copy_from_slice(right);
    // Fixed node-domain tweak. This construction is never reused for leaves
    // or variable-length inputs; the ordered 16-limb input is the full state.
    state[POSEIDON2_WIDTH - 1] = state[POSEIDON2_WIDTH - 1].add(MERKLE_NODE_COMPRESSION_V3_TWEAK);
    NJP_permutation(log, &mut state);
    core::array::from_fn(|index| state[index])
}

struct NJP_PermutationLog { calls:usize, seed:[M31;16], reply:[M31;16] }
fn NJP_permutation(log:&mut NJP_PermutationLog,state:&mut[M31;16]) {
 assert_eq!(log.calls,0);log.calls+=1;log.seed=*state;
 for i in 0..16 { assert!(state[i].0<2147483647); }
 *state=log.reply;
}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[M31]>::copy_from_slice,KMX_copy_from_slice)]
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
