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
