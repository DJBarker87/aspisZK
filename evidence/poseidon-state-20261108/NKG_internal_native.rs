
struct NKG_InternalLog { weights:[[QM31;7];2], constants:[[M31;7];2], dots:[QM31;2], dot_calls:usize,states:[[QM31;16];2],round_constants:[QM31;2],round_replies:[[QM31;16];2],round_calls:usize }
fn NKG_dot(log:&mut NKG_InternalLog,w:&[QM31],c:&[M31])->QM31 {
 let k=log.dot_calls;assert!(k<2);assert_eq!(w.len(),7);assert_eq!(c.len(),7);
 log.weights[k]=core::array::from_fn(|i|w[i]);log.constants[k]=core::array::from_fn(|i|c[i]);log.dot_calls+=1;log.dots[k]
}
fn NKG_round(log:&mut NKG_InternalLog,s:[QM31;16],c:QM31)->[QM31;16] {
 let k=log.round_calls;assert!(k<2);log.states[k]=s;log.round_constants[k]=c;log.round_calls+=1;log.round_replies[k]
}
fn NKG_internal_pair(
    state: [QM31; POSEIDON2_WIDTH],
    local: &[QM31; 16], log: &mut NKG_InternalLog,
) -> [QM31; POSEIDON2_WIDTH] {
    const ROWS: [usize; 7] = [2, 3, 4, 5, 6, 7, 8];
    let weights = ROWS.map(|row| local[row]);
    let even_constants = ROWS.map(|row| M31(INTERNAL[2 * (row - 2)]));
    let odd_constants = ROWS.map(|row| M31(INTERNAL[2 * (row - 2) + 1]));
    let even = NKG_dot(log,&weights, &even_constants);
    let odd = NKG_dot(log,&weights, &odd_constants);
    NKG_round(log,NKG_round(log,state, even), odd)
}

#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::unwind(80)]
fn NKG_internal_calls(){
 let state:[QM31;16]=core::array::from_fn(|_|NKG_q());let local:[QM31;16]=core::array::from_fn(|_|NKG_q());
 let dots:[QM31;2]=core::array::from_fn(|_|NKG_q());let round_replies:[[QM31;16];2]=core::array::from_fn(|_|core::array::from_fn(|_|NKG_q()));
 let mut log=NKG_InternalLog{weights:[[QM31::ZERO;7];2],constants:[[M31::ZERO;7];2],dots,dot_calls:0,states:[[QM31::ZERO;16];2],round_constants:[QM31::ZERO;2],round_replies,round_calls:0};
 let k:usize=kani::any();let j:usize=kani::any();let call:usize=kani::any();kani::assume(k<16&&j<7&&call<2);
 let before=NKG_words(local[k]);let mut out=NKG_internal_pair(state,&local,&mut log);
 if cfg!(NKG_bad_output){out[k].c0.a.0^=1;}
 if cfg!(NKG_bad_argument){log.weights[call][j].c0.a.0^=1;}
 assert_eq!(log.dot_calls,2);assert_eq!(log.round_calls,2);
 assert_eq!(NKG_words(log.weights[call][j]),NKG_words(local[j+2]));
 assert_eq!(log.constants[call][j].0,INTERNAL[2*j+call]);
 assert_eq!(NKG_words(log.states[0][k]),NKG_words(state[k]));
 assert_eq!(NKG_words(log.states[1][k]),NKG_words(round_replies[0][k]));
 assert_eq!(NKG_words(log.round_constants[call]),NKG_words(dots[call]));
 assert_eq!(NKG_words(out[k]),NKG_words(round_replies[1][k]));assert_eq!(NKG_words(local[k]),before);
}
