use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
struct NKG_ColumnLog { args:[[u32;6];4], replies:[u32;4], calls:usize }
fn NKG_limb(log:&mut NKG_ColumnLog,a:u32,b:u32,c:u32,d:u32,e:u32,f:u32)->M31 {
 let k=log.calls;assert!(k<4);log.args[k]=[a,b,c,d,e,f];log.calls+=1;M31(log.replies[k])
}
fn NKG_column_step(weights:[QM31;3],column0:[u32;16],column1:[u32;16],column2:[u32;16],output:&mut[QM31;16],lane:&mut usize,log:&mut NKG_ColumnLog){
 if *lane<POSEIDON2_WIDTH {
        output[*lane] = QM31 {
            c0: CM31::new(
                NKG_limb(log,
                    weights[0].c0.a.0,
                    weights[1].c0.a.0,
                    weights[2].c0.a.0,
                    column0[*lane],
                    column1[*lane],
                    column2[*lane],
                ),
                NKG_limb(log,
                    weights[0].c0.b.0,
                    weights[1].c0.b.0,
                    weights[2].c0.b.0,
                    column0[*lane],
                    column1[*lane],
                    column2[*lane],
                ),
            ),
            c1: CM31::new(
                NKG_limb(log,
                    weights[0].c1.a.0,
                    weights[1].c1.a.0,
                    weights[2].c1.a.0,
                    column0[*lane],
                    column1[*lane],
                    column2[*lane],
                ),
                NKG_limb(log,
                    weights[0].c1.b.0,
                    weights[1].c1.b.0,
                    weights[2].c1.b.0,
                    column0[*lane],
                    column1[*lane],
                    column2[*lane],
                ),
            ),
        };
        *lane += 1;
    }
}
fn NKG_q()->QM31 {QM31{c0:CM31::new(M31(kani::any()),M31(kani::any())),c1:CM31::new(M31(kani::any()),M31(kani::any()))}}
fn NKG_words(q:QM31)->[u32;4]{[q.c0.a.0,q.c0.b.0,q.c1.a.0,q.c1.b.0]}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::unwind(80)]
fn NKG_columns_iteration(){
 let weights=core::array::from_fn(|_|NKG_q());
 let c0:[u32;16]=kani::any();let c1:[u32;16]=kani::any();let c2:[u32;16]=kani::any();
 let mut out:[QM31;16]=core::array::from_fn(|_|NKG_q());
 let mut lane:usize=kani::any();kani::assume(lane<16);let initial=lane;
 let k:usize=kani::any();let j:usize=kani::any();kani::assume(k<16&&j<4);
 let old=NKG_words(out[k]);let replies:[u32;4]=kani::any();
 let mut log=NKG_ColumnLog{args:[[0;6];4],replies,calls:0};
 NKG_column_step(weights,c0,c1,c2,&mut out,&mut lane,&mut log);
 if cfg!(NKG_bad_output){out[k].c0.a.0^=1;}
 if cfg!(NKG_bad_argument){log.args[j][3]^=1;}
 assert_eq!(lane,initial+1);assert_eq!(log.calls,4);
 assert_eq!(log.args[j],[NKG_words(weights[0])[j],NKG_words(weights[1])[j],NKG_words(weights[2])[j],c0[initial],c1[initial],c2[initial]]);
 assert_eq!(NKG_words(out[k]),if k==initial{replies}else{old});
}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::unwind(80)]
fn NKG_columns_stop(){
 let weights=core::array::from_fn(|_|NKG_q());
 let c0:[u32;16]=kani::any();let c1:[u32;16]=kani::any();let c2:[u32;16]=kani::any();
 let mut out:[QM31;16]=core::array::from_fn(|_|NKG_q());
 let mut lane:usize=kani::any();kani::assume(lane>=16);let initial=lane;
 let k:usize=kani::any();kani::assume(k<16);let before=NKG_words(out[k]);
 let mut log=NKG_ColumnLog{args:[[0;6];4],replies:kani::any(),calls:0};
 NKG_column_step(weights,c0,c1,c2,&mut out,&mut lane,&mut log);
 if cfg!(NKG_bad_output){out[k].c0.a.0^=1;}
 assert_eq!(lane,initial);assert_eq!(log.calls,0);assert_eq!(NKG_words(out[k]),before);
}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::unwind(80)]
fn NKG_columns_initial(){
 let mut output = [QM31::ZERO; POSEIDON2_WIDTH];
 let lane = 0usize;
 let k:usize=kani::any();kani::assume(k<16);
 if cfg!(NKG_bad_output){output[k].c0.a.0^=1;}
 assert_eq!(lane,0);assert_eq!(NKG_words(output[k]),[0;4]);
}

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
    let middle = NKG_round(log,state, even);
    NKG_round(log,middle, odd)
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

struct NKG_FullLog { weights:[[QM31;3];2],columns:[[[u32;16];3];2],replies:[[QM31;16];2],calls:usize,states:[[QM31;16];2],constants:[[QM31;16];2],middle:[QM31;16],packed:[QM31;4],round_calls:usize }
fn NKG_columns(log:&mut NKG_FullLog,w:[QM31;3],a:[u32;16],b:[u32;16],c:[u32;16])->[QM31;16]{let k=log.calls;assert!(k<2);log.weights[k]=w;log.columns[k]=[a,b,c];log.calls+=1;log.replies[k]}
fn NKG_full(log:&mut NKG_FullLog,s:[QM31;16],c:[QM31;16])->[QM31;16]{assert_eq!(log.round_calls,0);log.states[0]=s;log.constants[0]=c;log.round_calls=1;log.middle}
fn NKG_full_packed(log:&mut NKG_FullLog,s:[QM31;16],c:[QM31;16])->[QM31;4]{assert_eq!(log.round_calls,1);log.states[1]=s;log.constants[1]=c;log.round_calls=2;log.packed}
fn NKG_full_pair(
    state: [QM31; POSEIDON2_WIDTH],
    local: &[QM31; 16], log: &mut NKG_FullLog,
) -> [QM31; STATE_ONLY_POSEIDON_PACKED_LANES] {
    let weights = [local[1], local[9], local[10]];
    let even = NKG_columns(log,
        weights,
        EXTERNAL_INITIAL[2],
        EXTERNAL_FINAL[0],
        EXTERNAL_FINAL[2],
    );
    let odd = NKG_columns(log,
        weights,
        EXTERNAL_INITIAL[3],
        EXTERNAL_FINAL[1],
        EXTERNAL_FINAL[3],
    );
    {let middle=NKG_full(log,state,even);NKG_full_packed(log,middle,odd)}
}

#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::unwind(80)]
fn NKG_full_calls(){
 let s:[QM31;16]=core::array::from_fn(|_|NKG_q());let l:[QM31;16]=core::array::from_fn(|_|NKG_q());
 let replies:[[QM31;16];2]=core::array::from_fn(|_|core::array::from_fn(|_|NKG_q()));let middle:[QM31;16]=core::array::from_fn(|_|NKG_q());let packed:[QM31;4]=core::array::from_fn(|_|NKG_q());
 let mut log=NKG_FullLog{weights:[[QM31::ZERO;3];2],columns:[[[0;16];3];2],replies,calls:0,states:[[QM31::ZERO;16];2],constants:[[QM31::ZERO;16];2],middle,packed,round_calls:0};
 let call:usize=kani::any();let j:usize=kani::any();let k:usize=kani::any();let g:usize=kani::any();kani::assume(call<2&&j<3&&k<16&&g<4);
 let mut out=NKG_full_pair(s,&l,&mut log);
 if cfg!(NKG_bad_output){out[g].c0.a.0^=1;}
 if cfg!(NKG_bad_argument){log.weights[call][j].c0.a.0^=1;}
 assert_eq!(log.calls,2);assert_eq!(log.round_calls,2);
 assert_eq!(NKG_words(log.weights[call][j]),NKG_words(l[[1,9,10][j]]));
 assert_eq!(log.columns[call][j][k],if j==0{EXTERNAL_INITIAL[2+call][k]}else{EXTERNAL_FINAL[2*(j-1)+call][k]});
 assert_eq!(NKG_words(log.states[0][k]),NKG_words(s[k]));assert_eq!(NKG_words(log.states[1][k]),NKG_words(middle[k]));
 assert_eq!(NKG_words(log.constants[call][k]),NKG_words(replies[call][k]));assert_eq!(NKG_words(out[g]),NKG_words(packed[g]));
}
