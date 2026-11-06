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
