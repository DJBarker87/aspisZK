use super::*;
fn same<const N:usize>(row:u8,bytes:&[u8],offset:usize){
    let actual=XRg_Record{row,framed:bytes}.decode_k::<N>(offset);
    assert_eq!(actual,XRg_decode_reference::<N>(row,bytes,offset));
}
#[kani::proof] #[kani::unwind(40)]
fn XRg_fallback_closure(){use aspis_r1_cost_probe::sampler::CircleRow;use aspis_core::circle::CirclePointError;let second:bool=kani::any();let err:bool=kani::any();let row=if second{CircleRow::Second}else{CircleRow::First};let e=if err{CirclePointError::SingularParameter}else{CirclePointError::ParameterInCm31Subfield};let got=XRg_circle_fallback(row,e);let expected=XRg_fallback_reference(second);assert!(got.x==expected.x&&got.y==expected.y);}
#[kani::proof] #[kani::unwind(40)]
fn XRg_dot_fold(){let sums:[u64;4]=kani::any();let raw:[u64;4]=kani::any();let i:usize=kani::any();kani::assume(i<4);let mut dot=XRg_Dot{sums};dot.push_raw(raw);assert_eq!(dot.sums[i],XRg_dot_reference(sums,raw,i));}
#[kani::proof] #[kani::unwind(40)]
fn XRg_boundary_sparse(){let raw:[u8;16]=kani::any();let x=K::from_le_bytes(&raw).unwrap_or(K::ZERO);let i:usize=kani::any();kani::assume(i<28);let mut p=[K::ZERO;28];p[i]=x;let expected=if i==0{x.add(x)}else{x};assert_eq!(XRg_semantic_boundary(&p),expected);assert_eq!(XRg_boundary_reference(&p),expected);}
#[kani::proof] #[kani::unwind(40)]
fn XRg_decode_one(){let b:[u8;37]=kani::any();same::<1>(25,&b,0);}
#[kani::proof] #[kani::unwind(40)]
fn XRg_decode_offset_one(){let b:[u8;69]=kani::any();same::<1>(25,&b,1);}
#[kani::proof] #[kani::unwind(40)]
fn XRg_validate_one(){let b:[u8;32]=kani::any();let row:u8=kani::any();assert_eq!(XRg_validate_record_fields(row,&b),XRg_validate_reference(row,&b));}
#[kani::proof] #[kani::unwind(40)]
fn XRg_validate_tail(){let b:[u8;63]=kani::any();let n:usize=kani::any();kani::assume(n>=32&&n<=63);assert_eq!(XRg_validate_record_fields(25,&b[..n]),XRg_validate_reference(25,&b[..n]));}
fn rows()->[Result<[K;29],Error>;3]{
    let mut rows=[[K::ZERO;29];3];
    let p:usize=kani::any();let i:usize=kani::any();kani::assume(p<3&&i<29);
    let raw:[u8;16]=kani::any();rows[p][i]=K::from_le_bytes(&raw).unwrap_or(K::ZERO);
    [Ok(rows[0]),Ok(rows[1]),Ok(rows[2])]
}
#[kani::proof] #[kani::unwind(40)]
fn XRg_claims_store(){let r=rows();let got=XRg_claims_storage(r).unwrap();let expected=XRg_claims_reference(r).unwrap();let p:usize=kani::any();let i:usize=kani::any();kani::assume(p<3&&i<29);assert_eq!(got[p][i],expected[p][i]);}
#[kani::proof] #[kani::unwind(40)]
fn XRg_dot_no_wrap(){let sum:u64=kani::any();let raw:u64=kani::any();kani::assume(sum<4095u64*(1u64<<34));let folded=(raw&2147483647).wrapping_add(raw>>31);kani::assume(folded<(1u64<<34));let mut dot=XRg_Dot{sums:[sum;4]};dot.push_raw([raw;4]);assert_eq!(dot.sums[0],sum+folded);assert!(dot.sums[0]<(1u64<<46));}
#[kani::proof] #[kani::unwind(40)]
fn XRg_claims_later_error(){let mut r=rows();let p:usize=kani::any();kani::assume(p==1||p==2);r[p]=Err(Error::NonCanonical{row:25,value:29*p});assert_eq!(XRg_claims_storage(r),XRg_claims_reference(r));}
