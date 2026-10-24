use aspis_core::field::{QM31,CM31,M31,P};
fn reference_statement_points(z: &[QM31; 10]) -> [[QM31; 10]; 3] {
    let mut successor = *z;
    let mut carry = QM31::ONE;
    for coordinate in (0..z.len()).rev() {
        let bit = z[coordinate];
        let bit_and_carry = bit.mul(carry);
        successor[coordinate] = bit.add(carry).sub(bit_and_carry.add(bit_and_carry));
        carry = bit_and_carry;
    }
    let mut absorption = *z;
    for coordinate in [7usize, 6] {
        absorption[coordinate] = QM31::ONE.sub(absorption[coordinate]);
    }
    [*z, successor, absorption]
}
fn next(s:&mut u64)->u32 { *s=s.wrapping_mul(6364136223846793005).wrapping_add(1); (*s%u64::from(P)) as u32 }
#[test]
fn explicit_complements_match_retained_point_source() {
 let mut seed=0x8f11_64a2_1309_23cdu64;
 for case in 0..512 {
  let alpha:[QM31;10]=core::array::from_fn(|_| match case {
   0=>QM31::ZERO,1=>QM31::ONE,
   2=>QM31{c0:CM31{a:M31(P-1),b:M31(P-1)},c1:CM31{a:M31(P-1),b:M31(P-1)}},
   _=>QM31{c0:CM31{a:M31(next(&mut seed)),b:M31(next(&mut seed))},c1:CM31{a:M31(next(&mut seed)),b:M31(next(&mut seed))}},
  });
  let actual=aspis_core::state_only_prefix::r0::statement_points(&alpha);
  assert_eq!(actual,reference_statement_points(&alpha),"source point case {case}");
  assert_eq!(actual[0],alpha);
  for i in 0..10 {assert_eq!(actual[2][i],if i==6||i==7 {QM31::ONE.sub(alpha[i])} else {alpha[i]});}
 }
}
