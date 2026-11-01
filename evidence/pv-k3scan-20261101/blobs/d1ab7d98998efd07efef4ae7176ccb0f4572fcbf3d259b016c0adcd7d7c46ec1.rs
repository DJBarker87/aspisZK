//! Mersenne shape of a single long-division step.
use aspis_core::field::P;
#[kani::proof]
#[kani::unwind(4)]
fn division_word_closed_form() {
 let word:u32=kani::any();let prior:u32=kani::any();kani::assume(prior<P);
 let dividend=(u64::from(prior)<<32)|u64::from(word);
 let high=dividend>>31;let sum=high+(dividend&u64::from(P));
 let correction=if sum>=2*u64::from(P) {2} else if sum>=u64::from(P) {1} else {0};
 let quotient=high+correction;let remainder=sum-correction*u64::from(P);
 assert!(quotient<=u64::from(u32::MAX));assert!(remainder<u64::from(P));
 let actual=super::sampler_word_source::actual(word,u64::from(prior));
 assert_eq!(u64::from(actual.0),quotient);assert_eq!(actual.1,remainder);
 assert_eq!(u64::from(actual.0)*u64::from(P)+actual.1,dividend);
}

/// Arithmetic fact only. Connecting it to U64 division requires uniqueness.
#[kani::proof]
#[kani::unwind(4)]
fn word_closed_form_arithmetic() {
 let word:u32=kani::any();let prior:u32=kani::any();kani::assume(prior<P);
 let dividend=(u64::from(prior)<<32)|u64::from(word);
 let high=dividend>>31;let sum=high+(dividend&u64::from(P));
 let correction=if sum>=2*u64::from(P) {2} else if sum>=u64::from(P) {1} else {0};
 let quotient=high+correction;let remainder=sum-correction*u64::from(P);
 assert!(quotient<=u64::from(u32::MAX));assert!(remainder<u64::from(P));
 assert_eq!((quotient<<31)-quotient+remainder,dividend);
}
