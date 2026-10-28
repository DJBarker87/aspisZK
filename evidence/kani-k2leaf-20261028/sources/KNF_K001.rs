#![allow(dead_code, non_snake_case)]
#[path="KNF_field.rs"] mod KNF_field;
use KNF_field::WideExact as E;

// All calls are monomorphized; no observer, function-pointer value or ghost global.
fn KNF_any_e() -> E {
    let w:[u32;8]=kani::any();
    for v in w { kani::assume(v<0x7fff_ffff); }
    E::from_limbs(w).unwrap()
}
fn KNF_array() -> [E;7] {
    let mut a=[E::ZERO;7];
    for i in 0..7 { a[i]=KNF_any_e(); }
    a
}
fn KNF_expect(actual:u32, expected:u32) {
    assert_eq!(actual, expected ^ KNF_XOR);
}
const KNF_XOR:u32=0;

#[kani::proof] #[kani::unwind(66)]
fn parts_store() {
    let mut parts=KNF_array(); let before=parts; let value=KNF_any_e();
    let point:usize=kani::any();kani::assume(point<6);
    parts[point+1]=value;
    let row:usize=kani::any();kani::assume(row<7);
    let limb:usize=kani::any();kani::assume(limb<8);
    KNF_expect(parts[row].to_limbs()[limb],if row==point+1 {value.to_limbs()[limb]} else {before[row].to_limbs()[limb]});
}
#[kani::proof] #[kani::unwind(66)]
fn powers_final_iteration() {
    let p=KNF_any_e();let mut out=KNF_array();let before=out;
    let mut i=6usize;out[i]=p;i+=1;
    assert_eq!(i,7);
    let j:usize=kani::any();kani::assume(j<7);
    let limb:usize=kani::any();kani::assume(limb<8);
    KNF_expect(out[j].to_limbs()[limb],if j==6 {p.to_limbs()[limb]} else {before[j].to_limbs()[limb]});
}
#[kani::proof] #[kani::unwind(66)]
fn powers_continue_prefix() {
    let x=KNF_any_e();let p=KNF_any_e();let mut out=KNF_array();let before=out;
    let at:usize=kani::any();kani::assume(at<6);let mut i=at;
    out[i]=p;i+=1;
    assert_eq!(i,at+1);assert!(i!=7);
    let j:usize=kani::any();kani::assume(j<7);
    let limb:usize=kani::any();kani::assume(limb<8);
    KNF_expect(out[j].to_limbs()[limb],if j==at {p.to_limbs()[limb]} else {before[j].to_limbs()[limb]});
    let operands=(p,x);
    assert_eq!(operands.0.to_limbs()[limb],p.to_limbs()[limb]);
    assert_eq!(operands.1.to_limbs()[limb],x.to_limbs()[limb]);
}
#[inline(never)]
fn KNF_word(b:&[u8;32],i:usize)->u32 {
    u32::from_le_bytes(b[4*i..4*i+4].try_into().unwrap())
}
#[kani::proof] #[kani::unwind(10)]
fn LPo_decode_words() {
    let b:[u8;32]=kani::any();
    let w:[u32;8]=core::array::from_fn(|i|KNF_word(&b,i));
    let actual=E::from_le_bytes(&b);
    let mut valid=true;
    for i in 0..8 {valid=valid && w[i]<2147483647;}
    match actual {
        None=>assert!(!valid),
        Some(e)=>{assert!(valid);let i:usize=kani::any();kani::assume(i<8);KNF_expect(e.to_limbs()[i],w[i]);}
    }
}
#[kani::proof] #[kani::unwind(10)]
fn LPk_byte_decode() {
    let block:[u8;32]=kani::any();
    let quotient:[u32;8]=core::array::from_fn(|i|KNF_word(&block,i));
    let i:usize=kani::any();kani::assume(i<8);
    let word=u32::from(block[4*i])|(u32::from(block[4*i+1])<<8)|
        (u32::from(block[4*i+2])<<16)|(u32::from(block[4*i+3])<<24);
    KNF_expect(quotient[i],word);
}
#[inline(never)]
fn KNF_transition(quotient:&mut [u32;8],next:[u32;8],digit:u32)->u32 {
    *quotient=next;digit
}
#[kani::proof] #[kani::unwind(10)]
fn LPk_from_fn_order_word() {
    let mut quotient:[u32;8]=kani::any();let initial=quotient;
    let mut count=0usize;
    let mut inputs=[[0u32;8];8];let mut outputs=[[0u32;8];8];let mut digits=[0u32;8];
    let result:[u32;8]=core::array::from_fn(|i| {
        assert_eq!(i,count);inputs[i]=quotient;
        let next:[u32;8]=kani::any();let digit:u32=kani::any();
        let returned=KNF_transition(&mut quotient,next,digit);
        outputs[i]=next;digits[i]=digit;count+=1;returned
    });
    assert_eq!(count,8);
    let at:usize=kani::any();kani::assume(at<8);
    KNF_expect(result[at],digits[at]);
    let word:usize=kani::any();kani::assume(word<8);
    assert_eq!(inputs[0][word],initial[word]);
    if at>0 {assert_eq!(inputs[at][word],outputs[at-1][word]);}
    assert_eq!(quotient[word],outputs[7][word]);
}
