//! Owned safe references, included only by cfg(kani) modules.
use aspis_core::field::{QM31,CM31,M31,WideExact,P};
pub fn equal(a:QM31,b:QM31)->bool {
    a.c0.a.0==b.c0.a.0 && a.c0.b.0==b.c0.b.0 && a.c1.a.0==b.c1.a.0 && a.c1.b.0==b.c1.b.0
}
pub fn all_slots_clear(values:&[[[QM31;2];2]],masks:&[u16;64],chi:QM31)->bool {
    let mut clear=true;let mut row=0;
    while row<values.len() {
        let active=masks[row>>4] & (1u16<<(row&15)) !=0;
        clear=clear & !(active & equal(chi,values[row][0][0]));
        clear=clear & !(active & equal(chi,values[row][0][1]));
        clear=clear & !(active & equal(chi,values[row][1][0]));
        clear=clear & !(active & equal(chi,values[row][1][1]));
        row+=1;
    }
    clear
}
pub fn gamma(block:[u8;32])->WideExact {
    let mut quotient=[0u32;8];let mut i=0;
    while i<8 {
        quotient[i]=u32::from_le_bytes([block[4*i],block[4*i+1],block[4*i+2],block[4*i+3]]);
        i+=1;
    }
    let mut digits=[0u32;8];i=0;
    while i<8 {
        let mut r=0u64;let mut j=8;
        while j>0 {
            j-=1;
            let n=(r<<32)|u64::from(quotient[j]);
            quotient[j]=(n/u64::from(P)) as u32;r=n%u64::from(P);
        }
        digits[i]=r as u32;i+=1;
    }
    let mut add=quotient[0]+1;i=0;
    while i<8 {
        let n=u64::from(digits[i])+u64::from(add);
        digits[i]=(n%u64::from(P)) as u32;add=(n/u64::from(P)) as u32;i+=1;
    }
    if add!=0 {
        add=1;i=0;
        while i<8 {
            let n=u64::from(digits[i])+u64::from(add);
            digits[i]=(n%u64::from(P)) as u32;add=(n/u64::from(P)) as u32;i+=1;
        }
    }
    WideExact::new(QM31{c0:CM31{a:M31(digits[0]),b:M31(digits[1])},c1:CM31{a:M31(digits[2]),b:M31(digits[3])}},
        QM31{c0:CM31{a:M31(digits[4]),b:M31(digits[5])},c1:CM31{a:M31(digits[6]),b:M31(digits[7])}})
}
