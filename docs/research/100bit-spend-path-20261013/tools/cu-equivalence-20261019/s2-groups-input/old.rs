use crate::{Weights,transport::Variant,field::{QM31 as K,WideExact as E}};
pub fn field(bytes:&[u8],i:usize)->E { E::from_le_bytes(&bytes[i*32..(i+1)*32]).unwrap() }
pub fn grouped_inactive_pair(weights:&Weights,f:&[u8],low:&[E;16])->E {
    let mut group_masks=[0u16;64];
    let mut group_coefficients=[E::ZERO;64];
    let mut groups=0;
    for j in 0..f.len()/32 {
        let mut mask=0u16;
        for s in 0..16 {if weights.raw(0,16*j+s)==K::ONE {mask|=1<<s;}}
        let coefficient=field(f,j);
        let mut group=0;
        while group<groups && group_masks[group]!=mask {group+=1;}
        if group==groups {group_masks[group]=mask;groups+=1;}
        group_coefficients[group]=group_coefficients[group].add(coefficient);
    }
    let mut pair=E::ZERO;
    for group in 0..groups {
        let mask=group_masks[group];
        let mut weight=E::ZERO;
        for (s,&challenge) in low.iter().enumerate() {
            if mask&(1<<s)!=0 {weight=weight.add(challenge);}
        }
        pair=pair.add(group_coefficients[group].mul(weight));
    }
    pair
}
