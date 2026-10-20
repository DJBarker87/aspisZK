use crate::{Weights,transport::Variant,field::{QM31 as K,WideExact as E}};
const S2_INACTIVE_GROUPS:[u8;64]=[0,1,2,3,4,5,5,6,4,5,5,5,7,7,7,7,7,7,7,4,4,5,5,6,4,5,5,5,7,7,7,4,7,7,7,7,4,5,5,5,4,5,5,5,8,9,10,8,11,2,2,10,4,5,5,6,4,5,5,6,7,7,7,7];
const S2_INACTIVE_MASKS:[u16;12]=[32769,49217,49280,16448,32767,16383,49151,65535,49152,57344,49216,33024];
pub fn s2_grouped_inactive_pair(f:&[u8],low:&[E;16])->E {
    let mut coefficients=[E::ZERO;12];
    for j in 0..64 {
        let group=S2_INACTIVE_GROUPS[j] as usize;
        coefficients[group]=coefficients[group].add(field(f,j));
    }
    let mut pair=E::ZERO;
    for group in 0..12 {
        let mut weight=E::ZERO;
        for (bit,&challenge) in low.iter().enumerate() {
            if S2_INACTIVE_MASKS[group]&(1<<bit)!=0 {weight=weight.add(challenge);}
        }
        pair=pair.add(coefficients[group].mul(weight));
    }
    pair
}
pub fn field(bytes:&[u8],i:usize)->E { E::from_le_bytes(&bytes[i*32..(i+1)*32]).unwrap() }
pub fn grouped_inactive_pair(weights:&Weights,f:&[u8],low:&[E;16])->E {
    if weights.variant==Variant::S2 && f.len()==64*32 {return s2_grouped_inactive_pair(f,low);}
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
