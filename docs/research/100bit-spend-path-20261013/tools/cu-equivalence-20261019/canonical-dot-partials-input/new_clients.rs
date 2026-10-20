use crate::{weights::field,field::{WideExact as E,QM31 as K},verifier::Error};
pub fn shared_partials(f:&[u8],common:&[K;16])->Result<[E;4],Error> {
            let mut partials=[E::ZERO;4];
            for s in 0..4 {
                partials[s]=shared_row(f,common,s)?;
            }
    Ok(partials)
}
pub fn shared_high(partials:&[E;4],scalars:&[K;4])->Result<E,Error> {
                let mut high=crate::new_pairing::EbyKDot::new();
                for s in 0..4 {
                    high.push(partials[s],scalars[s]).map_err(|_|Error::Parse)?;
                }
    Ok(high.finish())
}
pub fn final_stream(f:&[u8],weights:&[K])->Result<E,Error> {
    let mut dot=crate::new_pairing::EbyKDot::new();
    for (j,w) in weights.iter().enumerate() {dot.push(field(f,j),*w).map_err(|_|Error::Parse)?;}
    Ok(dot.finish())
}

pub fn shared_row(f:&[u8],common:&[K;16],s:usize)->Result<E,Error> {
                let mut dot=crate::new_pairing::EbyKDot::new();
                for j in 0..16 {
                    dot.push(field(f,16*s+j),common[j]).map_err(|_|Error::Parse)?;
                }
    Ok(dot.finish())
}
