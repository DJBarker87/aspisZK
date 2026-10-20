use crate::{weights::field,field::{WideExact as E,QM31 as K},verifier::Error};
pub fn field_stream(f:&[u8],scratch:&[K],n:usize)->Result<E,Error> {
                let mut pair=crate::old_pairing::EbyKDot::new();
                for j in 0..n {pair.push(field(f,j),scratch[j]).map_err(|_|Error::Parse)?;}
    Ok(pair.finish())
}
