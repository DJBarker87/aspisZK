use crate::field::{WideExact as E,QM31};
use crate::new_pairing::EbyKDot;
use crate::Error;
pub fn claim_dot(g:&[E;29])->Result<E,Error>{
let mut dot=crate::new_pairing::EbyKDot::new();
            for l in 0..29 {
                let scalar=crate::claim_scalar(l);
                dot.push(g[l],scalar).map_err(|_|Error::Parse)?;
            }
Ok(dot.finish())
}
pub fn tail(q:&[u8],g:&[E;29],slot:usize)->E {
let mut tail=EbyKDot::new();
        tail.push(g[28],QM31::from_le_bytes(&q[slot*120+104..slot*120+120]).unwrap()).unwrap();
        for term in 0..2 {
            let offset = 480 + slot * 32 + term * 16;
            tail.push(g[term+26],QM31::from_le_bytes(&q[offset..offset+16]).unwrap()).unwrap();
        }
tail.finish()
}
