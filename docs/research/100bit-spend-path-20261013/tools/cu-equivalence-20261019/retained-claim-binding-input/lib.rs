extern crate self as aspis_core;
pub mod field;
use field::WideExact as E;
#[derive(Debug,Clone,Copy,PartialEq,Eq)]
pub enum Error { Parse,Semantic,Transcript,Relation,Merkle,Query,Checkpoint,Allocation }
pub fn powers<const N:usize>(_:E)->[E;N]{unreachable!()}
pub fn claim_dot(_:usize,_:&[E;29])->Result<E,Error>{unreachable!()}
pub fn trace_value(_:u8,_:usize,_:E){}
pub fn claim_context(inactive:E,g:&[E;29],kappa:E)->Result<E,Error>{
let k=powers::<7>(kappa);let parts=claim_parts(inactive,g)?;Ok(claim_sum(&k,&parts))
}
pub fn claim_parts(inactive:E,g:&[E;29])->Result<[E;7],Error>{
        let mut parts=[E::ZERO;7];parts[0]=inactive;
        for point in 0..6 {
            parts[point+1]=crate::claim_dot(point,g)?;
        }
Ok(parts)
}
pub fn claim_sum(k:&[E;7],parts:&[E;7])->E{
        let mut claim=E::ZERO;
        for i in 0..7 {crate::trace_value(14,i,parts[i]);claim=claim.add(k[i].mul(parts[i]));}
        crate::trace_value(14,7,claim);
        claim

}
