use std::vec::Vec;
#[derive(Debug,Clone,Copy,PartialEq,Eq)]
pub enum GeometryInputsError { Parse,Semantic,Transcript,Relation,Merkle,Query,Checkpoint,Allocation,
    /// Host prover only (LOG D38.3): this attempt's challenges fail the public
    /// P_R1 check. Carries no challenge and no conjunct.
    #[cfg(feature="prover")] Rejected,
    /// Host prover only (D38.3): all N = 8 attempts were rejected; nothing is published.
    #[cfg(feature="prover")] AttemptsExhausted,
    /// Host prover only: the operating-system entropy source failed.
    #[cfg(feature="prover")] Entropy }
type Error=GeometryInputsError;
#[derive(Clone,Copy,PartialEq,Eq,Debug,Default)]
pub struct M31(pub u32);
pub fn query_values_entry(_query:u32)->Result<([M31;5],M31),Error> {unreachable!()}
pub fn geometry_inputs_indexed(queries:&[u32;22],start:usize,end:usize)->Result<(Vec<M31>,Vec<M31>),Error> {
        if start>end||end>queries.len(){return Err(Error::Query);}
        let mut line_z_values=Vec::with_capacity(end-start);
        let mut flat=Vec::with_capacity((end-start)*5);
        let mut i=start;
        while i<end {
            let (values,line_z)=query_values_entry(queries[i])?;
            flat.extend_from_slice(&values);
            line_z_values.push(line_z);
            i+=1;
        }
        Ok((flat,line_z_values))
}

pub fn option_context_anchor(v:Option<u8>)->Option<u8>{v}
