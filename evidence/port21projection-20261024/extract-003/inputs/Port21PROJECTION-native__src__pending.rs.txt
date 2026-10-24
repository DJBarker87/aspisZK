struct BatchedWeights { raw:Vec<[u64;4]>, terms:usize }
impl BatchedWeights {
    fn new(weights:&[K])->Result<Self,Error> {
        let mut raw=aspis_core::r0::heap::filled(weights.len(),[0u64;4]).map_err(|_|Error::Allocation)?;
        let mut index=0;
        while index<weights.len() {
            let w=weights[index];
            raw[index]=[w.c0.a.0 as u64,w.c0.b.0 as u64,w.c1.a.0 as u64,w.c1.b.0 as u64];
            index+=1;
        }
        Ok(Self{raw,terms:0})
    }
}
