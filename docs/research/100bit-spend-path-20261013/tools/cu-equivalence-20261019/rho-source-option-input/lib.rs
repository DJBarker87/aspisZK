pub struct BatchedWeights { pub raw: Vec<[u64;4]>, pub terms: usize }
pub fn source_reborrow<'a,'b>(value:&'a mut Option<&'b mut BatchedWeights>)->Option<&'a mut BatchedWeights> {value.as_deref_mut()}
