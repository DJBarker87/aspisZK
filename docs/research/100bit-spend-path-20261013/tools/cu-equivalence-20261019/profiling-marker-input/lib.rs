pub enum Phase { Parsed,Semantic,SemanticPart(u8),Prepare,CheckpointRead,Merkle(usize),Query(usize),QueryPart(usize,u8),CheckpointWrite,Relation,Final }
pub type Observer=Option<fn(Phase)>;
pub fn mark(obs:Observer,p:Phase) { if let Some(f)=obs {f(p);} }
