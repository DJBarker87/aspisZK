// Exact deployed enum coverage; feature prover is disabled in deployed receipts.
impl kani::Arbitrary for Error {
 fn any()->Self {match kani::any::<u8>()%8 {0=>Error::Parse,1=>Error::Semantic,2=>Error::Transcript,3=>Error::Relation,4=>Error::Merkle,5=>Error::Query,6=>Error::Checkpoint,_=>Error::Allocation}}
}
impl kani::Arbitrary for Variant {
 fn any()->Self {match kani::any::<u8>()%3 {0=>Variant::S1,1=>Variant::S2,_=>Variant::D}}
}
