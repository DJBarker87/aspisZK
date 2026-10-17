/// C1 can be constructed before λ/χ; C2 separately after them. The 29-entry
/// input permits virtual lanes but only this time's lanes are committed.
pub struct Commitment {
    time: CommitmentTime,
    lanes: Vec<usize>,
    messages: Vec<Message<E>>,
    words: Vec<Word>,
    tree: Tree,
    private_salts: Option<PrivateSalts>,
}