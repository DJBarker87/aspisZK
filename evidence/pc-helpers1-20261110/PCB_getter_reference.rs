pub type Digest=[u32;8];
pub struct Tree {pub next_leaf_index:u64,pub root:Digest,pub frontier:[Digest;32]}
pub struct Validated<'a> {pub inner:Tree,pub empty:&'a [Digest;33]}
impl<'a> Validated<'a> {pub fn as_tree(&self)->&Tree {&self.inner}}
pub fn tree_ref<'loan,'table>(x:&'loan Validated<'table>)->&'loan Tree {x.as_tree()}
pub fn deref_ref<'loan,'table>(x:&'loan Validated<'table>)->&'loan Tree {x.as_tree()}
pub struct Plan<P> {pub preparation:P,pub seed:[u8;32],pub encoded_marker:[u8;208]}
pub fn seed_ref<P>(x:&Plan<P>)->&[u8;32] {&x.seed}
pub struct Auth<T> {pub value:Box<T>,pub exact_bytes:Box<[u8]>}
pub fn value_ref<T>(x:&Auth<T>)->&T {&x.value}
pub struct Canonical<P,S> {pub program_id:P,pub pool:P,pub state:Box<S>}
pub fn state_ref<P,S>(x:&Canonical<P,S>)->&S {&x.state}
