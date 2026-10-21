//! Owned explicit-state oracle interface. The recording callback is the
//! named D133 map contract, not a source/model execution-equality premise.
pub trait Recording {
    fn insert(self, parts: &[&[u8]], answer: [u8;32]) -> (Option<[u8;32]>,Self);
}
pub struct CoinState<R> {
    pub coins: Vec<[u8;32]>,
    pub next: usize,
    pub record: Option<R>,
    pub collision: bool,
}
pub trait EffectDigest32<S> {
    fn digest(state:S, parts:&[&[u8]]) -> ([u8;32],S);
}
pub struct CoinOracle;
fn different(a:[u8;32], b:[u8;32])->bool {
    let mut i=0;
    while i<32 {if a[i]!=b[i] {return true;}i+=1;}
    false
}
impl<R:Recording> EffectDigest32<CoinState<R>> for CoinOracle {
    fn digest(mut state:CoinState<R>, parts:&[&[u8]]) -> ([u8;32],CoinState<R>) {
        let answer=if state.next<state.coins.len() {state.coins[state.next]} else {[0;32]};
        state.next+=1;
        if let Some(table)=state.record.take() {
            let (previous,table)=table.insert(parts,answer);
            state.record=Some(table);
            if let Some(old)=previous {if different(old,answer) {state.collision=true;}}
        }
        (answer,state)
    }
}
