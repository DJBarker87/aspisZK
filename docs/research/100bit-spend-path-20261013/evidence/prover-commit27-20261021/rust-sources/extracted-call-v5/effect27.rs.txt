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
fn different0(a:[u8;32],b:[u8;32])->bool {
    a[0]!=b[0] ||
    a[1]!=b[1] ||
    a[2]!=b[2] ||
    a[3]!=b[3] ||
    a[4]!=b[4] ||
    a[5]!=b[5] ||
    a[6]!=b[6] ||
    a[7]!=b[7]
}
fn different8(a:[u8;32],b:[u8;32])->bool {
    a[8]!=b[8] ||
    a[9]!=b[9] ||
    a[10]!=b[10] ||
    a[11]!=b[11] ||
    a[12]!=b[12] ||
    a[13]!=b[13] ||
    a[14]!=b[14] ||
    a[15]!=b[15]
}
fn different16(a:[u8;32],b:[u8;32])->bool {
    a[16]!=b[16] ||
    a[17]!=b[17] ||
    a[18]!=b[18] ||
    a[19]!=b[19] ||
    a[20]!=b[20] ||
    a[21]!=b[21] ||
    a[22]!=b[22] ||
    a[23]!=b[23]
}
fn different24(a:[u8;32],b:[u8;32])->bool {
    a[24]!=b[24] ||
    a[25]!=b[25] ||
    a[26]!=b[26] ||
    a[27]!=b[27] ||
    a[28]!=b[28] ||
    a[29]!=b[29] ||
    a[30]!=b[30] ||
    a[31]!=b[31]
}
#[cfg_attr(kani,kani::ensures(|out: &bool| *out == (a != b)))]
pub fn different(a:[u8;32],b:[u8;32])->bool {different0(a,b)||different8(a,b)||different16(a,b)||different24(a,b)}
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
