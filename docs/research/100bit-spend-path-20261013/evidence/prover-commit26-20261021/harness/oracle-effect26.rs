use std::cell::RefCell;
use std::collections::BTreeMap;
type Table=BTreeMap<Vec<u8>,[u8;32]>;
trait Digest32:Copy {fn digest(&self,parts:&[&[u8]])->[u8;32];}
fn concat(parts:&[&[u8]])->Vec<u8> {
    let mut a=Vec::with_capacity(parts.iter().map(|p|p.len()).sum());
    for p in parts {a.extend_from_slice(p);}
    a
}

struct CoinState { coins:Vec<[u8;32]>, next:usize, record:Option<Table>, collision:bool }
#[derive(Clone,Copy)]
struct CoinOracle<'a>(&'a RefCell<CoinState>);
impl Digest32 for CoinOracle<'_> {
    fn digest(&self,parts:&[&[u8]])->[u8;32] {
        let mut s=self.0.borrow_mut();
        let answer=*s.coins.get(s.next).unwrap_or(&[0;32]);
        s.next+=1;
        if let Some(t)=s.record.as_mut() {
            if let Some(prev)=t.insert(concat(parts),answer) { if prev!=answer {s.collision=true;} }
        }
        answer
    }
}

#[test]
fn same_input_two_answers() {
 let state=RefCell::new(CoinState{coins:vec![[0;32],[1;32]],next:0,record:None,collision:false});
 let oracle=CoinOracle(&state);
 let parts:&[&[u8]]=&[b"same-input"];
 let first=oracle.digest(parts);
 let second=oracle.digest(parts);
 assert_eq!(first,[0;32]);assert_eq!(second,[1;32]);assert_ne!(first,second);
 assert_eq!(state.borrow().next,2);
}
