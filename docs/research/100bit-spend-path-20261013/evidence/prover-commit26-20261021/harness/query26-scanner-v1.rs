const QUERY_COUNT: usize=22;
const QUERY_BOUND: u32=1<<18;
const QUERY_MAX_DRAWS: usize=64;
fn block_rank(block: &[u8;32])->[u32;8] {
    core::array::from_fn(|i| {
        let j=4*i;
        u32::from_le_bytes([block[j],block[j+1],block[j+2],block[j+3]])
    })
}
fn query_words(block: &[u8;32])->[u32;8] {
    block_rank(block).map(|word|word & (QUERY_BOUND-1))
}
#[derive(Clone,Copy)]
struct QueryScan {accepted:[u32;22],accepted_len:usize,draws:usize}
impl QueryScan {
    fn scan(&mut self, block: &[u8; 32]) -> bool {
        for candidate in query_words(block) {
            if self.accepted_len == QUERY_COUNT || self.draws == QUERY_MAX_DRAWS {
                return true;
            }
            self.draws += 1;
            if !self.accepted[..self.accepted_len].contains(&candidate) {
                self.accepted[self.accepted_len] = candidate;
                self.accepted_len += 1;
            }
        }
        false
    }

    fn indexed(&mut self,block: &[u8;32])->bool {
        let words=query_words(block);let mut i=0;
        while i<8 {
            let candidate=words[i];
            if self.accepted_len==QUERY_COUNT || self.draws==QUERY_MAX_DRAWS {return true;}
            self.draws+=1;
            if !self.accepted[..self.accepted_len].contains(&candidate) {
                self.accepted[self.accepted_len]=candidate;self.accepted_len+=1;
            }
            i+=1;
        }
        false
    }
}
#[kani::proof]
#[kani::unwind(24)]
fn scanner_iterator_equals_indexed() {
    let accepted:[u32;22]=kani::any();let len:usize=kani::any();let draws:usize=kani::any();
    kani::assume(len<=22 && draws<=64);
    let mut a=QueryScan{accepted,accepted_len:len,draws};let mut b=a;
    let block:[u8;32]=kani::any();
    assert_eq!(a.scan(&block),b.indexed(&block));
    assert_eq!(a.accepted_len,b.accepted_len);assert_eq!(a.draws,b.draws);
    for i in 0..22 {assert_eq!(a.accepted[i],b.accepted[i]);}
}
