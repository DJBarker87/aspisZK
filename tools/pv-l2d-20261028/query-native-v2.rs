#![allow(dead_code)]

const QUERY_COUNT:usize=22;const QUERY_MAX_DRAWS:usize=64;const QUERY_BOUND:u32=1<<18;

#[derive(Debug,PartialEq,Eq)]
pub enum QuerySampleError {
    /// Masking is exact only when the domain size is a nonzero power of two.
    BoundNotPowerOfTwo { bound: u32 },
    /// A without-replacement sample cannot contain more points than its domain.
    CountExceedsBound { count: usize, bound: u32 },
    /// The configured candidate-draw cap was reached before `count` distinct
    /// positions were accepted. This is an explicit completeness abort.
    DrawLimitExhausted { accepted: usize, max_draws: usize },
}

type Rank=[u32;8];

fn block_rank(block: &[u8; 32]) -> Rank {
    core::array::from_fn(|i| {
        let j = 4 * i;
        u32::from_le_bytes([block[j], block[j + 1], block[j + 2], block[j + 3]])
    })
}

fn query_words(block: &[u8; 32]) -> [u32; 8] {
    block_rank(block).map(|word| word & (QUERY_BOUND - 1))
}

#[derive(Default)]
struct QueryScan {
    accepted: [u32; QUERY_COUNT],
    accepted_len: usize,
    draws: usize,
}

impl QueryScan {
    /// Checks before each word, with no check after the last word. In
    /// particular, success on word 8 is detected in the next block.
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

    fn finish(self) -> Result<[u32; QUERY_COUNT], QuerySampleError> {
        if self.accepted_len == QUERY_COUNT {
            Ok(self.accepted)
        } else {
            Err(QuerySampleError::DrawLimitExhausted {
                accepted: self.accepted_len,
                max_draws: QUERY_MAX_DRAWS,
            })
        }
    }
}

pub fn queries_from_pairs(
    blocks: &[[u8; 32]; 8],
    advances: &[[u8; 32]; 8],
) -> Result<([u32; QUERY_COUNT], [u8; 32]), QuerySampleError> {
    let mut scan = QueryScan::default();
    let mut state = advances[7];
    for k in 0..8 {
        if scan.scan(&blocks[k]) {
            state = advances[k];
            break;
        }
    }
    Ok((scan.finish()?, state))
}

mod verifier {#[derive(Debug,PartialEq,Eq)] pub enum Error {Transcript}}

mod host {

pub fn queries_from_pairs(blocks:&[[u8;32];8],advances:&[[u8;32];8])->Result<([u32;22],[u8;32]),crate::verifier::Error> {
    scan_query_words(blocks,advances,[0;22],0,0)
}

fn scan_query_words(blocks:&[[u8;32];8],advances:&[[u8;32];8],mut accepted:[u32;22],n:usize,draws:usize)->Result<([u32;22],[u8;32]),crate::verifier::Error> {
    if draws==64 {
        return if n==22 {Ok((accepted,advances[7]))} else {Err(crate::verifier::Error::Transcript)};
    }
    let k=draws/8;
    if n==22 {return Ok((accepted,advances[k]));}
    let at=4*(draws%8);
    let candidate=u32::from_le_bytes([blocks[k][at],blocks[k][at+1],blocks[k][at+2],blocks[k][at+3]])&0x3ffff;
    if query_contains(&accepted,n,candidate) {
        scan_query_words(blocks,advances,accepted,n,draws+1)
    } else {
        accepted[n]=candidate;
        scan_query_words(blocks,advances,accepted,n+1,draws+1)
    }
}

fn query_contains(accepted:&[u32;22],n:usize,candidate:u32)->bool {
    let mut i=0;
    while i<n {if accepted[i]==candidate {return true;} i+=1;}
    false
}

}


fn reference(blocks:&[[u8;32];8],advances:&[[u8;32];8])->Result<([u32;22],[u8;32]),verifier::Error> {
 let mut accepted=Vec::new();let mut draws=0;
 while draws<64 && accepted.len()<22 {
  let k=draws/8;let j=4*(draws%8);
  let x=u32::from_le_bytes([blocks[k][j],blocks[k][j+1],blocks[k][j+2],blocks[k][j+3]])&0x3ffff;
  draws+=1;
  if !accepted.iter().any(|&v|v==x){accepted.push(x);}
 }
 if accepted.len()!=22 {return Err(verifier::Error::Transcript);}
 let selected=(draws/8).min(7);
 Ok((accepted.try_into().unwrap(),advances[selected]))
}
fn pack(words:&[u32;64])->[[u8;32];8] {
 std::array::from_fn(|k|std::array::from_fn(|j|words[k*8+j/4].to_le_bytes()[j%4]))
}
fn check(words:&[u32;64])->usize {
 let b=pack(words);let a=std::array::from_fn(|i|[i as u8;32]);
 let original=queries_from_pairs(&b,&a).map_err(|_|verifier::Error::Transcript);
 let rewritten=host::queries_from_pairs(&b,&a);let expected=reference(&b,&a);
 assert_eq!(original,expected);assert_eq!(rewritten,expected);1
}
fn main(){
 if std::env::args().any(|x|x=="negative") {
  let w=std::array::from_fn(|i|if i<3 {0}else{(i-2).min(21) as u32});let b=pack(&w);let a=std::array::from_fn(|i|[i as u8;32]);
  assert_eq!(host::queries_from_pairs(&b,&a).unwrap().1,[2;32],"false control: stop-at-draw24 selects advance3");return;
 }
 let mut checks=0;checks+=check(&[0;64]);checks+=check(&[u32::MAX;64]);
 for end in 22..=64 {
  let w=std::array::from_fn(|i|if i<end-21 {0}else{((i-(end-22)).min(21)) as u32});
  checks+=check(&w);
  let a=std::array::from_fn(|i|[i as u8;32]);
  assert_eq!(host::queries_from_pairs(&pack(&w),&a).unwrap().1,[(end/8).min(7) as u8;32]);
 }
 let mut state=0x1531_8765_1234_9abcu64;
 for case in 0..20000 {
  let mask=if case%3==0 {31}else{0x3ffff};
  let w=std::array::from_fn(|_|{state^=state<<13;state^=state>>7;state^=state<<17;(state as u32)&mask});
  checks+=check(&w);
 }
 let status=std::process::Command::new(std::env::current_exe().unwrap()).arg("negative").status().unwrap();assert_eq!(status.code(),Some(101));
 println!("{{\"complete_result_checks\":{},\"directed_stop_positions\":43,\"matched_negative_exit\":101,\"failed\":0}}",checks);
}

