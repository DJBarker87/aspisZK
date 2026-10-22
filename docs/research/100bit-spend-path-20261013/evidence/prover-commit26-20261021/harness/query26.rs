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

#[kani::proof]
#[kani::unwind(10)]
fn array_iterator_order() {
 let words:[u32;8]=kani::any();let mut it=words.into_iter();
 for i in 0..8 {assert_eq!(it.next(),Some(words[i]));}
 assert_eq!(it.next(),None);
}
#[kani::proof]
#[kani::unwind(24)]
fn prefix_contains() {
 let a:[u32;22]=kani::any();let len:usize=kani::any();let c:u32=kani::any();
 kani::assume(len<=22);
 let left=a[..len].contains(&c);
 let mut right=false;let mut i=0;
 while i<len {if a[i]==c {right=true;break;}i+=1;}
 assert_eq!(left,right);
}

// Length-specialised membership gates, with every length 0..22 covered.
#[kani::proof]
#[kani::unwind(24)]
fn contains_len_0() {
 let a:[u32;22]=kani::any();let c:u32=kani::any();
 let left=a[..0].contains(&c);
 let mut right=false;let mut i=0;
 while i<0 {if a[i]==c {right=true;break;}i+=1;}
 assert_eq!(left,right);
}
#[kani::proof]
#[kani::unwind(24)]
fn contains_len_1() {
 let a:[u32;22]=kani::any();let c:u32=kani::any();
 let left=a[..1].contains(&c);
 let mut right=false;let mut i=0;
 while i<1 {if a[i]==c {right=true;break;}i+=1;}
 assert_eq!(left,right);
}
#[kani::proof]
#[kani::unwind(24)]
fn contains_len_2() {
 let a:[u32;22]=kani::any();let c:u32=kani::any();
 let left=a[..2].contains(&c);
 let mut right=false;let mut i=0;
 while i<2 {if a[i]==c {right=true;break;}i+=1;}
 assert_eq!(left,right);
}
#[kani::proof]
#[kani::unwind(24)]
fn contains_len_3() {
 let a:[u32;22]=kani::any();let c:u32=kani::any();
 let left=a[..3].contains(&c);
 let mut right=false;let mut i=0;
 while i<3 {if a[i]==c {right=true;break;}i+=1;}
 assert_eq!(left,right);
}
#[kani::proof]
#[kani::unwind(24)]
fn contains_len_4() {
 let a:[u32;22]=kani::any();let c:u32=kani::any();
 let left=a[..4].contains(&c);
 let mut right=false;let mut i=0;
 while i<4 {if a[i]==c {right=true;break;}i+=1;}
 assert_eq!(left,right);
}
#[kani::proof]
#[kani::unwind(24)]
fn contains_len_5() {
 let a:[u32;22]=kani::any();let c:u32=kani::any();
 let left=a[..5].contains(&c);
 let mut right=false;let mut i=0;
 while i<5 {if a[i]==c {right=true;break;}i+=1;}
 assert_eq!(left,right);
}
#[kani::proof]
#[kani::unwind(24)]
fn contains_len_6() {
 let a:[u32;22]=kani::any();let c:u32=kani::any();
 let left=a[..6].contains(&c);
 let mut right=false;let mut i=0;
 while i<6 {if a[i]==c {right=true;break;}i+=1;}
 assert_eq!(left,right);
}
#[kani::proof]
#[kani::unwind(24)]
fn contains_len_7() {
 let a:[u32;22]=kani::any();let c:u32=kani::any();
 let left=a[..7].contains(&c);
 let mut right=false;let mut i=0;
 while i<7 {if a[i]==c {right=true;break;}i+=1;}
 assert_eq!(left,right);
}
#[kani::proof]
#[kani::unwind(24)]
fn contains_len_8() {
 let a:[u32;22]=kani::any();let c:u32=kani::any();
 let left=a[..8].contains(&c);
 let mut right=false;let mut i=0;
 while i<8 {if a[i]==c {right=true;break;}i+=1;}
 assert_eq!(left,right);
}
#[kani::proof]
#[kani::unwind(24)]
fn contains_len_9() {
 let a:[u32;22]=kani::any();let c:u32=kani::any();
 let left=a[..9].contains(&c);
 let mut right=false;let mut i=0;
 while i<9 {if a[i]==c {right=true;break;}i+=1;}
 assert_eq!(left,right);
}
#[kani::proof]
#[kani::unwind(24)]
fn contains_len_10() {
 let a:[u32;22]=kani::any();let c:u32=kani::any();
 let left=a[..10].contains(&c);
 let mut right=false;let mut i=0;
 while i<10 {if a[i]==c {right=true;break;}i+=1;}
 assert_eq!(left,right);
}
#[kani::proof]
#[kani::unwind(24)]
fn contains_len_11() {
 let a:[u32;22]=kani::any();let c:u32=kani::any();
 let left=a[..11].contains(&c);
 let mut right=false;let mut i=0;
 while i<11 {if a[i]==c {right=true;break;}i+=1;}
 assert_eq!(left,right);
}
#[kani::proof]
#[kani::unwind(24)]
fn contains_len_12() {
 let a:[u32;22]=kani::any();let c:u32=kani::any();
 let left=a[..12].contains(&c);
 let mut right=false;let mut i=0;
 while i<12 {if a[i]==c {right=true;break;}i+=1;}
 assert_eq!(left,right);
}
#[kani::proof]
#[kani::unwind(24)]
fn contains_len_13() {
 let a:[u32;22]=kani::any();let c:u32=kani::any();
 let left=a[..13].contains(&c);
 let mut right=false;let mut i=0;
 while i<13 {if a[i]==c {right=true;break;}i+=1;}
 assert_eq!(left,right);
}
#[kani::proof]
#[kani::unwind(24)]
fn contains_len_14() {
 let a:[u32;22]=kani::any();let c:u32=kani::any();
 let left=a[..14].contains(&c);
 let mut right=false;let mut i=0;
 while i<14 {if a[i]==c {right=true;break;}i+=1;}
 assert_eq!(left,right);
}
#[kani::proof]
#[kani::unwind(24)]
fn contains_len_15() {
 let a:[u32;22]=kani::any();let c:u32=kani::any();
 let left=a[..15].contains(&c);
 let mut right=false;let mut i=0;
 while i<15 {if a[i]==c {right=true;break;}i+=1;}
 assert_eq!(left,right);
}
#[kani::proof]
#[kani::unwind(24)]
fn contains_len_16() {
 let a:[u32;22]=kani::any();let c:u32=kani::any();
 let left=a[..16].contains(&c);
 let mut right=false;let mut i=0;
 while i<16 {if a[i]==c {right=true;break;}i+=1;}
 assert_eq!(left,right);
}
#[kani::proof]
#[kani::unwind(24)]
fn contains_len_17() {
 let a:[u32;22]=kani::any();let c:u32=kani::any();
 let left=a[..17].contains(&c);
 let mut right=false;let mut i=0;
 while i<17 {if a[i]==c {right=true;break;}i+=1;}
 assert_eq!(left,right);
}
#[kani::proof]
#[kani::unwind(24)]
fn contains_len_18() {
 let a:[u32;22]=kani::any();let c:u32=kani::any();
 let left=a[..18].contains(&c);
 let mut right=false;let mut i=0;
 while i<18 {if a[i]==c {right=true;break;}i+=1;}
 assert_eq!(left,right);
}
#[kani::proof]
#[kani::unwind(24)]
fn contains_len_19() {
 let a:[u32;22]=kani::any();let c:u32=kani::any();
 let left=a[..19].contains(&c);
 let mut right=false;let mut i=0;
 while i<19 {if a[i]==c {right=true;break;}i+=1;}
 assert_eq!(left,right);
}
#[kani::proof]
#[kani::unwind(24)]
fn contains_len_20() {
 let a:[u32;22]=kani::any();let c:u32=kani::any();
 let left=a[..20].contains(&c);
 let mut right=false;let mut i=0;
 while i<20 {if a[i]==c {right=true;break;}i+=1;}
 assert_eq!(left,right);
}
#[kani::proof]
#[kani::unwind(24)]
fn contains_len_21() {
 let a:[u32;22]=kani::any();let c:u32=kani::any();
 let left=a[..21].contains(&c);
 let mut right=false;let mut i=0;
 while i<21 {if a[i]==c {right=true;break;}i+=1;}
 assert_eq!(left,right);
}
#[kani::proof]
#[kani::unwind(24)]
fn contains_len_22() {
 let a:[u32;22]=kani::any();let c:u32=kani::any();
 let left=a[..22].contains(&c);
 let mut right=false;let mut i=0;
 while i<22 {if a[i]==c {right=true;break;}i+=1;}
 assert_eq!(left,right);
}

#[kani::proof]
#[kani::unwind(10)]
fn decoder_order() {
 let block:[u8;32]=kani::any();let words=query_words(&block);
 let mut expected=[0u32;8];let mut i=0;
 while i<8 {let k=4*i;expected[i]=u32::from_le_bytes([
  block[k],block[k+1],block[k+2],block[k+3]]) & 262143;i+=1;}
 for i in 0..8 {assert_eq!(words[i],expected[i]);}
}
#[derive(Clone,Copy)]
struct Control {stops:[bool;8],calls:usize,seen:[[u8;32];8]}
impl Control {
 fn scan(&mut self,block:&[u8;32])->bool {
  self.seen[self.calls]=*block;let stop=self.stops[self.calls];self.calls+=1;stop
 }
}
fn loop_control(mut scan:Control,blocks:&[[u8;32];8],advances:&[[u8;32];8])
 ->(Control,[u8;32]) {
 let mut state=advances[7];
 for k in 0..8 {if scan.scan(&blocks[k]) {state=advances[k];break;}}
 (scan,state)
}
fn unrolled_control(mut scan:Control,blocks:&[[u8;32];8],advances:&[[u8;32];8])
 ->(Control,[u8;32]) {
 if scan.scan(&blocks[0]) {return (scan,advances[0]);}
 if scan.scan(&blocks[1]) {return (scan,advances[1]);}
 if scan.scan(&blocks[2]) {return (scan,advances[2]);}
 if scan.scan(&blocks[3]) {return (scan,advances[3]);}
 if scan.scan(&blocks[4]) {return (scan,advances[4]);}
 if scan.scan(&blocks[5]) {return (scan,advances[5]);}
 if scan.scan(&blocks[6]) {return (scan,advances[6]);}
 let _=scan.scan(&blocks[7]);(scan,advances[7])
}
#[kani::proof]
#[kani::unwind(34)]
fn driver_first_stop() {
 let blocks:[[u8;32];8]=kani::any();let advances:[[u8;32];8]=kani::any();
 let control=Control{stops:kani::any(),calls:0,seen:[[0;32];8]};
 let (a,sa)=loop_control(control,&blocks,&advances);
 let (b,sb)=unrolled_control(control,&blocks,&advances);
 assert_eq!(a.calls,b.calls);
 for j in 0..32 {assert_eq!(sa[j],sb[j]);}
 for i in 0..8 {for j in 0..32 {assert_eq!(a.seen[i][j],b.seen[i][j]);}}
}
