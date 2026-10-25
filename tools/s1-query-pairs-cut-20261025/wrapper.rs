
// Proof-only scan script. Native QueryScan representation and driver unchanged.
#[cfg(kani)]pub type S126Reply=([u32;22],usize,usize,bool);
#[cfg(kani)]static mut S126_TAPE:[S126Reply;8]=[([0;22],0,0,false);8];
#[cfg(kani)]static mut S126_CALLS:usize=0;
#[cfg(kani)]static mut S126_REFS:usize=0;
#[cfg(kani)]static mut S126_OBS_CALL:usize=0;
#[cfg(kani)]static mut S126_OBS_WORD:usize=0;
#[cfg(kani)]static mut S126_OBS_BYTE:usize=0;
#[cfg(kani)]static mut S126_WORD:u32=0;
#[cfg(kani)]static mut S126_LEN:usize=0;
#[cfg(kani)]static mut S126_DRAWS:usize=0;
#[cfg(kani)]static mut S126_BYTE:u8=0;
#[cfg(kani)]pub fn s126_init(tape:[S126Reply;8],call:usize,word:usize,byte:usize){unsafe{
 S126_TAPE=tape;S126_CALLS=0;S126_REFS=0;S126_OBS_CALL=call;S126_OBS_WORD=word;S126_OBS_BYTE=byte;
 S126_WORD=0;S126_LEN=0;S126_DRAWS=0;S126_BYTE=0;
}}
#[cfg(kani)]pub fn s126_counts()->(usize,usize){unsafe{(S126_CALLS,S126_REFS)}}
#[cfg(kani)]pub fn s126_scan_reply(scan:&mut QueryScan,block:&[u8;32])->bool{unsafe{
 let index=S126_CALLS;assert!(index<8);
 if index==S126_OBS_CALL{
  S126_WORD=scan.accepted[S126_OBS_WORD];S126_LEN=scan.accepted_len;S126_DRAWS=scan.draws;S126_BYTE=block[S126_OBS_BYTE];
 }
 let (a,n,d,stop)=S126_TAPE[index];scan.accepted=a;scan.accepted_len=n;scan.draws=d;
 S126_CALLS+=1;stop
}}
#[cfg(kani)]pub fn s126_reference_scan_reply(a:[u32;22],n:usize,d:usize,block:&[u8;32])->S126Reply{unsafe{
 let index=S126_REFS;assert!(index<S126_CALLS);
 if index==S126_OBS_CALL{
  assert!(a[S126_OBS_WORD]==S126_WORD);assert!(n==S126_LEN);assert!(d==S126_DRAWS);assert!(block[S126_OBS_BYTE]==S126_BYTE);
 }
 S126_REFS+=1;S126_TAPE[index]
}}
