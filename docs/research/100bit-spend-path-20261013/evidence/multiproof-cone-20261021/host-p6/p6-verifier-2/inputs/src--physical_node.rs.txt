//! Physical cursor rebase for the exact generated binary_group. No read32,
//! row or level stub is used. Only the independently checked hash observer is
//! stubbed by the harness; all byte positions and cursors remain symbolic.
use core::cell::Cell;
use super::{reference as r,adoption_node::{Hash,source}};
pub fn check(case:u8) {
 let physical:[u8;5504]=kani::any();let length:usize=kani::any();
 let s=r::Scratch{idx:kani::any(),val:kani::any(),n:kani::any(),at:kani::any()};
 let i:usize=kani::any();let w:usize=kani::any();let coordinate:usize=kani::any();
 let answer:[u8;32]=kani::any();
 kani::assume(s.n>0 && s.n<=16 && i<s.n && w<=i && s.at<=length && length<=5504 && coordinate<65);
 let paired=i+1<s.n && s.idx[i+1]==s.idx[i]^1;
 kani::assume(if case==0 {paired}else{!paired && (length-s.at>=32)==(case==1)});
 // This stronger ordering domain is NOT needed for rebase itself. Its source
 // construction/preservation is checked separately, so the adoption includes
 // every state in that domain without assuming it here.
 let calls=Cell::new(0);let event=Cell::new(0);
 let hash=Hash{answer,coordinate,calls:&calls,event:&event};
 let (success,after,ni,nw)=source(hash,s,&physical[..length],i,w);
 let count=calls.get();let byte=event.get();calls.set(0);event.set(0);
 let window_len=if length-s.at>=32 {32}else{length-s.at};
 let window=&physical[s.at..s.at+window_len];
 let (relative_ok,relative,ri,rw)=source(hash,r::Scratch{at:0,..s},window,i,w);
 assert_eq!(success,relative_ok);assert_eq!((ni,nw),(ri,rw));
 assert_eq!(after.at,s.at+relative.at);assert_eq!(after.n,relative.n);
 let j:usize=kani::any();let k:usize=kani::any();kani::assume(j<16 && k<32);
 assert_eq!(after.idx[j],relative.idx[j]);assert_eq!(after.val[j][k],relative.val[j][k]);
 assert_eq!(count,calls.get());assert_eq!(byte,event.get());
}
