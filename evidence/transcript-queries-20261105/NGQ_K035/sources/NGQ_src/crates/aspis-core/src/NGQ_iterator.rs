#[kani::proof] #[kani::unwind(34)]
fn NGQ_range_next() {
 let start:usize=kani::any();kani::assume(start<=8);let mut iter=start..8;
 let out=iter.next();let expected=if start<8 {Some(start)}else{None};
 let next=if start<8 {start+1}else{start};
 let correct=out==expected && iter.start==next && iter.end==8;
 #[cfg(not(NGQ_invert))] assert!(correct);
 #[cfg(NGQ_invert)] assert!(out==Some(9));
}
#[kani::proof] #[kani::unwind(34)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn NGQ_array_next() {
 let words:[u32;8]=kani::any();let cursor:usize=kani::any();kani::assume(cursor<=8);
 let mut iter=words.into_iter();if cursor>0 {let _=iter.nth(cursor-1);}
 let out=iter.next();let expected=if cursor<8 {Some(words[cursor])}else{None};
 let remaining=if cursor<8 {7-cursor}else{0};
 let correct=out==expected && iter.len()==remaining;
 #[cfg(not(NGQ_invert))] assert!(correct);
 #[cfg(NGQ_invert)] {if cursor<8 {assert!(out==Some(words[cursor]^1));}else{assert!(out==Some(0));}}
}
