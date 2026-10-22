//! One native binary-parent iteration, with the untouched input suffix framed.
//! The caller guarantees strict ordering and nonempty remaining input.
#[derive(Debug,PartialEq,Eq)]
pub struct Group { pub parent:u32,pub consumed:usize,pub sibling:Option<u32> }
/// D144 structurally finite reference for one binary parent.
pub fn reference(a:u32,b:Option<u32>)->Group {
    let parent=a>>1u32;
    if let Some(b)=b {
        if b==a^1 {return Group{parent,consumed:2,sibling:None};}
    }
    Group{parent,consumed:1,sibling:Some(a^1)}
}
#[cfg(kani)] mod proofs {
 use super::*;
 #[kani::proof] #[kani::unwind(36)]
 fn binary_group() {
  let a:u32=kani::any();let b:Option<u32>=kani::any();
  kani::assume(a<1<<18);
  if let Some(b)=b {kani::assume(a<b && b<1<<18);}
  let mut level=vec![a];if let Some(b)=b {level.push(b);}
  let mut i=0;let mut requests=Vec::new();let mut next=Vec::new();
  // The source generate group's body, specialised only to Arity::Two.
  let parent = level[i] >> 1;
  for slot in 0..2u32 {
      let child = (parent << 1) | slot;
      if i < level.len() && level[i] == child {
          i += 1;
      } else {
          requests.push(child);
      }
  }
  next.push(parent);
  let expected=reference(a,b);
  assert_eq!(i,expected.consumed);assert_eq!(next,vec![expected.parent]);
  let siblings:Vec<u32>=expected.sibling.into_iter().collect();assert_eq!(requests,siblings);
  // node_count's same parent group, including occupied-node arithmetic.
  let mut j=0;
  while j<level.len() && level[j]>>1==parent {j+=1;}
  assert_eq!(j,i);assert_eq!(2-(j-0),requests.len());
 }
}

#[cfg(kani)] mod cursor_proofs {
 use super::*;
 #[kani::proof] #[kani::unwind(36)]
 fn binary_cursor_transition() {
  let mut level:[u32;16]=kani::any();let n:usize=kani::any();let start:usize=kani::any();let w:usize=kani::any();
  kani::assume(n>0 && n<=16 && start<n && w<=start);
  for k in 0..n {kani::assume(level[k]<1<<18);if k>0 {kani::assume(level[k-1]<level[k]);}}
  let saved=level;let a=level[start];let b=if start+1<n {Some(level[start+1])} else {None};
  let expected=reference(a,b);
  let mut i=start;let mut requests=Vec::new();
  // Exact native generate group specialised to the deployed binary arity.
  let parent=level[i]>>1;
  for slot in 0..2u32 {
   let child=(parent<<1)|slot;
   if i<n && level[i]==child {i+=1;} else {requests.push(child);}
  }
  assert_eq!(i-start,expected.consumed);
  assert_eq!(parent,expected.parent);
  assert_eq!(requests.len(),expected.sibling.is_some() as usize);
  if let Some(sibling)=expected.sibling {assert_eq!(requests[0],sibling);}
  // Exact count group and in-place update, with unread suffix preserved.
  let mut j=start;
  while j<n && level[j]>>1==parent {j+=1;}
  assert_eq!(j,i);assert_eq!(2-(j-start),requests.len());
  level[w]=parent;
  assert!(w<j);
  for k in j..n {assert_eq!(level[k],saved[k]);}
 }
}
