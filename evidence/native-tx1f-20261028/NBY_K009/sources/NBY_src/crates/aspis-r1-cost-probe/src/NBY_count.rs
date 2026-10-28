use super::*;
#[kani::proof] #[kani::unwind(34)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(<[u32]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
fn NBY_count_row(){let mut level:[u32;16]=kani::any();let n:usize=kani::any();let i0:usize=kani::any();let w0:usize=kani::any();let k:usize=kani::any();let count0:usize=kani::any();kani::assume(i0<n&&n<=16&&w0<=i0&&k<16&&count0<=288);for a in i0..n-1{kani::assume(level[a]<level[a+1]);}let old=level[k];let expected=if i0+1<n&&level[i0+1]/2==level[i0]/2{i0+2}else{i0+1};let arity=Arity::Two;let mut i=i0;let mut w=w0;let mut count=count0;let parent=index_at(&level,i)>>arity.bits();let mut j=i;while j<n&&index_at(&level,j)>>arity.bits()==parent{j+=1;}count+=arity.width()-(j-i);level[w]=parent;w+=1;i=j;assert!(i==expected&&w==w0+1&&count==count0+2-(expected-i0)&&level[k]==if k==w0{parent}else{old});}
#[kani::proof] #[kani::unwind(34)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(<[u32]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
fn NBY_count_row_wrong(){let mut level:[u32;16]=kani::any();let n:usize=kani::any();let i0:usize=kani::any();let w0:usize=kani::any();let k:usize=kani::any();let count0:usize=kani::any();kani::assume(i0<n&&n<=16&&w0<=i0&&k<16&&count0<=288);for a in i0..n-1{kani::assume(level[a]<level[a+1]);}let old=level[k];let expected=if i0+1<n&&level[i0+1]/2==level[i0]/2{i0+2}else{i0+1};let arity=Arity::Two;let mut i=i0;let mut w=w0;let mut count=count0;let parent=index_at(&level,i)>>arity.bits();let mut j=i;while j<n&&index_at(&level,j)>>arity.bits()==parent{j+=1;}count+=arity.width()-(j-i);level[w]=parent;w+=1;i=j;assert!(!(i==expected&&w==w0+1&&count==count0+2-(expected-i0)&&level[k]==if k==w0{parent}else{old}));}
#[kani::proof] #[kani::unwind(34)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(<[u32]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
fn NBY_count_admitted_start(){let input:[u32;16]=kani::any();let n:usize=kani::any();let k:usize=kani::any();kani::assume(0<n&&n<=16&&k<16);for a in 0..n{kani::assume(input[a]<262144);if a+1<n{kani::assume(input[a]<input[a+1]);}}let accepted=well_formed(&input[..n]);assert!(accepted);let mut level=[0u32;MAX_BATCH];level[..n].copy_from_slice(&input[..n]);let count=0usize;let mut levels=0..Arity::Two.levels();let depth=levels.next();let w=0usize;let i=0usize;assert!(level[k]==if k<n{input[k]}else{0}&&count==0&&depth==Some(0)&&levels.start==1&&w==0&&i==0);}
#[kani::proof] #[kani::unwind(34)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(<[u32]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
fn NBY_count_admitted_start_wrong(){let input:[u32;16]=kani::any();let n:usize=kani::any();let k:usize=kani::any();kani::assume(0<n&&n<=16&&k<16);for a in 0..n{kani::assume(input[a]<262144);if a+1<n{kani::assume(input[a]<input[a+1]);}}let accepted=well_formed(&input[..n]);assert!(accepted);let mut level=[0u32;MAX_BATCH];level[..n].copy_from_slice(&input[..n]);let count=0usize;let mut levels=0..Arity::Two.levels();let depth=levels.next();let w=0usize;let i=0usize;assert!(!(level[k]==if k<n{input[k]}else{0}&&count==0&&depth==Some(0)&&levels.start==1&&w==0&&i==0));}
#[kani::proof] #[kani::unwind(34)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(<[u32]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
fn NBY_count_outer_transition(){let idx:[u32;16]=kani::any();let n:usize=kani::any();let i:usize=kani::any();let w:usize=kani::any();let k:usize=kani::any();kani::assume(n>0&&n<=16&&i==n&&w<=n&&k<16);let before=idx[k];let mut levels=kani::any::<u32>()..Arity::Two.levels();kani::assume(levels.start<=18);let depth=levels.start;let next_n=w;let next=levels.next();let next_w=0usize;let next_i=0usize;assert!(next_n<=16&&next_w<=next_i&&next_i<=next_n&&idx[k]==before&&next==if depth<18{Some(depth)}else{None});}
#[kani::proof] #[kani::unwind(34)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(<[u32]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
fn NBY_count_outer_transition_wrong(){let idx:[u32;16]=kani::any();let n:usize=kani::any();let i:usize=kani::any();let w:usize=kani::any();let k:usize=kani::any();kani::assume(n>0&&n<=16&&i==n&&w<=n&&k<16);let before=idx[k];let mut levels=kani::any::<u32>()..Arity::Two.levels();kani::assume(levels.start<=18);let depth=levels.start;let next_n=w;let next=levels.next();let next_w=0usize;let next_i=0usize;assert!(!(next_n<=16&&next_w<=next_i&&next_i<=next_n&&idx[k]==before&&next==if depth<18{Some(depth)}else{None}));}
