#[cfg(kani)]
mod NJA_native {
    use super::*;
    #[kani::proof]
    fn NJA_bits() { let eight:bool=kani::any();let a=if eight{Arity::Eight}else{Arity::Two};assert_eq!(a.bits(),if eight{3}else{1}); }
    #[kani::proof]
    fn NJA_bits_control() { let eight:bool=kani::any();let a=if eight{Arity::Eight}else{Arity::Two};assert_eq!(a.bits(),if eight{1}else{3}); }
    #[kani::proof]
    fn NJA_width() { let eight:bool=kani::any();let a=if eight{Arity::Eight}else{Arity::Two};assert_eq!(a.width(),if eight{8}else{2}); }
    #[kani::proof]
    fn NJA_width_control() { let eight:bool=kani::any();let a=if eight{Arity::Eight}else{Arity::Two};assert_eq!(a.width(),if eight{2}else{8}); }
    #[kani::proof]
    fn NJA_levels() { let eight:bool=kani::any();let a=if eight{Arity::Eight}else{Arity::Two};assert_eq!(a.levels(),if eight{6}else{18}); }
    #[kani::proof]
    fn NJA_levels_control() { let eight:bool=kani::any();let a=if eight{Arity::Eight}else{Arity::Two};assert_eq!(a.levels(),if eight{18}else{6}); }
    #[kani::proof]
    fn NJA_index() {let a:[u32;16]=kani::any();let i:usize=kani::any();kani::assume(i<16);assert_eq!(index_at(&a,i),a[i]);}
    #[kani::proof]
    fn NJA_index_control() {let a:[u32;16]=kani::any();let i:usize=kani::any();kani::assume(i<16);assert_eq!(index_at(&a,i),a[i]^1);}

    #[kani::proof]
    fn NJA_root() {let a:[[u8;32];16]=kani::any();let r:[u8;32]=kani::any();assert_eq!(root_matches(&a,&r),a[0].eq(&r));}
    #[kani::proof]
    fn NJA_root_control() {let a:[[u8;32];16]=kani::any();let r:[u8;32]=kani::any();assert_ne!(root_matches(&a,&r),a[0].eq(&r));}
    #[kani::proof]
    fn NJA_well_empty() {let a:[u32;0]=[];assert!(!well_formed(&a));}
    #[kani::proof]
    fn NJA_well_empty_control() {let a:[u32;0]=[];assert!(well_formed(&a));}
    #[kani::proof]
    fn NJA_well_large() {let a:[u32;17]=kani::any();assert!(!well_formed(&a));}
    #[kani::proof]
    fn NJA_well_large_control() {let a:[u32;17]=kani::any();assert!(well_formed(&a));}
    #[kani::proof]
    fn NJA_count_empty() {let a:[u32;0]=[];let eight:bool=kani::any();let arity=if eight{Arity::Eight}else{Arity::Two};assert_eq!(node_count(arity,&a),None);}
    #[kani::proof]
    fn NJA_count_empty_control() {let a:[u32;0]=[];let eight:bool=kani::any();let arity=if eight{Arity::Eight}else{Arity::Two};assert!(node_count(arity,&a).is_some());}
    #[kani::proof]
    fn NJA_count_large() {let a:[u32;17]=kani::any();let eight:bool=kani::any();let arity=if eight{Arity::Eight}else{Arity::Two};assert_eq!(node_count(arity,&a),None);}
    #[kani::proof]
    fn NJA_count_large_control() {let a:[u32;17]=kani::any();let eight:bool=kani::any();let arity=if eight{Arity::Eight}else{Arity::Two};assert!(node_count(arity,&a).is_some());}

    #[kani::proof]
    fn NJA_window_active() {let a:[u32;16]=kani::any();let n:usize=kani::any();let at:usize=kani::any();kani::assume(n<=16 && at+0<=n);kani::assume(at<n && n-at>=2);let mut it=a[at..n].windows(2);let w=it.next().unwrap();assert_eq!(w.len(),2);assert_eq!(w[0],a[at]);assert_eq!(w[1],a[at+1]);}
    #[kani::proof]
    fn NJA_window_active_control() {let a:[u32;16]=kani::any();let n:usize=kani::any();let at:usize=kani::any();kani::assume(n<=16 && at<=n);kani::assume(at<n && n-at>=2);let mut it=a[at..n].windows(2);let w=it.next().unwrap();assert_eq!(w[0],a[at]^1);}
    #[kani::proof]
    fn NJA_window_exit() {let a:[u32;16]=kani::any();let n:usize=kani::any();let at:usize=kani::any();kani::assume(n<=16 && at<=n && n-at<2);let mut it=a[at..n].windows(2);assert!(it.next().is_none());}
    #[kani::proof]
    fn NJA_window_exit_control() {let a:[u32;16]=kani::any();let n:usize=kani::any();let at:usize=kani::any();kani::assume(n<=16 && at<=n && n-at<2);let mut it=a[at..n].windows(2);assert!(it.next().is_some());}
    #[kani::proof]
    fn NJA_iter_active() {let a:[u32;16]=kani::any();let n:usize=kani::any();let at:usize=kani::any();kani::assume(n<=16 && at<n);let mut it=a[at..n].iter();let x=it.next().unwrap();assert_eq!(*x,a[at]);assert_eq!(it.len(),n-at-1);}
    #[kani::proof]
    fn NJA_iter_active_control() {let a:[u32;16]=kani::any();let n:usize=kani::any();let at:usize=kani::any();kani::assume(n<=16 && at<n);let mut it=a[at..n].iter();let x=it.next().unwrap();assert_eq!(*x,a[at]^1);}
    #[kani::proof]
    fn NJA_iter_exit() {let a:[u32;16]=kani::any();let n:usize=kani::any();kani::assume(n<=16);let mut it=a[n..n].iter();assert!(it.next().is_none());}
    #[kani::proof]
    fn NJA_iter_exit_control() {let a:[u32;16]=kani::any();let n:usize=kani::any();kani::assume(n<=16);let mut it=a[n..n].iter();assert!(it.next().is_some());}
    #[derive(Clone,Copy)] struct NJA_Never;
    impl aspis_core::Digest32 for NJA_Never {fn digest(&self,_parts:&[&[u8]])->[u8;32]{panic!("unreachable digest on invalid entry")}}
    #[kani::proof]
    fn NJA_verify_invalid() {let mut idx:[u32;16]=kani::any();let mut val:[[u8;32];16]=kani::any();let n:usize=kani::any();kani::assume(n==0 || n>16);let k:usize=kani::any();let j:usize=kani::any();kani::assume(k<16 && j<32);let x=idx[k];let v=val[k][j];let root:[u8;32]=kani::any();let out=verify_in_place(NJA_Never,Arity::Two,&root,&mut idx,&mut val,n,&[]);assert!(!out);assert_eq!(idx[k],x);assert_eq!(val[k][j],v);}
    #[kani::proof]
    fn NJA_verify_invalid_control() {let mut idx:[u32;16]=kani::any();let mut val:[[u8;32];16]=kani::any();let n:usize=kani::any();kani::assume(n==0 || n>16);let root:[u8;32]=kani::any();let out=verify_in_place(NJA_Never,Arity::Two,&root,&mut idx,&mut val,n,&[]);assert!(out);}
    #[kani::proof]
    fn NJA_verify_invalid_frame_control() {let mut idx:[u32;16]=kani::any();let mut val:[[u8;32];16]=kani::any();let n:usize=kani::any();kani::assume(n==0 || n>16);let k:usize=kani::any();kani::assume(k<16);let x=idx[k];let root:[u8;32]=kani::any();let _=verify_in_place(NJA_Never,Arity::Two,&root,&mut idx,&mut val,n,&[]);assert_eq!(idx[k],x^1);}

    fn NJA_group_once(arity:Arity,level:&[u32;16],n:usize,parent:u32,j:usize)->(bool,usize){
      if j<n && index_at(level,j)>>arity.bits()==parent {(true,j+1)} else {(false,j)}
    }
    #[kani::proof]
    fn NJA_group_active(){let level:[u32;16]=kani::any();let n:usize=kani::any();let j:usize=kani::any();kani::assume(j<n&&n<=16);let eight:bool=kani::any();let arity=if eight{Arity::Eight}else{Arity::Two};let parent=level[j]>>(if eight{3}else{1});assert_eq!(NJA_group_once(arity,&level,n,parent,j),(true,j+1));}
    #[kani::proof]
    fn NJA_group_active_control(){let level:[u32;16]=kani::any();let n:usize=kani::any();let j:usize=kani::any();kani::assume(j<n&&n<=16);let eight:bool=kani::any();let arity=if eight{Arity::Eight}else{Arity::Two};let parent=level[j]>>(if eight{3}else{1});assert_eq!(NJA_group_once(arity,&level,n,parent,j),(false,j));}
    #[kani::proof]
    fn NJA_group_bounds_exit(){let level:[u32;16]=kani::any();let n:usize=kani::any();let j:usize=kani::any();kani::assume(n<=16&&j>=n);let parent:u32=kani::any();assert_eq!(NJA_group_once(Arity::Two,&level,n,parent,j),(false,j));}
    #[kani::proof]
    fn NJA_group_bounds_exit_control(){let level:[u32;16]=kani::any();let n:usize=kani::any();let j:usize=kani::any();kani::assume(n<=16&&j>=n);let parent:u32=kani::any();assert!(NJA_group_once(Arity::Two,&level,n,parent,j).0);}
    #[kani::proof]
    fn NJA_group_parent_exit(){let level:[u32;16]=kani::any();let n:usize=kani::any();let j:usize=kani::any();let parent:u32=kani::any();kani::assume(j<n&&n<=16&&level[j]>>1!=parent);assert_eq!(NJA_group_once(Arity::Two,&level,n,parent,j),(false,j));}
    #[kani::proof]
    fn NJA_group_parent_exit_control(){let level:[u32;16]=kani::any();let n:usize=kani::any();let j:usize=kani::any();let parent:u32=kani::any();kani::assume(j<n&&n<=16&&level[j]>>1!=parent);assert!(NJA_group_once(Arity::Two,&level,n,parent,j).0);}
    fn NJA_finish_group(level:&mut[u32;16],count:&mut usize,w:&mut usize,i:&mut usize,j:usize){let parent=index_at(level,*i)>>Arity::Two.bits();*count+=Arity::Two.width()-(j-*i);level[*w]=parent;*w+=1;*i=j;}
    #[kani::proof]
    fn NJA_finish_group_log(){let mut level:[u32;16]=kani::any();let mut count:usize=kani::any();let mut w:usize=kani::any();let mut i:usize=kani::any();let j:usize=kani::any();kani::assume(w<=i&&i<j&&j<=16&&j-i<=2&&count<=288);let old_i=i;let old_w=w;let old_count=count;let k:usize=kani::any();kani::assume(k<16);let before=level[k];let parent=level[i]>>1;NJA_finish_group(&mut level,&mut count,&mut w,&mut i,j);assert_eq!(i,j);assert_eq!(w,old_w+1);assert_eq!(count,old_count+2-(j-old_i));assert_eq!(level[k],if k==old_w{parent}else{before});}
    #[kani::proof]
    fn NJA_finish_group_log_control(){let mut level:[u32;16]=kani::any();let mut count:usize=kani::any();let mut w:usize=kani::any();let mut i:usize=kani::any();let j:usize=kani::any();kani::assume(w<=i&&i<j&&j<=16&&j-i<=2&&count<=288);let old_w=w;let parent=level[i]>>1;NJA_finish_group(&mut level,&mut count,&mut w,&mut i,j);level[old_w]^=1;assert_eq!(level[old_w],parent);}
    #[kani::proof]
    fn NJA_height_active(){let d:u32=kani::any();kani::assume(d<18);let mut it=d..18;assert_eq!(it.next(),Some(d));assert_eq!(it.start,d+1);assert_eq!(it.end,18);}
    #[kani::proof]
    fn NJA_height_active_control(){let d:u32=kani::any();kani::assume(d<18);let mut it=d..18;assert_eq!(it.next(),Some(d^1));}
    #[kani::proof]
    fn NJA_height_exit(){let d:u32=kani::any();kani::assume(d>=18);let mut it=d..18;assert_eq!(it.next(),None);assert_eq!(it.start,d);}
    #[kani::proof]
    fn NJA_height_exit_control(){let d:u32=kani::any();kani::assume(d>=18);let mut it=d..18;assert!(it.next().is_some());}
}
#[cfg(kani)]
pub fn NJA_value_at(values:&[[u8;32];MAX_BATCH],index:usize)->[u8;32]{value_at(values,index)}
