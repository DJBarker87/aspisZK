// Structural caller slices only, not field arithmetic substitutes or whole-function equivalence.
#[cfg(kani)]
mod PV_Inv_control {
#[kani::proof] #[kani::unwind(4)]
fn first_empty(){let weights:[u32;2]=kani::any();if let Some(s)=weights.iter().position(|v|*v==0){assert!(s<2);assert_eq!(weights[s],0);if s==1{assert_ne!(weights[0],0);}}}
#[kani::proof]
fn guarded_pivot(){let value:u32=kani::any();if value==0{return;}assert_ne!(value,0);}
#[kani::proof] #[kani::unwind(5)]
fn swap_pivot(){let mut a:[[u32;3];3]=kani::any();let c:usize=kani::any();kani::assume(c<3);if let Some(p)=(c..3).find(|&i|a[i][c]!=0){a.swap(c,p);assert_ne!(a[c][c],0);}}
#[kani::proof] #[kani::unwind(5)]
fn packed_membership(){let vals:[u32;2]=kani::any();let ws:[u32;2]=kani::any();let mut values=[0u32;2];let mut weights=[0u32;2];for j in 0..2{if let Some(s)=weights.iter().position(|v|*v==0){values[s]=vals[j];weights[s]=ws[j];}}for s in 0..2{if weights[s]!=0{assert!(values[s]==vals[0]||values[s]==vals[1]);}}}
#[kani::proof] #[kani::unwind(5)]
fn guard_all_slots(){let chi:u32=kani::any();let vals:[u32;2]=kani::any();let mut clear=true;for value in &vals{clear &= chi!=*value;}if clear{for value in vals{assert_ne!(chi,value);}}}
#[kani::proof] #[kani::unwind(5)]
fn guard_both_sides(){let chi:u32=kani::any();let vals:[[u32;2];2]=kani::any();let mut clear=true;for side in vals{for value in side{clear &= chi!=value;}}if clear{for side in vals{for value in side{assert_ne!(chi,value);}}}}
#[kani::proof] #[kani::unwind(4)]
fn overwritten_inactive(){let old:u32=kani::any();let new:u32=kani::any();let mut values=[old,0];let mut weights=[0u32;2];let weight:u32=kani::any();kani::assume(weight!=0);let s=weights.iter().position(|v|*v==0).unwrap();values[s]=new;weights[s]=weight;assert_eq!(values[0],new);assert_ne!(weights[0],0);}
#[kani::proof] #[kani::unwind(5)]
fn static_arity(){let values:[u32;2]=kani::any();let mut slots=[0u32;2];let mut arity=0usize;for value in values{assert!(arity<2);let slot=arity;arity+=1;slots[slot]=value;}assert_eq!(slots[0],values[0]);assert_eq!(slots[1],values[1]);}
#[kani::proof]
fn m31_difference_zero(){const P:u32=0x7fffffff;let x:u32=kani::any();let y:u32=kani::any();kani::assume(x<P&&y<P);let s=x+P-y;let difference=if s>=P{s-P}else{s};assert_eq!(difference==0,x==y);assert!(difference<P);}
#[kani::proof]
fn qm31_zero_control(){let x:[u32;4]=kani::any();let z=(x[0]==0&&x[1]==0)&&(x[2]==0&&x[3]==0);if !z{assert!(x[0]!=0||x[1]!=0||x[2]!=0||x[3]!=0);}else{assert_eq!(x[0],0);assert_eq!(x[1],0);assert_eq!(x[2],0);assert_eq!(x[3],0);}}
}
