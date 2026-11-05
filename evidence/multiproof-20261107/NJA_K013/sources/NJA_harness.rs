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
}
