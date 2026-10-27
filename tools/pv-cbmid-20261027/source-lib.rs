//! cfg(kani) extraction context; all source modules are unedited and hash-pinned.
extern crate alloc;
#[cfg(kani)]
pub use aspis_core::field;
#[cfg(kani)]
pub use aspis_statement::*;
#[cfg(kani)]
#[path = "/home/dombarker/project-offloads/codex-pv-cbmid-20261027/source-proof/constraints-fragments.rs"]
pub mod constraints_v4;
#[cfg(kani)]
pub mod pool_v1 {
    pub use aspis_statement::pool_v1::*;
    #[path = "/home/dombarker/project-offloads/codex-pv-cbmid-20261027/source-proof/hiding-with-harness.rs"]
    pub mod hiding;
    #[path = "/home/dombarker/project-offloads/codex-pv-cbmid-20261027/source-proof/oracle-fragments.rs"]
    pub mod oracle;
}
#[cfg(kani)]
pub mod r0 {
    pub use aspis_core::r0::*;
    #[path = "/home/dombarker/project-offloads/codex-pv-cb3-20261026/source/crates/aspis-core/src/r0/encoder.rs"]
    pub mod encoder;
    #[path = "/home/dombarker/project-offloads/codex-pv-cb3-20261026/source/crates/aspis-core/src/r0/basis.rs"]
    pub mod basis;
}
#[cfg(kani)]
pub mod reference;
#[cfg(all(kani,not(pv_cb_extract)))]
mod checks {
    use aspis_statement::pool_v1::pair_forest_hiding::*;
    #[kani::proof]
    #[kani::unwind(1025)]
    fn masks_complete() {
        assert_eq!(pool_v1_pair_forest_copy_active_row_masks_v1(),crate::reference::masks());
    }
    #[kani::proof]
    #[kani::unwind(257)]
    fn rows_complete() {
        assert_eq!(pool_v1_pair_forest_copy_active_rows_v1(),crate::reference::rows());
    }
}

#[cfg(kani)]
pub mod reference_encoder;
#[cfg(all(kani,not(pv_cb_extract)))]
mod schedule_checks {
    #[kani::proof]
    #[kani::unwind(137)]
    fn schedule_success() {
        let result=aspis_statement::pool_v1::pair_forest_hiding::build_pool_v1_pair_forest_copy_row_schedule_v1();
        assert!(matches!(result,Ok(ref links) if links.len()==136));
    }
}
#[cfg(kani)]
pub mod reference_multilinear;
#[cfg(all(kani,not(pv_cb_extract)))]
mod cell_checks {
    #[kani::proof]
    #[kani::unwind(1025)]
    fn cells_complete() {
        assert_eq!(aspis_statement::pool_v1::pair_forest_hiding::pool_v1_pair_forest_relation_free_mask_cells_v1(),crate::reference::cells());
    }
}

// Control-flow prerequisites only. No shipped/reference field equality is claimed.
#[cfg(all(kani,not(pv_cb_extract)))]
mod index_checks {
    #[kani::proof]
    #[kani::unwind(513)]
    fn encoder_pair_order() {
        let q:[u16;1024]=kani::any();
        let mut i=0usize;
        for (pair,n) in q.chunks_exact(2).zip(0..512) {
            assert_eq!(i,n);
            assert_eq!(pair[0],q[2*i]);
            assert_eq!(pair[1],q[2*i+1]);
            i+=1;
        }
        assert_eq!(i,512);
    }
    #[kani::proof]
    #[kani::unwind(12)]
    fn suffix_scan_order() {
        // 0/1 are Boolean coordinates; 2 is any non-Boolean coordinate class.
        let point:[u8;10]=kani::any();
        for value in point {kani::assume(value<=2);}
        let trailing=point.iter().rev().take_while(|x|**x<=1).count();
        let mut suffix=0usize;
        for value in &point[10-trailing..] {suffix=(suffix<<1)|usize::from(*value==1);}
        let mut indexed_trailing=0usize;
        while indexed_trailing<10 {
            if point[9-indexed_trailing]>1 {break;}
            indexed_trailing+=1;
        }
        let mut indexed_suffix=0usize;
        let mut coordinate=10-indexed_trailing;
        while coordinate<10 {
            indexed_suffix=(indexed_suffix<<1)|usize::from(point[coordinate]==1);
            coordinate+=1;
        }
        assert_eq!(trailing,indexed_trailing);
        assert_eq!(suffix,indexed_suffix);
    }
    #[kani::proof]
    #[kani::unwind(2)]
    fn sparse_row_bounds() {
        let prefix_len:usize=kani::any();kani::assume(prefix_len<=10);
        let trailing=10-prefix_len;
        let prefix:usize=kani::any();kani::assume(prefix<(1usize<<prefix_len));
        let suffix:usize=kani::any();kani::assume(suffix<(1usize<<trailing));
        let row=(prefix<<trailing)|suffix;
        assert!(row<1024);
        assert_eq!(row>>trailing,prefix);
        assert_eq!(row&((1usize<<trailing)-1),suffix);
    }
}
