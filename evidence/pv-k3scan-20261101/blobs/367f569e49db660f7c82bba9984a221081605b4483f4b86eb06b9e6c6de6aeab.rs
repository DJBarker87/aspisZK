#![allow(dead_code,unexpected_cfgs)]
extern crate alloc;
#[path="../../../crates/aspis-r1-cost-probe/src/sampler.rs"] mod sampler;
#[path="../../../crates/aspis-r1-cost-probe/src/r1_wire.rs"] mod r1_wire;
#[path="../../../crates/aspis-r1-cost-probe/src/host_wire.rs"] mod host_wire;
// The selected codec's only verifier import is this public length constant.
// Binding to the actual source is checked by the runner before compilation.
mod verifier {pub const SEMANTIC_BYTES:usize=12903+29*32;}
#[path="../../../crates/aspis-r1-cost-probe/src/compact.rs"] mod compact;
#[path="../../../crates/aspis-r1-cost-probe/src/host_compact.rs"] mod host_compact;

#[cfg(kani)] mod proofs {
    #[kani::proof]
    #[kani::unwind(70)]
    fn compact_values_exact_with_error_prefix() {
        let data:[u8;64]=kani::any();let n:usize=kani::any();kani::assume(n<=64);
        let prefix:[u8;3]=kani::any();let mut left=prefix.to_vec();let mut right=left.clone();
        let a=super::host_compact::compact_values(&data[..n],&mut left);
        let b=super::compact::compact_values(&data[..n],&mut right);
        assert_eq!(a,b);assert_eq!(left,right);
    }
    #[kani::proof]
    #[kani::unwind(70)]
    fn record_exact_short_payload() {
        let data:[u8;32]=kani::any();let n:usize=kani::any();kani::assume(n<=32);
        let row:u8=kani::any();
        assert_eq!(super::host_wire::record(row,&data[..n]),super::r1_wire::record(row,&data[..n]));
    }
}
