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

#[path="../../../crates/aspis-r1-cost-probe/src/multiproof.rs"] mod multiproof;
#[cfg(kani)] mod hash_contracts;
#[cfg(kani)] mod clear_source;
#[cfg(kani)] mod clear_contracts;
#[cfg(kani)] mod dtail_source;
#[cfg(kani)] mod dtail_contracts;
#[cfg(kani)] mod proofs {
    #[kani::proof]
    #[kani::unwind(40)]
    fn compact_one_exact_with_error_prefix() {
        let data:[u8;32]=kani::any();let n=32;
        let prefix:[u8;3]=kani::any();let mut left=prefix.to_vec();let mut right=left.clone();
        let a=super::host_compact::compact_values(&data[..n],&mut left);
        let b=super::compact::compact_values(&data[..n],&mut right);
        assert_eq!(a,b);assert_eq!(left,right);
    }
    #[kani::proof]
    #[kani::unwind(40)]
    fn record_exact_row14() {
        let data:[u8;32]=kani::any();let n=32;
        let row=14;
        assert_eq!(super::host_wire::record(row,&data[..n]),super::r1_wire::record(row,&data[..n]));
    }
}

#[cfg(kani)] mod field_codec_contracts;

#[cfg(test)] mod decoder_precondition_tests;

#[cfg(kani)]
#[path="../../ct-kernels-20261022/reference/field.rs"] mod reference_field;
#[cfg(kani)] mod inverse_chain_contracts;

#[cfg(kani)] mod hash_fn_contracts;

#[cfg(kani)] mod power_chain_contracts;

#[cfg(kani)] mod generic_inverse_contracts;

#[cfg(kani)] mod representation_contracts;

#[cfg(kani)] mod scalar_adapter_contracts;

#[cfg(kani)] mod raw_writer_contracts;
