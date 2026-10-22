# S3 powers trace to scalar-factor helper carrier

This focused Lean owner maps values from the retained S3 `weights::powers` stateful P6 trace into the nominal `AspisR1S9HelperP6.field.WideExact` carrier through the shared CurrentWide exact representation. For each of the four indices, it preserves canonicality and the exact decoded value `decode(alpha)^i`. It reuses the indexed powers theorem; it adds no power arithmetic.

The result is a carrier/value bridge for supplying the `p` array of the scalar-factor helper model. It does not prove the enclosing Rust caller equation assigning its `ap0` from `weights::powers(alpha[0])`, Rust `core::array::from_fn` correspondence, the actual six field-operation laws, the full `factored_s2_libra_weights` call, or `Weights::pair` continuation. Those remain separate boundaries.

No `.olean` binary is included. Original source hashes, producer receipts, selected object hashes, and the focused local Lean receipt are pinned below.
