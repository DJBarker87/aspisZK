# Scalar-factor to S9 model instance

This packet freezes a focused GREEN Lean consumer. From one successful generated `Weights.scalar_factor` call, canonical p-array values, a canonical seed, and successful `kpowers 4 seed`, it returns the exact emitted `PERM` reads and proves the decoded output equals `S2LibraFactoredIdentity.scalar (scaled pVec quarter) seed`. The same `pVec`, quarter, and decoded seed instantiate `S3S9CurrentSourceModel.old_s9_weight_eq_factored`; both facts are in one theorem result.

The theorem is useful for the `factored_s2_libra_weights` low call, whose generated body sets `q1` from `kpowers 4 extra[side]` and passes that `q1` to `scalar_factor`. It is not a proof for normal `Weights::pair` factor arrays, which are constructor-produced rather than necessarily powers.

The result does not yet establish both side calls, the high `terms` array, the full factored helper loop, its caller/control flow, actual field-operation laws, or adopted Rust source refinement. P6 `kpowers`/`from_fn` and fold-to-Std correspondence remain explicit boundaries. No `.olean` binaries are included.

Run `python3 check_packet.py` in this directory to verify the packet source and dependency source hashes.
