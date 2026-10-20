# S3 P6 powers/low totality

`S3PowersLowTotalV1` proves totality and canonical-output preservation for the checked P6 operational models used for the two four-element powers arrays and the sixteen-element low callback array. It reuses the exact selected current field multiplication and reduction owners and uses standard Lean axioms only.

The result is scoped to the P6 callback-array model. It does not prove the Rust standard library's `core::array::from_fn` corresponds to that model, nor does it bind the model arrays to the current `Weights::pair` caller. That call-site/source correspondence remains open. The source hash and line-level current caller are retained in the model review notes sent separately to the parent.

Run `python3 check_packet.py` from this directory to verify packet file hashes, direct owner source hashes, and producer receipt hashes. The focused compile receipt records the exact command, Lean 4.32.0 hash, `-M 4400 -j 1`, wall time, peak RSS, swap, and the complete `#print axioms` output. The compile used the already-pinned warm closure and a small exact-owner overlay; it did not rebuild dependencies.
