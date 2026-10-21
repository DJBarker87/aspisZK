# S3/S9 selected `kpowers` read semantics

This packet proves that successful reads from the exact selected four-entry `kpowers` result are canonical and decode to the corresponding seed powers. It composes that fact with the scalar-factor fourfold meaning theorem to remove scalar-factor's per-read canonicality premises. The companion value equations for the same `q0`–`q3` witnesses are composed in `evidence/s3-s9-scalar-factor-power-polynomial-v1-20261021`.

The proof retains the P6 iterator-fold relation, canonicality of indexed `p` reads, selected `kpowers` success, and canonical seed. The `core.array.from_fn` Rust standard-library correspondence and enclosing `Weights::pair` caller refinement remain open. Run `python3 check_packet.py` from this directory to verify the source, receipt, and file pins.
