# Per-function nullifier-path inspection

Frozen source unchanged at entry 1799052273; BuilderForestAdmissionPort is the retained port, not a new extraction.

- poseidon2::hash_fields_with_trace: Rust lines 516–528 initializes state[8], writes state[9], then uses input.chunks(8).enumerate and chunk.iter().enumerate; shared iterators, direct state[index] assignment. Emission lines 2239–2278 retains index_mut_back and applies it in both branches; absorption loop lines 2183–2201 uses Array.update and passes its result recursively. No dropped restoration continuation in these bodies.
- hash_fields callbacks: shared index callback returns state unchanged; the traced callback threads the captured trace. Checked constant callback theorem in HashCallback17.
- nullifier reference preimage: owned explicit array construction/index reads; no mutable iterator or borrowed-element writes. The checked preimage theorem is reused.
- format.pool_v1_nullifier / spend.derive_nullifier: forwarding calls, no write or discarded back function.

SDY covers the twelve-leaf release Funs overlap under ruling (o); this job does not duplicate that scan or claim it covers this separate builder port. The two fixture key/salt values are equal across transfer/withdrawal; initial length16 and both absorption writes change the state. The production source-loop equations and final source result are checked by 50924 and50933. These give a concrete comparison to the retained native nullifier, with both absorption writes preserved. A new native differential has not been run by this job; D287's numeric fixture probe is retained evidence, not a general fidelity proof.
