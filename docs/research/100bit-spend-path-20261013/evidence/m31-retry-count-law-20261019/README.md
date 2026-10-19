# Fixed sixteen-attempt M31 sampler: exact finite counts

The executable decoder masks a uniform32-bit word down to31 bits and rejects the top remainder P31=2^31-1. The accepted-word fiber for each r< P31 has exactly two words, and the rejected-word fiber also has exactly two words. A generic proof-only permutation of word fibers proves equal cardinality of every accepted output event for the actual first-success function on sixteen word slots; the permutation is not executed by the sampler.

The all-rejected output fiber is in bijection with sixteen independent choices from the two rejected words, hence has cardinality2^16. Nat.card partition proves total input count (2^32)^16, abort count2^16, and success count (2^32)^16-2^16. No word space or field is enumerated. The exact rational probability theorem and the bridge to the recovery mean are still pending; this packet supplies their counting prerequisites.

Seven focused Lean4.32 modules include six proof leaves and the generic theorem axioms audit. Exact sources/import pins, commands, source revisions, exit codes, time, RSS and zero process swap are retained. Audited results contain only standard axioms. The generic leaf's raw receipt has no printed-axioms declarations; its separate import-only AuditV2 target checks the transitive symmetry theorem and runtime-map theorem. No full package replay was run.

A Fintype-based mass consumer exceeded its2GiB interpreter guard. Import-only isolation passed at1.49GB, identifying proof elaboration rather than cache loading as the problem. The replacement uses Nat.card partition and avoids concrete Fintype reductions; it passed at1.50GB under the same cap. The failed source/receipt/log are retained as diagnostics. No unchanged memory-failed job was rerun at a larger cap.

Boundaries: this models uniform32-bit words and fixed retry slots. A Boolean-bit/word law, actual Rust/caller correspondence, sequential/offset behavior across limbs, eight-limb WideExact field packing, whole finite field-pair tape law, and global exhaustion/query/bit-cost composition remain separate. It does not claim source-backed privacy sampling or the full100-bit spend theorem.
