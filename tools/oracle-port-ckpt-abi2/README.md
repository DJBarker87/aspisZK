# Checkpoint ABI continuation

This is a standalone proof crate. It links the actual frozen verifier crate;
no shipped crate is edited. `proofs::frozen_writer_exact_byte_and_reads`
compares one arbitrary output byte and one arbitrary checksum-input byte to
`body_byte`. This universally quantified index method covers every byte
without constructing a second 1736-byte vector. All fields are arbitrary;
wide-field inputs are canonical. The writer domain is S2, next=10, 64 weights.
Proof/public slices have lengths 3 and 5 in these roots. Those fixed lengths
are a remaining generalization boundary, not an all-length source theorem.
The hash is a three-answer arbitrary call protocol; the protocol checks the
exact ordered addresses, lengths and checksum domain. Native SHA and the
runtime same-snapshot obligation are separate.

Field contracts prove the actual shipped QM31 encode/decode and wide decode
against explicit LE limb formulas, and every wide-encode byte against its
limb formula. Foreign field types cannot implement Kani Arbitrary here, so
verified decoder stubs return Option arrays of raw words, then reconstruct
canonical field structures. The replacement adapter is exactly the wrapper
whose original decoder call is checked by the contract root. The reader
composition roots use these verified contracts and retain all other checks.

The `reader_proofs` roots remain diagnostic until their exact receipt is
green. A successful field contract, writer root, extraction or model theorem
must not be reported as a successful reader/driver/cone join. CBMC uses its
standard no-malloc-failure model; it does not prove physical allocation
availability. No production allocator or drop semantics are replaced here.

Host commands go through `run-kani.py` or `extract.py`; their wrapper records
source hashes, command, exit, wall time, GNU time and cgroup peaks, swaps and
explicit 6G/8G/zero-swap/64-task limits. `compile.py` uses the prescribed local
Lean lock and private object cache. All failed attempts are retained.
