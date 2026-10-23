# Stage 1: per-call oracle transport

`S2Z_Oracle.successful_call` establishes the exact CheckpointBytes5Inputs.Oracle
for the digest dictionary transported from the adopted AdapterRw extraction.
Its quantified input is a single call, not a whole trace or successful verifier.
`dictionary_call` preserves op43 verbatim, including fail/div.
`total_call` establishes the stronger total law consumed by S2CallerFacts.oracle.

Retained hypotheses: `NativeBinding` (op43 is the native hashv wrapper),
`RuntimeSyscall` (every returning syscall decodes to SHA256 on flattened input),
and `P1Realization` (fixed-oracle interpretation inside the existing P1 ROM
experiment). The total theorem additionally requires total native return with
encoded SHA256 output. This packet does not prove SHA256 random, instantiate the
native ABI port, or derive deterministic SHA256 equality from a probability
bound. P1Realization exposes the semantic interpretation needed when using P1;
it is not a new proved version of the headline P1 assumption. Native installation
remains open; these premises receive no discharge credit.

Source connection inspected: lib.rs:11–16 is hashv(parts).to_bytes(); the owned
extraction dictionary at AdapterRwModel:640–644 delegates exactly to op43. The
retained solana-sha256-hasher 2.3.0 source calls sol_sha256 with the parts pointer,
parts count and 32-byte output pointer on target_os=solana; native SHA uses ordered
Hasher.update per slice. The S4 wrapper packet is reused only for read-only source
inspection, not reattributed as an adopted-owned runtime proof. Runtime valid
pointers, syscall return/abort behavior and extraction-to-native binding remain
explicit. No S4 file or candidate was changed.

`S2Z_OracleLimits` gives a formal interface counterexample: an op43 that always
diverges satisfies the successful-call predicate but fails the total predicate
at every supplied input. This is not a counterexample to shipped SolanaDigest.
It prevents silently using success-only interpretation to fill the total field.

Validation: host Lean001/002, one module per attempt, 6G high / 8G max / swap0 /
Tasks64; dependency objects reused, source/dependency/tool hashes, exact argv,
source revisions, wall/RSS/swap, complete axioms and reservation receipts retained.
All five added theorem reports use only propext, Classical.choice, Quot.sound.
No Rust/Kani/ELF or full-manifest replay: no shipped source changed.

Disposition: oracle **conditional**, with NativeBinding + runtime/P1 realization
and (for Required14) totality named above. No new trust item is adopted. The next
concrete deliverable is native op43/hashv/sol_sha256 admission/reification on the
same execution and its total-versus-VM-abort domain, supplied to these ports.
