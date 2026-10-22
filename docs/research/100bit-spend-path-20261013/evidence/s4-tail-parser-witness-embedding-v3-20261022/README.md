# S4 tail parser witness embeddings, term-linked whole trace

This source-only packet contains accepted Lean source, launch evidence, selected direct-import pins, and retained failed diagnostics. It contains no `.olean` binaries.

`S4TailParserWitnessEmbeddingV1.lean` proves `first_query_exact_embedding` and `contribution_exact_embedding` from the actual `FirstQueryInput` and `InputWitness`, respectively. Each uses the shared 608-byte opening equation and actual parser binding to identify the parser output with the encoded C1 tail or C2 lane. The source is compiled under a unique module name and imports the separately pinned fixed-array predecessor.

`S4TailRunTraceScalarEmbeddingV1.lean` proves `run_trace_scalar_embeddings` over one successful actual `RunTrace` for range 0..2. For each emitted contribution `c`, it returns a `termFin : Fin 2` with the explicit equality `termFin.val = c.term.val` and identifies the same contribution scalar with the corresponding C2 lane. The proof recovers each `InputWitness` and term bound from the trace; it does not assume an independent per-contribution read, parse, or slice fact. Attempt18's named axiom report is standard-only: `[propext, Classical.choice, Quot.sound]`.

Attempt18 is the accepted strongest whole-trace result: exit 0, 7.31 seconds, peak RSS 3,732,553,728 bytes, swap 0, launch revision `531175a515acdfd74de2873266db546ba49db4d1`, and Lean 4.32 compiler SHA recorded in `receipts/attempt18/`. Attempt16 is retained as a weaker successful theorem without the explicit term-index link; it is not the accepted whole-trace API. Attempt17 is a setup failure. Attempt12's same-name module shadowing is retained only as a rejected diagnostic.

The packet also pins the actual byte-window projections, current-QM slot embedding, fixed-array parser producer, and trace-membership helper. Their theorem-specific axiom output is retained in `receipts/byte-axiom-audit-v1/`. `check_packet.py` verifies source/object receipt pins, named axiom reports, no binaries, and rejects an accepted Lean source importing its own module name.

## Scope

These kernel-checked statements connect selected Lean parser and codec models to retained tail-loop witnesses and encoded C1/C2 values. They do not by themselves establish full S4 execution, Rust `std` extraction, deployment, or source-freeze closure. The downstream width-29 theorem remains a separate composition.
