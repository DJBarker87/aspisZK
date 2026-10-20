# Candidate 5: actual shared-point and final-relation consumers

Checked equality of the original and optimized computations, including decoder/index failures, mapped Parse errors, successful values, and divergence:

- `CuSavingsCanonicalDotClients.final_equivalence`: the actual `finish_relation` final-message `iter().enumerate()` dot loop. No canonical-input or loop-success premise.
- `CuSavingsCanonicalDotClients.partials_equivalence`: the actual four shared-point partials, each computed by the original 16-term field-reading dot source.
- `CuSavingsCanonicalDotPartialsCanonical.caller_context`: the partial-array source computation followed by any unchanged continuation using the high dot on any factor rows. This covers both high functional slots. Canonicality of every high-dot input is derived from actual row finishes, not asserted for arbitrary input records.

`high_equivalence` is an internal component with a canonical-array premise; `caller_context` discharges that premise using the exact partial builder. All final declarations use only `propext`, `Classical.choice`, and `Quot.sound`, besides the existing source runtime instance parameters. No new axiom, interpreter, candidate-equivalence premise, or production Rust change.

Source correspondence is checked by `check-canonical-dot-clients.py`. It regenerates byte-pinned source regions from candidate `e58b87665233febecc1b1a75c506eac1a8b72e00` and parent `d11f9b2fcbddf68fd1ffec297f987de0aa95a6c0`, verifies inverse lexical substitutions, and verifies promoted emitted bodies byte-for-byte after inserting the existing `Shared` binder and sharing byte-identical nominal carriers. The Error enum is shared through the field-stream module's audited alias to the identical original Reader Error enum.

The first exact nested partial-loop extraction (`canonical-dot-clients-aeneas-a`) failed at the producer's unsupported nested returns. The replacement lifts only the original constructor/inner16 loop/finish into a Result-valued row helper; expansion reconstructs the exact source bytes, and the added `?` is ordinary Result-bind factoring. The outer four source writes and all original inner error propagation remain. `canonical-dot-partials-{charon,aeneas}-a` succeeded. This is an explicit source extraction boundary, not a new trusted semantic premise.

The final selected integration replay is `canonical-clients-integration-1` through `-12`, after the shared Reader/KReader/FieldStream source dependencies froze. The earlier own-closure replay `canonical-clients-final-1` through `-12` remains historical evidence; the JSON report records exact commands, revision, features, exit, wall time, RSS, swap and axioms for each. Shared generic source-bound loop proofs are `CuSavingsCanonicalFieldStreamLoop` (receipt `canonical-field-stream-loop-f`) and `CuSavingsCanonicalFieldStreamCanonical` (`canonical-field-stream-canonical-a`), supplied by the profiling agent. The count guard bounds successful continuations even for an arbitrary cursor; no iterator termination premise is introduced.

No SBF build, CU measurement or production runtime suite was rerun for these Lean-only changes. This report establishes these consumer substitutions, not an additional CU saving or a whole verifier acceptance theorem by itself.
