# Actual fixed-input decoder bank

The executable bank runs 29 initial and 2 final maintained GS decoders. All input arrays are supplied before the extractor randomness. The initial calls share one field-pair tape, and the final calls share another: a finite union bound needs no independence between calls when the inputs are fixed before those tapes. At 149 retries, the actual bank's combined abort mass under uniform field-pair tapes is strictly below 2^-127.

This reuses the actual interpolation/state/root-recovery contracts. It is not a bound for adaptively chosen received words after seeing extractor randomness. The completed-log to fixed-input constructor, finite-byte tape coupling, message-list completeness, spend-witness recovery, protocol/ROM composition and source/runtime correspondence remain open. The new generic finite-bank proof factors the algebra before instantiation, avoiding concrete decoder normalization. Failed earlier local attempts remain diagnostics and are not passing evidence.

Focused Lean 4.32 checks only; each retained receipt pins source, imported objects, command, revision, exit status, wall time, RSS, swap and printed axioms. Standard axioms only. This is not the full 100-bit soundness theorem.
