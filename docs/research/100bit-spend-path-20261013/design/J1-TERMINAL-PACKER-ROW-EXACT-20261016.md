# Actual packer and selected matrix row reach the model

The actual generated four-input QM31 packing function now has a checked
success, canonicality and model-correspondence theorem. The proof follows the
source's array copy, checked U64 operations and reducers, then reuses the
concrete QM31-to-WideExact map and basis theorem to reach `R0P.pack4`.
Its only input conditions are a slice of length four and canonical inputs.

The actual candidate Poseidon row wrapper now reaches `R0P.poseidonMat4`.
The theorem accepts arbitrary fixed U32 word arrays and a row index below four;
it derives successful execution and canonical output. Symbolic linearity bridges
the already checked raw-word row formulas to the field model. This is not yet
the entire matrix layer, permutation, selector or terminal caller.

[The evidence](../evidence/terminal-packer-row-exact-20261016/README.md) records
15 successful focused targets, 37 clean axiom reports, zero process swaps,
and an independent audit of source/object pins, exact generated declarations
and prior dependency results. Thirty-four failed compiler attempts and one
source-only preflight remain recorded separately. No unchanged broad replay
was run. The final packer uses explicit source-zero initialization rather
than the separately checked generic-default helper.

This closes two concrete producer obligations needed by the preceding
selected-claim/fold composition. Remaining work includes the actual gathers,
selectors, semantic and copy lane producers, complete terminal execution,
and their source-to-protocol connection. The complete 100-bit per-attempt
soundness and private spend claims remain open.
