# S4 concrete width-29 callback kernel

This packet proves the value equation for one successful `LiteralFieldResult` under the selected concrete kernel Ops. It derives the 26 head terms from the C1 projection, the first C1 parser embedding, the trace-indexed C2 parser embeddings, and coefficient powers from the very same callback trace. The result is the exact `width29Batch` over the `localWord` at the fixed literal lane index zero.

The public theorem is `AspisR1D18S4ConcreteWidth29KernelV1.literal_field_result_concrete_width29`. Its `hresult` type is exactly `LiteralFieldResult (literalOps concreteOps) a g slotU value`, matching the per-slot field-result parameter emitted by `S4ConcreteKernelOpsRootV1.original_four_total_and_field_results`; no adapter law is needed for this premise. Candidate query field evidence uses the same proposition after instantiating the same array and slot.

The upstream opening byte equality and all 29 power equations remain explicit. The theorem is a typed concrete-kernel result, not a full accepted caller or Std `from_fn` source refinement. The source and object hashes, direct object pins, complete selected LEAN_PATH, command, time/RSS/swap log, and axioms audit are retained. No `.olean` is copied into this packet. Launch HEAD was not captured by the runner; packaging-time HEAD is reported only as context.
