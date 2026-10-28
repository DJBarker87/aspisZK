# op53: observable effect exceeds Result Unit

Frozen source 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387,
programs/r1-cost-probe/src/r1_pool_adapter.rs, emit_result (915–943), has
`program::set_return_data(&encoded); Ok(())` after its encoder/validation gates.
The coherent AdapterRw.Ops.op53 type is Statement → Result (Result Unit
ProgramError). The call occurs at AdapterRwModel line3425 with val.statement.
NBX_SOURCE_ASSOCIATION.json pins complete source excerpts and all callers.

Under ruling (s)’s literal frame “no writes outside the returned value”,
op53 cannot be marked instantiated: the returned Unit does not carry the
runtime return-data update. This is an interface/effect obstruction, not a
finding about ASR8’s encoder correctness and not a shipped Rust vulnerability.

No trust item or dictionary law is added. No altered SDK, suppressed syscall,
or successful encoding premise repairs the mismatch here. The lead must
identify an existing extraction/runtime observation quotient which excludes
that return-data state, or supply a separately authorized effect interface.
This worker does not change the headline/extraction carrier or contract.

ASR8 body fidelity remains outside soundness scope. The requested K050 negative
control is still useful independent local evidence, and is scheduled last.
