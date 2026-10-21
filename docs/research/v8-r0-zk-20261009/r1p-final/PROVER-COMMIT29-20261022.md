# Prover commitment part 29

Branch `codex/cx-prover-commit29-20261022`; inherited revision `6a86aa5dc`.
Endpoint comparison base `26b922be6`. Target not yet established.
Env J 7840–7999 only, skipping every existing receipt.

## Stage 1: owned native semantic iteration

The cfg-only `sim::owned29::semantic_step` owns the incoming transcript,
record and semantic array. It calls the retained P6 `semantic20::semantic`,
with its `fields20` owned validator, then maps errors and writes the sampled
array cell. The unchanged shipped iteration remains the comparison target.
The two retained helper modules are now present under cfg(kani)/cfg(aeneas_ref)
in `r1_wire.rs`; production configurations do not include them.

`step29-owned-v3` extracts the entire owned reference with **no opaque cut**:
Charon exit 0, 33.952 s, 577660 KiB RSS; Aeneas exit 0, 1.281 s,
116336 KiB RSS; both zero swaps. The earlier direct-native-callee reference
failed in `InterpReduceCollapse.ml:1991` while translating the borrowed field
validator. `step29-v2` cut that validator and succeeds, but is excluded as a
completed native semantic refinement. V3 replaces that route with the retained
owned semantic reference, rather than asserting the opaque validator correct.

`port-step.py --check` compares all 25 reused extracted definitions with the
retained semantic namespace and retains the new owner body exactly, apart from
the nominal verifier Error namespace. One dependency has the raw generator's
`32#i32` shift operand where the pinned library requires `U32`; the retained
`32#u32` annotation is used. `shift_count` audits the equal nonnegative numeric
operand. The raw generated text is retained; it is not represented as compiling
unchanged against the older shift signature.

J7840 compiles the extracted owner port. J7842 proves `extracted_step`, the
numeric annotation check, and `iteration_effects`, installing the concrete
oracle machine. Exit 0, 1.87 s, 4132272 KiB RSS, zero swaps; all three axiom
reports are `[propext, Classical.choice, Quot.sound]`. J7841 is an excluded
failed diagnostic, not an accepted proof. No source-to-model claim is inferred
from the reference alone.

The no-stub empty-record Kani preflight was stopped after pathological symbolic
sampler expansion. Its receipt is retained. The replacement uses an arbitrary
shared sampler result, checks equality of both sampler inputs and call counts,
and separately replays every ordered Digest32 call and answer. The empty-record
replacement passes (1762 checks; 7.131 s total, 533792 KiB RSS, zero swaps).
This is still just a preflight: the all-record check is pending.

The shipped-file gate rebuilt default, devnet and pool from a separate exact
tracked-source snapshot after the cfg additions. All are byte-identical to
the frozen artifacts: respectively `dfc2a91a…`, `fb2fc048…`, `121f3e29…`;
full hashes, sizes, `cmp` status, command, cap and resource receipts are in
`frozen-elf-final-check.json`. The first build hit the 64-task limit before
four-CPU affinity was applied; the next found an incomplete workspace snapshot.
Both failures and their environment/snapshot fixes are retained. Final builds
exit 0 in 6.066/2.305/0.363 s, peak RSS 203936/204000/100816 KiB, zero swaps.
No cap was raised. Build time was optimized compilation/linking.

Pending: complete per-iteration Kani gate, finite-row induction, native walk
composition, shipped experiment and both WholeRunJoins. No refinement premise
has been removed. Target not yet established.
