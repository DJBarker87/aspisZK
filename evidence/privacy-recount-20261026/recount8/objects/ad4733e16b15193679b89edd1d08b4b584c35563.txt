# Foreign metadata extraction review

The pinned Charon source sets mir_opt_level=0 and mir_preserve_ub=true
(charon/src/bin/charon-driver/driver.rs:set_mir_options). Its CLI documents
that optimized local MIR still has optimizations disabled. The inlining
flags on earlier attempts did not cause records to be inlined.

A normal optimized nightly-2026-06-01 build of the exact source, with
always-encode-mir, mir-opt-level=4, inline-mir=no, makes foreign MIR
available to the unchanged pinned Charon. No shipped file, extractor
binary/source or shared infrastructure is modified by this route.
The first foreign metadata translation has_errors=true from unrelated
core Iterator trait bodies and is REJECTED despite process exit 0.
The restricted core/alloc translation requires the real Option/Range types;
adding their include patterns yields has_errors=false.

Aeneas06 process exits 0 but translation.json contains NO implemented
records function. It emits only ZERO8 plus type definitions and two
external templates. It is REJECTED as R_shipped. These are quarantined
raw generator outputs, never imported or accepted as proof declarations.
The user's target is not established. The earlier commentary overstatement
was corrected as soon as this output was inspected.

The cause is Aeneas PrePasses.remove_read_discriminant:simplify calls'
used-function pruning: local definitions are roots, while an unreferenced
foreign definition can be dropped. The next extraction includes the
unchanged direct caller CopyRecords::new as a second starting point so
records is referenced by an actual source body. This is an extraction
configuration change; it does not change the source or manually edit LLBC.

Including the direct foreign caller retains records. Aeneas07 then fails at
exactly records230/InterpAbs1955; metadata optimization is not evidence that
the borrow obstacle disappears. Owned adapter metadata (explicitly cfg-only,
no mapper transcription) also still calls records and fails identically at
Aeneas08. Raising the separate forwarder/hint inlining thresholds produces
another clean LLBC but still retains a separate records body. No success is
inferred from these process exits or unexecuted output.

The smallest proposed source change to address this new obstacle is the
single-line pair-borrow-proposal.diff (NOT APPLIED). PoolV1PairInputNoteWitnessV1
is explicitly Copy in pair_trace.rs:71. This proposal changes a local shared
borrow to a Copy value, preserving values/order and the public signature.
The current owner prompt explicitly authorizes only closure replacements,
so that additional line requires a new lead ruling. If authorized, commit
it separately and rerun all three ELF pins immediately before proof work;
stop on any mismatch. The closure-only edit is retained unchanged meanwhile.
