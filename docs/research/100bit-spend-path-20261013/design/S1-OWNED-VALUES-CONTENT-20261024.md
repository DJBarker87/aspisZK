# Value codec content and actual preparation domain

Target not yet established. This is an addendum to
`S1-OWNED-VALUES-CALLER-20261024.md`, not frozen S1/S6 or SDK closure.
No production source, wire format, error carrier or security contract changed.

## Concrete progress beyond the previous packet

The unchanged native **1856-byte input / 3712-byte output** positive case now
passes against its exact byte formula: all 251 checks passed (5 unreachable),
31.673 seconds, 1476816 KiB peak RSS, swap 0. There are no stubs. Full input and
initial output arrays are arbitrary; a symbolic watched index quantifies every
output byte. Complete codec result is `Ok(())`; source input is read-only.
The existing failed 181.810-second native-v5 dual-execution attempt is retained.
It was not rerun unchanged or with a larger cap. The native-v6 gate executes only
the unchanged native function; the reference's nested Vec loops are proved
against the same formula in Lean instead of re-executed in CBMC.

This closes the previously missing **valid-dimension positive primitive**
correspondence at the largest format shape by composition of the two artifacts.
It is not an unbounded native length-rejection theorem or a theorem connecting
all primitive occurrences to actual SDK execution. Kani is not represented by a
Lean custom axiom. The Rust model-checker/compiler and Charon/Aeneas translation
boundaries remain explicit trust boundaries, with their exact source/tool pins.

## Exact full-buffer Lean result

`S1ValuesOwnedCellV1` proves the actual emitted read value and returned setter.
`S1ValuesOwnedStepBytesV1.step_bytes` proves both writes and every untouched byte
of one actual source step. `S1ValuesOwnedChunkBytesV1.chunk_bytes` composes these
through the actual inner Std.loop, and `S1ValuesOwnedExpansionBytesV1.loop_bytes`
composes the actual outer Std.loop. Both use the previously checked loop
invariant transport, not a simplified loop or concrete large-buffer reduction.

`S1ValuesOwnedReferenceBytesV1.reference_bytes` proves from the SAME complete
reference call returning `Ok(())`:

* Exact input retention and output-length preservation.
* Actual output length equals twice input length; input alignment is derived.
* For every valid output index `j`, output is input at
  `(j / 32) * 16 + j % 32` when `j % 32 < 16`, and zero otherwise.

Neither alignment, output-size equality, child execution, desired byte equality
nor a successful loop is an independent premise. It is ACCEPTED-ONLY.
`S1ValuesOwnedExactV1.reference_success` separately supplies TOTAL successful
codec execution from aligned dimensions, matching output length and the checked
doubling bound. `installed_exact` gives the same formula for the installed full
reference. The previous totality theorem includes malformed-dimension errors.

## Enclosing caller, not a free codec invocation

`S1PrepareCodecCallsV1.prepare_codec_calls` strengthens the full actual current
prepare success decomposition to retain both reached codec calls and downstream
View/semantic/Prepared calls. It needs **no length law** or chosen intermediate
outputs. Existing parser and original preparation proofs are reused unchanged.

`S1ValuesOwnedPrepareY1V1.prepare_y1` instantiates that same full preparation at
`NativeBuffers.install (withValues ops) nativeValues R B`, deriving:

* Actual source input range proof `[7031,7495)` and its length 464.
* Its same successful installed expansion, with initial and returned lengths 928.
* The exact byte formula for all 928 expanded bytes.
* The same downstream View, semantic verification, Prepared output and scratch.

The two offsets come from installed frozen constants and checked additions;
range length comes from the actual accepted slice operation. Initial output
length is derived from this reached codec's own success, without assuming an
allocation-length law or projecting away the allocation error branch.
This eliminates the independent Y1 size witness at the reference caller.
Native transport for this reached **positive domain** can therefore consume the
existing unchanged 464/928 native gate. It does not establish rejected-prefix
transport or all native semantic value-call domains automatically.

`S1ValuesOwnedStage1Y1V1.owned_stage1_y1` carries this result through the SAME
accepted owned adapter stage1, retaining the decoded complete public statement,
source prepare on release `None`, scratch, both physical roots and the checkpoint
continuation. Actual native SDK/account association remains open; the model is
the complete owned adapter reference, not an opaque or reduced SDK carrier.

## Remaining premises and source decisions

The displayed enclosing theorems retain exactly the earlier caller's `ops`,
`RoundModel.Boundaries R`, `FinishModel.Boundaries B`, full digest/hash/public,
proof bytes, scratch and enclosing success; the owned stage1 theorem also retains
its full `AdapterRw.Ops`, program, accounts, instruction bytes and output.
No native source equality or SDK execution hypothesis has been silently folded
into a structure or discharged by naming it.

Still open: native source rejected-path/metadata transport; source domains of all
semantic value calls; actual whole prepared_claim loop/reference and primitive
associations; original powers-from_fn equivalence or explicit candidate adoption;
complete challenge/query-state trace; full serialized Prepared/checkpoint field
binding; and S6 native SDK/account/effects/abort-prefix/caller retention. S2 stays
with its new owner. Full <=2^-100 per-attempt soundness remains unestablished.

All new Lean validation is focused, one job at a time, atomic lock and
`-j1 -M4400`, with standard axiom audits. Native-v6 used fresh admission,
MemoryHigh=6G/MemoryMax=8G/MemorySwapMax=0 and optimized Rust. Source-only receipts,
commands, import/source/tool pins and the old failures are archived. No binary,
LLBC or compiled object is shipped; no unchanged full replay was run.
`tools/s1-y1-source-20261024/check-content.py` checks the selected evidence.
There is no adoption request in this packet; production adoption would require
explicit equivalence/integration gates and release source/artifact re-pins.

Selected successful Lean targets: 12; total wall time 168.880s; maximum RSS 3832922112 bytes; swap 0.
