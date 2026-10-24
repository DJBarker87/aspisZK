# Complete owned value expansion in the preparation caller

Target not yet established. This packet removes the value-length premise from
concrete **owned-reference instances** of the preparation and owned stage1
physical-root theorems. It does not close frozen S1, S6, SDK/account execution,
or the probability theorem. S2 remains transferred to its new owner.

## Before and after

Before, `NativeBuffers.prepare_physical_roots` and
`NativeBuffers.owned_stage1_physical_roots` required

```lean
∀ input output status updated,
  ops.op11 input output = ok (status, updated) →
  updated.length = output.length
```

After, `AspisS1ValuesOwnedInstallation.prepare_physical_roots` and
`owned_stage1_physical_roots` have no such premise. Their full successful
caller execution uses `NativeBuffers.install (withValues ops) nativeValues R B`.
The complete owned reference is installed at **both** value-expansion call
sites: Y1 op11 and the value leaf inside native semantic expansion. All input
and output bytes, error variants, other caller ports, original preparation
scratch, release observer `None`, public decoder, and continuation are retained.
The same two roots remain physical proof byte ranges `[16,48)` and `[63,95)`.
`AspisS1ValuesOwnedInstallation.writer_physical_roots` removes the same premise
from the lead writer-prefix instance, retaining its batch/geometry/query/finish
ports, reservation outcome, digest, hash, public, proof, split and accumulator.

This is a concrete instance change, not a proof that the arbitrary old
`ops.op11` satisfies its law. In particular, native/reference transport on the
reached source domain is still required before applying this result to the
frozen implementation. The new theorem does not assume that desired transport.
The previous unchanged-native semantic expansion and parser proofs are reused.

## Complete reference and totality

`tools/s1-y1-source-20261024/owned-v3.rs` owns complete input and output Vecs.
Both buffers move through read/write/chunk helpers; no simplified carrier or
opaque operation replaces the body. Charon and Aeneas both succeeded.
`S1ValuesOwnedModelV1` retains the emitted operations, guards, checked arithmetic,
nested loops, and all codec errors. The adapter only shares the complete codec
type, retargets imports and removes generated resource defaults; the raw emitted
source is archived as `.lean.txt` and is not compiled with those defaults.

`S1ValuesOwnedFrameV1.reference_frame` proves, for every successful outer return
and **any codec status**, exact input retention and output length preservation.
It is ACCEPTED-ONLY and does not imply termination.

`S1ValuesOwnedTotalV1.reference_total` separately proves TOTAL execution for all
complete input/output contents and dimensions satisfying
`2 * input.length ≤ Usize.max`. Alignment, output-size equality and codec success
are not premises. Malformed dimensions retain the actual Length rejection.
`chunk_step_total` discharges both low/high write ranges and all checked
arithmetic; inner and outer loops use symbolic decreasing-count inductions.
There is no concrete large-buffer normalization. Allocation/reservation,
capacity and native SDK borrow effects are not proved by the Vec content model.

## Native correspondence evidence and retained failures

All native cuts preserve the exact frozen `expand_values` function and complete
CodecError enum. Positive gates use no stubs. For arbitrary full initial arrays
and symbolic watch indices, **native-v5** checks compare codec result, both
returned lengths, every input byte and every output byte:

| Input/output bytes | Result | Wall seconds | RSS KiB | Swap |
|---|---|---:|---:|---:|
| 16 / 32 | PASS | 3.187 | 300608 | 0 |
| 448 / 896 | PASS | 33.445 | 1998424 | 0 |
| 464 / 928 | PASS | 35.233 | 2077796 | 0 |
| 1856 / 3712 | TIMEOUT, no theorem | 181.810 | 6534536 | 0 |

Each passing gate reports 0 of 480 checks failed, 5 unreachable. The timeout is
not a counterexample, nor accepted evidence. Next native task is a symbolic
chunk/iterator transition plus composition for the claims-sized call, not an
unchanged whole-function retry with a larger cap. Lean caller-domain transport
is also still needed for **all** sizes, including the three passing gates.

Earlier failures are retained under `s1-y1-source`: native-v1/v2 symbolic-length
rejection checks timed out; array-reference extraction-v1 failed borrow collapse;
helper-array native-v4 equality timed out. The replacement complete Vec reference
extracted successfully in extraction-v3: Charon 0.182s / 156288 KiB and Aeneas
0.365s / 69872 KiB, swap 0. Native-v3's bounded rejection check uses a checked
panic cut at `chunks_exact` (reaching the cut fails verification), not a silent
assumption; it passed with both requested edge lengths covered. That historical
bounded result is not an unbounded native metadata or caller theorem.

## Source and tool pins

`evidence/s126-current-caller-20261021/s1-values-owned-freeze-assessment.json`
checks exact `compact.rs` SHA-256
`adcd99bdedda8ecdb250fb810ad9bcd263ce80a2c6cb6e7d2d3777587dabb9b7`
at the authoritative b2727acd freeze, the 25866ec research freeze, our parent
revision, and observed research 19058d5320. This establishes codec-file identity
only, not whole-source/SDK/ELF equivalence or adoption. Production Rust is unchanged.

The source-only receipts include exact commands, tools, source/import hashes,
exit status, wall time, RSS, swap and axiom audits. Local targets use the atomic
Lean lock, `-j1 -M4400`, one at a time. Heavy gates use fresh host admission and
MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0. Actual optimized Rust flags are pinned
in compilation fingerprints. No binaries, LLBC, object files or compiled caches
are distributed. `check.py` validates the selected evidence without replaying
unchanged proofs; import pins identify the selected cached dependency closure.
The 13 selected successful local targets took 239.500 seconds in total,
with peak RSS 3966500864 bytes and swap 0. This is not a coherent release replay.
Accepted Lean declarations report only
propext, Classical.choice and Quot.sound, or no axioms for the type alias.

## Exact remaining obligations

* Native/reference correspondence for the 1856/3712 call and composition of the
  native iterator, including all rejected paths relevant to the enclosing claim.
* Derive actual reached dimensions and preserve source execution/error/state
  semantics when transporting the reference caller instance back to native.
* Other `ops : AspisR1CurrentCaller.Ops` ports and the full
  `RoundModel.Boundaries R` / `FinishModel.Boundaries B` remain quantified exactly
  as in the displayed theorem statements. They are not discharged by this packet.
* Actual native whole prepared_claim/reference loop and primitive associations;
  native powers-from_fn equivalence or explicit adoption of the isolated powers
  candidate; actual complete challenge-state/query connection.
* Full Prepared/checkpoint field binding, beyond the two physical root ranges,
  to the lead's committed-root and serialized-field model.
* S6 actual SDK/account/effects/abort-prefix connection and caller input retention.
  Decoded-public reuse in the owned caller is retained, not promoted to SDK closure.

No security contract, wire format, verifier source or release artifact changed.
No source adoption is requested by this packet; adopting a candidate would require
explicit equivalence, integration and release re-pin gates.
