# S6 concrete encoder reference totality — 2026-10-23

Status: S6 OPEN; target not yet established. This is pure Result totality,
not full source/runtime/SDK correspondence, accepted round-trip, or soundness.
Authoritative source freeze remains 25866ec331cc7ce27dd9956609c11d32fa8fa58a.
No production verifier changes. S2 belongs to the transferred owner.

## Enclosing obligations established

`S6SourcePaymentValidatorTotalV1` proves both concrete payment validators total.
`S6SourcePaymentCommonEncodeTotalV1` proves the complete common writer total;
`S6SourcePaymentEncodeTotalV1` proves both concrete payment writers total.
These install the actual concrete digest and validator implementations rather
than independent successful-child hypotheses.

`AspisS6AfterstateLoopParent.Total.encode_total` proves the complete 688-byte
encoder reference total on every full native afterstate, including validation
errors. `AspisS6SnapshotLoopParent.Total.encode_total` proves the complete
snapshot encoder reference total on every full native snapshot and arbitrary
mutable output slice, preserving its length on success and error. Neither
statement assumes canonicality or successful children. The Rust Result may
contain an error: totality does not assert acceptance.

The former unrolled proofs exceeded default Lean recursion depth. No resource
option was raised. The replacement isolates one actual frontier write and
proves the complete twenty-step loop by remaining-count induction. Native Kani
checks compare the original frozen foreach with the reference helper loop on
full native carriers, arbitrary initial buffers and a symbolic output byte:
205 checks each for snapshot and afterstate. Only the previously verified
concrete digest encoder is stubbed. Mutable snapshot Slice semantics, full
native structures and all error variants are retained.

The enclosing snapshot/afterstate source references replace only the frontier
loop fragment. Extraction leaves are concretely installed from the complete
source codec and validators. `frontier_eq` identifies the extracted parent loop
with its separately proved helper. No arbitrary Ops interface remains.

The lane-transition enclosing source `S6LateParentSourceV1` also compiles with
both concrete encoder references and the actual extracted std Option method.
`AspisS6LateParent.Total.encode_total` is now accepted (v9): total for every
full native statement and output slice, with output length retained and no
child-success premise. Focused check: exit0,22.783060s,2274344960 bytes RSS,
zero swap, standard axioms only.

## Evidence and trust boundaries

Evidence is under `evidence/s126-current-caller-20261021`:
`s6-owned-frontier`, `s6-afterstate-loop-parent`, `s6-snapshot-helper`,
`s6-snapshot-loop-parent`, `s6-late-parent`. Each includes source-only native
inputs, exact extraction/source/tool hashes, admissions and resource receipts.
Some cloned runner captions say afterstate on the snapshot attempt; the actual
harness, pinned inputs and command identify the snapshot scope. An initial
snapshot parent setup selected the wrong source file and failed its fragment
assertion before any compiler launched; corrected extraction uses v2.

`s6-encoder-total-targets.json` selects only successful current-source receipts;
`s6-encoder-total-import-pins.json` hashes their compiled dependency closure
without distributing binaries. Every receipt records target, revision,
source/tool/import hashes, command, exit, wall, RSS, swap and axioms. Local Lean
used the atomic lock, -j1 and -M4400. Native frontier jobs used High3G/Max4G,
extraction High1G/Max2G, MemorySwapMax=0 and fresh admission. All accepted
Lean audits contain only propext, Classical.choice and Quot.sound.

Failed proof attempts and raw external templates are diagnostic evidence only.
Any sorryAx in a failed elaboration report is excluded; no admitted declaration
is installed in an accepted target. The scanner is
`tools/s6-full-forest-roundtrip-20261023/check-encoder-total.py`.

## Exact remaining work

- Complete the full 1880-byte encoder/decoder composition and accepted inverse.
- Prove contextual transport of the verified loop transformations and prior
  validation/codec references to the frozen source, including error/state
  behavior required by the enclosing execution.
- Connect decoded public reuse through actual first/first_decoded and SDK stage1,
  allocation/Vec/account effects and actual caller/trace. Pure Result totality
  does not discharge those premises.
- S1 still needs original native whole prepared_claim/caller connection with the
  actual Std/P6/runtime instance. Existing borrowed-ABI preparation/power and
  joint challenge-trace results are retained, not claimed as whole S1 closure.

Any candidate adoption needs equivalence/contextual gates and explicit source,
artifact and proof re-pins. The frozen release has not been silently replaced.
