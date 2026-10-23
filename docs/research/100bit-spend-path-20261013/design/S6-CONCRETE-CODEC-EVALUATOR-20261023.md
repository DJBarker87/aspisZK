# S6 concrete complete codec evaluator — 23 October 2026

S6 and S1 remain OPEN. This packet constructs the complete value-source codec
reference with no free child operations and proves the listed local totality
and enclosing control results. It does NOT prove the full accepted 1880-byte
roundtrip, whole encoder/decoder totality, stateful public Vec provider or
actual first/first_decoded/stage1 join. No production source changed.

## Concrete evaluator and source boundary

`S6FullSourceCodecV1`, namespace `AspisS6SourceCodec`, defines complete
`encode : Statement → Result (RustResult (Array U8 1880) FormatError)` and
`decode : Slice U8 → Result (RustResult Statement FormatError)`. Statement is
EXACTLY the complete native Charon type in `S6FiveCodecTypesV1`, including both
variants, all common/live-snapshot/frontier/payment fields. There is no new
statement/account carrier, admission subtype, ghost runtime state or supplied
encoder/decoder/validator operation. The actual codec/validation bodies remain
present. Ordinary errors and outer Result failure/divergence are retained.

The authoritative freeze remains `25866ec331cc7ce27dd9956609c11d32fa8fa58a`.
The complete extraction reference has the five separately checked loop
transformations documented in S6-FULL-FOREST-NATIVE-20261023.md: digest writes,
snapshot and afterstate frontier writes, and their two validation scans.
The native Kani checks retain complete types, error variants and caller-sized
frames. **Whole contextual transport to the original frozen path remains an
explicit obligation.** No adoption or release artifact re-pin is inferred.
Any adoption requires that equivalence, affected source/ELF/SBF/cone pins and
integration/performance gates. No source decision is requested prematurely.

The core field source actually used by the external dependency matches the
freeze byte-for-byte: SHA256
`28df5a1abee13bde4b3aa9eeceb0489bedf00531f298460954a97661f5f1baea`.
`s6-concrete-core-freeze.json` associates that file with the predecessor's
all-local-before inventory. Statement Rust pins/five changes are in the
predecessor source packet. Workspace-normalized Cargo version/path changes
and feature r0 are build inputs, not a new protocol freeze. The host receipt's
workspace revision is not substituted for these exact source pins.

## Standard-library installation

The prior complete model exposed three generated external-template entries.
Two are now actual extracted generic Rust bodies: Option.ok_or and Option.eq.
Focused Charon/Aeneas extraction of those methods emits no external template.
The backend omitted the required Option discriminant instance; the supplied
None0/Some1 isize definition is checked directly against the current LLBC enum
metadata. No axiom, output hypothesis or successful-call premise is added.
`materialize-std-options.py --check` reproduces the exact checked source.

The third template, Slice/array equality, has **zero references in the emitted
function bodies**. `materialize-five-codec.py` asserts this before emitting
the concrete evaluator. This is not an opaque replacement: no declaration
or arbitrary implementation for that unused template is imported. Actual
used array/slice comparisons remain the existing Aeneas standard-library
models. `S6StdByteArrayTotalV1` proves the byte-array model total by symbolic
List.allM induction, not concrete byte enumeration or native_decide.

The before/after SOURCE INTERFACE is explicit: the historical outer model
has nine arbitrary codec/validator children; the complete intermediate model
has three external-template fields; `AspisS6SourceCodec.encode/decode` have
no child-operation arguments. Input/output/error carriers are unchanged.
This is not advertised as a completed premise removal from the final
soundness/caller theorem: its full roundtrip and stateful source joins remain.
The extraction trust boundary is the existing Charon/Aeneas boundary; lead
D188 (`850662c263`, research LOG) explicitly records that project convention.
That ruling does not discharge the five source transformations or runtime joins.

## Proved results

- `S6FullSourceCodecRangesV1`: TOTAL evaluation of the native size expression
  to1880; exact WrongLength rejection on every wrong-sized input; accepted
  decode derives the original input length1880 from the same call.
- `S6FullSourceCodecEncoderControlV1.encoder_control`: complete Result
  factorization through the ACTUAL closed full validator. Rejection preserves
  its exact error; `encoder_success_validates` derives actual validation success
  and the SAME continuation/output from one accepted encoding. No free validator
  callback or independent child-success premise remains in this statement.
- `S6SourceDigestTotalV1`: exact equality to the previously checked eight-write
  reference and TOTAL encoding for arbitrary eight raw native words.
- `S6SourceWordInverseV1`: TOTAL native four-byte field decoding (including
  noncanonical none) and ACCEPTED-ONLY recovery of all four original bytes,
  reusing the checked generic u32 byte inverse without a canonicality premise.
- `S6SourceCanonicalTotalV1.scan_total`: TOTAL unmodified native canonicality
  scan, using remaining-index induction over eight arbitrary raw words.
- `S6SourceSnapshotValidatorTotalV1.snapshot_total` and
  `S6SourceAfterstateValidatorTotalV1.afterstate_total`: TOTAL reference
  validators on the full native records, including all twenty entries and
  malformed-input Rust errors. No canonical-input or child-success premise.

These local TOTAL results are not whole S6/R22 totality. Arithmetic bounds in
those declarations are discharged by the source loop measure, native array
extents and checked scalar operations. Allocation/abort/SDK traces are not
manufactured by pure Result statements.

## Validation and excluded work

Focused Lean4.32.0 targets ran serially under the atomic local lock with
-j1 -M4400 and warm imports. No cold package build, resource override or
package/frozen-manifest replay ran. All accepted audits are standard or empty and all
accepted process swaps are zero. Exact source/tool/import/object hashes,
commands, exit, wall, RSS and multiline axioms are in the receipts indexed by
`s6-concrete-codec-targets.json` and the transitive import inventory.

| Target | Exit | Wall s | Peak RSS bytes | Swap |
|---|---:|---:|---:|---:|
| S6FiveCodecNativeV1 | 0 | 10.136204 | 2468462592 | 0 |
| S6FiveDigestTotalV1 | 0 | 12.363174 | 2232582144 | 0 |
| S6StdOptionSourceV1 | 0 | 14.873053 | 2226618368 | 0 |
| S6FiveCodecStdOptionsV1 | 0 | 9.444092 | 2222784512 | 0 |
| S6FiveWordInverseV1 | 0 | 14.692106 | 2235990016 | 0 |
| S6FullSourceCodecV1 | 0 | 7.676194 | 2421653504 | 0 |
| S6FullSourceCodecRangesV1 | 0 | 14.771667 | 2208497664 | 0 |
| S6FullSourceCodecEncoderControlV1 | 0 | 2.527744 | 2260647936 | 0 |
| S6SourceDigestTotalV1 | 0 | 15.057716 | 2233696256 | 0 |
| S6SourceWordInverseV1 | 0 | 2.382559 | 2244018176 | 0 |
| S6SourceCanonicalTotalV1 | 0 | 2.620499 | 2271739904 | 0 |
| S6StdByteArrayTotalV1 | 0 | 32.659511 | 2150416384 | 0 |
| S6SourceSnapshotValidatorTotalV1 | 0 | 17.689311 | 2235809792 | 0 |
| S6SourceAfterstateValidatorTotalV1 | 0 | 15.474469 | 2262106112 | 0 |

The formatter-only tool repair changes margin80→1000 and maximum indentation
to999. Its warm optimized build used an admitted High1G/Max2G/Swap0 scope,
7.244596s and573767680bytes cgroup peak. The same LLBC rerender used
High6G/Max8G/Swap0:59.848s,3368112KiB RSS, exit0. Source content after stripping
comments/metadata/whitespace is identical. Four emitted monadic constants
reuse their original narrow layout with identical tokens; top-level declaration
indentation is normalized. No translation rule or Rust body changed.

Focused std Option extraction: Charon0.155s/125136KiB/exit0, Aeneas0.427s/
60720KiB/exit0, swap0. Aeneas ran High128M/Max256M/Swap0 after a fresh admission;
the earlier generic-std predecessor measured58960KiB. Full std-template
experiments retain a pattern-parse failure, corrected Charon result and
admission refusals. Generic slice/array extraction hit unsupported PtrMetadata
and is EXCLUDED; it is not used as a verified summary. The unused-template
finding makes that extraction unnecessary for the concrete codec.

Two focused dispatches (native-v4/v7) accidentally ran the preceding failed
source after a materializer preflight failed; both are excluded, and later
compiles were dispatched only after checking preflight success.
Failed Lean materialization/layout attempts and compiler recovery sorryAx
reports are EXCLUDED. An optional whole Result agreement audit against the
older abstract model hit the default recursion limit. Small function equalities
checked, but frontier cases still fail even with named contexts; no complete
agreement theorem is accepted and no resource option was raised. Those attempts
are retained separately and are not counted as enclosing security closure.

## Exact remaining obligations

1. FullForestAcceptedRoundtrip for the complete concrete evaluator, with both
   variants, all1880 bytes, reserved fields and rejected/noncanonical paths.
2. Complete encoder/decoder and remaining child totality, beyond the local
   word/digest/scans/two validators above.
3. Contextual transport of the five checked native loop transformations to
   the enclosing frozen source, plus any required adoption/re-pin gates.
4. Actual stateful full-forest Vec provider and first/first_decoded/stage1
   composition, including actual tx1/SolanaDigest, observer None, account/owner/
   capacity frames, ordered error/log/oracle/allocation prefixes and aborts.
   S2 remains with its new owner; its tracks are untouched here.
5. S1's original whole native claim loop connection and actual remaining
   Std/P6/caller installations described in S1-BORROWED-CLAIM-CALLER-20261023.md.

No enclosing soundness boundary or100-bit headline is marked closed.
