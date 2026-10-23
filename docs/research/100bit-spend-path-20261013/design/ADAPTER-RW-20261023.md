# Adapter owned caller candidate — 23 October 2026

Status: STAGE 1 DESIGN; ADOPTION CANDIDATE, NOT ADOPTED.
Branch: `codex/cx-adapter-rw-20261023`.
Evidence: `../evidence/adapter-rw-20261023/`.

## Contract and decision point

D182 authorizes replacing the two callers, not weakening their behavior.
The requested contract is identical accept/reject on every input, identical
ProgramError values, return data, checkpoint bytes and all account effects.
This contract is NOT established by this note. Entry copies introduce new
allocations and change borrow admission/lifetimes; unrestricted equivalence
must not be asserted. The exceptions below require explicit approval before
implementing a candidate that depends on them. No exception is adopted here.

The source currently requires distinct keys, not distinct Rc data cells, and
S2TrustedSdkBorrow explicitly permits aliases and arbitrary valid counters.
A raw SDK input domain is broader than a runtime invocation with initially
zero counters and independently backed distinct account keys.

## Proposed shape

Keep instruction/count and account metadata admission explicit. At the entry
boundary, snapshot each needed account data allocation with one short scoped
borrow and an owned Vec/array copy, then immediately drop the guard. Snapshot
complete metadata independently; never clone an AccountInfo as an owned model.
Use one SDK exclusive checkpoint write/copy at the end of successful stage1.
Stage2 has no checkpoint write. Preserve its return-data clear before validation
and its exact successful emit syscall. No guard crosses a child call.

Owned stage1 is split into instruction/count admission, metadata admission,
checkpoint zero scan, full public decode/validation, candidate encoding,
proof length/prefix/tag checks, first verifier call, returned length check,
and successful checkpoint output. The zero scan is a small structurally
recursive function; no iterator adapters, RefCell, broad loop body or timing
code enters extraction. Decode, validate, encode and verifier children retain
their complete carriers and exact error mapping.

Owned stage2 must cover the WHOLE caller including authentication: request
decode/bindings, account metadata, master/registry/entry/checkpoint/lane
reconstruction, proof scan, reconstructed statement, public encoding,
tx2_authenticated and result emission. Leaving native validate_asq8 opaque
would hide the remaining SDK reads and would not meet D182. Its owned port
must call the unchanged value children on snapshots. Extract both full caller
continuations, with SDK snapshots/write outside the owned boundary.

## Explicit behavioral differences requiring disposition

1. Eager fallible copies reorder errors. Give stage1 distinct valid metadata,
   a zero checkpoint1768, empty public bytes and an externally exclusively
   borrowed proof cell. Current stage1 decodes public first and returns
   InvalidAccountData without borrowing proof. An eager proof copy propagated
   with `?` instead returns AccountBorrowFailed. Capturing copy Results and
   consuming errors in original order can fix this example; eager `?` cannot.
2. Shared-cell saturation survives deferred error ordering. Let two readonly
   handles with distinct keys share a data cell whose counter is MAX-1.
   Current overlapping shared acquisitions admit the first and reject the
   second at MAX. Sequential copy/drop acquisitions both succeed. This is a
   valid SDK counter schedule, not a native accepted full-transaction witness;
   it proves that substituting the new admission schedule is not itself an
   equivalence theorem. Actual caller control must still be connected.
3. With a nonzero shared checkpoint counter, current stage1 rejects at its
   initial exclusive acquisition. A shared checkpoint snapshot followed by an
   end-only exclusive borrow can instead reach an earlier owned logic error.
   An exclusive entry snapshot preserves that initial check, but is an extra
   exclusive acquisition in addition to the successful final write.
4. Additional Vec allocations consume the fixed256KiB SBF bump heap (lib.rs).
   Memory allocation failure/abort, malformed oversized account buffers, stack
   behavior and transaction compute exhaustion require runtime gates. Equal
   successful-fixture values do not prove equal behavior on all allocations.

Recommended disposition: retain the every-input contract until the lead gives
an explicit input-domain/error exception. If runtime admission is approved,
state and prove initial counters0, valid account allocation associations,
exclusive checkpoint availability, and sufficient allocation/CU resources.
Do not infer those premises from distinct keys or from adapter acceptance.
The pending question does not authorize restricting the security experiment.
A source-order copy alternative still needs a solution for overlapping-counter
admission; moving copies later alone does not settle unrestricted equivalence.

## Proved-cone impact and remaining child obligations

No source function is touched in this design stage. Proposed production changes
are caller glue and new owned authentication continuations only. Keep original
verifier first_decoded/tx1, tx2_authenticated, checkpoint encoder/decoder,
multiproof parser/views, S7/S8 and arithmetic child bodies byte-identical.
Keep original metadata/authentication helpers if other callers use them; add
owned counterparts rather than silently attributing old proofs to new bodies.
Hash and compare individual pinned functions and their dependency inventories
before claiming reuse. All source-to-ELF ports must refer to the new pins.

S2G supplies installed pure decode, validate, candidate, first and owned-copy
contracts. Its table DOES NOT supply a complete native effect contract for
first/second, whole authenticated ASQ8, forest public encoding, emit or clear
return data. These remain named missing-child hypotheses with exact carriers
and ordered effects; no fabricated successful return or erased query prefix.
S2TrustedSdkBorrow's existing fifteen fields are unchanged. A snapshot/write
composition theorem and runtime/allocator admission remain necessary; the
trust record does not prove the caller merely by being imported.

## Copy cost estimate and gates

Stage1 successful payload copy volume is58295 +1880 +1768 =61943 additional
bytes, plus the existing1768-byte checkpoint output copy. Stage2 copies the
58295-byte proof and1768-byte verifier checkpoint plus master, pool checkpoint,
lane, registry and entry data at their admitted lengths. No second proof copy
is needed for proof scanning. Owned buffers stay on heap, never a58KiB stack
array. Eager copying of unchecked lengths has no finite byte bound.

For planning only, if memcpy were charged10 + floor(n/250),
the three stage1 payload copies sum to277 CU. This is NOT a measured increment:
allocation, caller instructions, data traversals, syscall lowering and heap
high water add costs. Treat the estimate as hundreds of copy-charge CU and an
UNKNOWN total; the 12000-CU regression limit is a measurement gate, not a claim.

Stage2 gate: optimized capped host builds (6G high/8G max/swap0/tasks64,-j4),
all three ELFs with source/features/toolchain and old/new hashes; native/SBF
transfer and withdrawal fixtures both stages; side-by-side original snapshots,
errors, return data, checkpoint and ALL account records; at least1000 mutated
length/tag/account/counter inputs. Record CU per transaction for both versions.
STOP on any >1400000 CU or increase >12000 CU. Retain build-generated keys.
No binary or key material enters git. Reserve aggregate host capacity first.

Stage3 gate: extract both full owned callers; smallest changed Lean file first,
then dependent bridge and axioms audit. Budget100 Lean attempts/60 Kani runs.
For each Required14 field report concrete discharged theorem or named missing
obligation. No new field is discharged by this note. Runtime cross-transaction
checkpoint retention and oracle interpretation remain separate from local
buffer copying. No full manifest replay before focused predecessors pass.

## Pins and current completion status

Inherited default:40dc75742430dd198bd51d519aa5a41bad4a45e8f173ccbd51c6d5be344ac3f0.
Inherited devnet:12cb0bc2f8ff3993643638080a3786fdcd941910e5e4dd65ae2937a99290c28f.
Inherited Pool:121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548.
New pins: NOT BUILT. These historical pins are not fresh confirmation.

Stage1 note committed before code. Stages2/3 are pending the behavioral-domain
resolution above. No production change, host build, fixture suite, CU measure,
Lean attempt or Kani run has occurred. Required14 newly discharged:0/14.
The diagnostic receipt checks only the finite abstract SDK schedule and source
order anchors; it is not the requested1000-input differential gate.
Target not yet established. No merge, adoption or push is authorized here.
