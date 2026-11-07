# Canonical345 specification findings (active review)

Target not established. These are source/specification findings, not Kani
counterexamples or a ledger promotion. Canonical087/094/328 remain unchanged.
No frozen code, trust row, runtime assumption or security metric is changed.

## NMT-S1: String-error clone is not an infallible pure getter on all owned records

RSL_Base.OwnedAccount.data/data_len and verifierCheckpoint are pure `Except`
functions. RSL.TX1_345.Domain is True, so arbitrary deferred ProgramError
payloads are in the target. The frozen solana-program-error2.2.2 ProgramError
has `#[derive(Clone,...)]` and `BorshIoError(String)` (lib.rs32/51).
String::clone in the PINNED nightly2026-09-17 std calls Vec::clone, whose
implementation calls `[T]::to_vec_in`, allocating a fresh vector. The pinned
source paths, hashes and exact excerpts are in NMT_CLONE_STD_SOURCE.json.
A nonempty String clone can therefore abort on allocation failure under the
already retained std/allocator semantics. No post-abort world is required.

The earlier generic data_std/checkpoint_std lemmas instantiate the emitted
opaque clone with `.ok e`. They are correct SOURCE/LIBRARY SUPPORT FOR THAT
INTERPRETATION, not a proof that arbitrary actual String clones always return.
They must not be used as unconditional full-observation physical packets.
The existing CLOSED335 and341 native packets explicitly restrict deferred
errors, excluding String. NMT_345CloneWitness tests the canonical target's
forced String-error return and excludes a clone abort; its compile receipt
will decide whether that Lean witness is accepted.

The actual344 caller uses snapshot343. NGL_SnapshotCases.Domain proves only
AccountBorrowFailed length errors and AccountBorrowFailed/InvalidAccountData
byte errors, with matching returned length/bytes. NGL_StorageCases adds the
actual length set, including58295/1880/1768; this is NOT a4096 bound.
NHJ_DataPacket.storage_domain and NHJ_LengthPacket.storage_domain expose the
exact clone domains. A snapshot-domain own-input clause on345 would address
THIS finding and is a concrete (bf)(2) caller clause for344, not a child-output
hypothesis. It is an EXACT DIFFERENCE from canonical Domain=True and is not
silently adopted or reported as the canonical theorem.

## NMT-S2: decoder's internal allocation prefixes precede later Rust Err arms

Frozen4bb3b3f51e16b4525f1d10336e2b0bcbbd775387,
crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs332–425:
`decode_pool_v1_pair_forest_terminal_statement_v1` calls
`decode_terminal_common_boxed_v1` BEFORE the payment decoder. The common
decoder calls the boxed lane-transition decoder and then `Box::new(common)`
at351. Only afterwards does transfer/withdrawal payment parsing run at377/392;
these can return format Err. Terminal-statement Box allocation is at379/394.
Thus an internal allocation may fail on a reached prefix even when the full
error-returning decoder would ultimately reject the input. These are actual
frozen calls, not a proposed implementation.

RSL.S1Lib.decodeStatement is `Bytes -> Option Statement`, required by RSL_INDEX
to be the CLOSED332 model at SAME arguments. RSL345.body first executes
`RS.ofOption decodeStatement`, THEN one `Spec.alloc`. At `none`, it returns
InvalidAccountData with no allocation/abort alternative. It cannot represent
an internal allocation abort on a prefix of a later rejecting decoder run.
Moving a generic allocation before every decoder input would also be wrong:
wrong length/magic/version reject before any such allocation.

A faithful correction uses the CLOSED decoder's FULL Result/abort observation
packet in S1Lib, including its actual reached allocation sites, rather than
an Option result followed by one unconditional post-success allocation.
NMT_345Decoder already transports the complete emitted Result and can be
reused in that correction; it does not itself prove physical allocation
success or discharge this specification mismatch. Snapshot-domain restriction
alone does NOT fix NMT-S2, because malformed1880-byte public inputs can reach
a boxed common before a later payment rejection. A child-success/decode-Ok
hypothesis would be forbidden and is not proposed.

The run continues with independent source-position folds, concrete child
installations and public-domain discharge. No canonical345 complete fold or
candidate is claimed while these discrepancies remain. The next gate should
review the exact corrected full-observation statement, rather than treating
a pure Option or an allocation-success interpretation as closure.

### Checked semantic distinctions

NMT_345CloneSemantics.deferred_string_models_differ compares the allocation-aware
getter transcription with the pure canonical getter at the SAME owned argument.
NMT_345DecodeAbortDistinction.reject_models_differ proves that a reached
allocation followed by rejection differs from Option.none followed by any
post-success continuation. Both are standard-axiom Lean results, not physical
native counterexamples. NMT_345CloneWitness.forced_return/no_clone_abort passed
L202; the earlier prospective wording above is superseded by that receipt.

Proposed exact target differences, not silently installed: (1) either adopt
snapshot343's actual owned-record invariant as a caller-established own-input
clause on345, or represent error cloning in the getter/checkpoint observation
law; (2) replace S1Lib.decodeStatement's Option-plus-post-success-alloc by the
CLOSED332 full observable decoder law, preserving allocations before later
Rust Err branches. Both corrections are required unless an existing admitted
library policy supplies stronger exact physical laws. No new allocation-success,
child-success or 4096-bound assumption is proposed. The canonical087/094/328
parameters are retained exactly.
