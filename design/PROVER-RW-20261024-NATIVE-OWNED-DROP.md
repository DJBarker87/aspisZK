# ProverRwOwnedDrop: actual owned byte destruction (unadopted)

Design before execution, parent b724680f271cf989d7acef38d7438e4df1138c78,
branch codex/cx-prover-rw-20261023. The manager revokes the prior blanket
Guard prerequisite. Failed Guard evidence and unaccepted tools remain intact.
No shipped source, installed tool, trust, protocol, wire, feature, security
contract, wallet, chain, adoption, merge or push change is authorized.

## Exact source class and obligations

Target crates/aspis-prover/src/state_only_entropy.rs:211-241,
StateOnlyAttemptSecrets::generate_for_mask_nonce, selected64 LLBC hash
b8ac641c1fdb71667cb34a554d37c310ad81d38ead8e57e80529a32bce0f1b48.
Concrete dependencies: zeroize 1.8.1 and getrandom 0.3.4. Reject zero public
nonce without a draw. Each of at most16 iterations initializes an owned64
buffer to zero, calls fill, and preserves partial writes and advanced provider
state even on Err. The ? path drops64 before returning mapped OS error.
Success copies the two halves into owned32 buffers; if both are nonzero,
they MOVE into Self and64 drops. Failed nonzero test drops leaf32, field32,
then64, before retry; exhaustion returns RepeatedZeroBlock. Returned Self
retains two32 owners for later cleanup. Moves do not justify wiping stale
copies or registers. Panic during fill/copy/other calls requires unwind
cleanup separately; double-panic abort is not normal Result failure.

Actual Zeroizing<Z>::drop calls self.0.zeroize(); array Zeroize calls
iter_mut().zeroize(); IterMut iterates and each u8 invokes volatile_write of
Default::default() plus SeqCst compiler_fence. These are owned Z=[u8;32/64],
without nested-reference Z. Regular precise glue, mutable self borrow/return,
array iterator loans, volatile pointer writes and compiler fences are needed.
Generic swap<Option<&mut T>> is NOT a prerequisite for these instantiations.
No opaque Zeroize dictionary, fixed-zero return, destructor stub or axiom may
stand in for this source chain. Physical byte erasure is distinct from L3
hardware/register/cache/timing claims.

The selected69 inventory has31 Zeroizing32 and25 Zeroizing64 sites (including
unwind statements),9 generic free0,2 RealR1 closure,1 Result<Self,Error>,1
free3 sites. Generic/captured Drop is not eliminated by proving the56 byte
owner sites. RealR1_client takes mut proof_account: impl FnMut(usize)->[u8;32];
its closure BORROWS that arbitrary mutable policy and invokes generate. The
outer retry owner recursively moves next_attempt after Rejected up to8;
nonce_store remains &mut DurableStateOnlyMaskNonceStore. Arbitrary policy
captures may own references, Drop-bearing values or escaping loans. They
remain required on that path, fail-closed/open, without fixture specialization.
Advanced policy/provider/store state on errors, reservation and ordered draw,
retry, error, cleanup, ledger and publication events remain observable.

## Planned source proof and memory argument

First isolate unchanged pinned Zeroizing32/64 source via a proof-only crate.
Try actual precise-owned-Drop lowering with -eval-drops and pinned flag guard;
never drop_as_no_op. If pointer/volatile leaves reject, use authorized Kani
source proofs under existing P6 policy, without extending extraction trust.
Use initialized symbolic arrays; prove direct array Zeroize and actual Drop
exactly once in retained storage. Proposed retained storage is MaybeUninit
initialized by write of a complete Zeroizing value, not uninitialized bytes.
Compute the INNER u8 pointer via a live mutable dereference, end that borrow,
call drop_in_place exactly once on the live outer value, then inspect ONLY
inner32/64 bytes through the raw pointer while the backing allocation remains
alive. No Rust reference to the dropped value, freed-memory read, padding read,
second drop, leaked live secret, or assumed expected result. Justification
requires actual destructor only writes valid initialized u8s, owns no allocated
children, and does not deallocate backing storage. Kani memory checks must
remain on; a rejection is retained, not bypassed. A source helper theorem is
not automatic-scope glue, unwind, whole owner, or hardware closure. Normal
move/error integration needs its own checked relation; unwind remains open
unless specifically validated. No production unsafe code is introduced.

## Transport, validation, resources and budgets

Before/after all existing theorem statements are IDENTICAL; no premise is
removed or introduced. Caller-specific cuts need event/probability transport,
never whole-output equality as a premise. Literal E1 conditional64 law, OS
primitive,16-inner/8-outer, L1/L2/L3, native owner/event transport and adoption
obligations unchanged. Both deployed targets not yet established.

Start backend15/16 (no new allocation; preserve last slot), extraction44/48,
Lean236/260, Kani44/60; at most8 Kani and4 optimized Rust commands this step.
All reserved failures count. No full manifest without lead closure approval.
Host jobs only6G/8G/noSwap/Tasks64 or existing stricter Lean5G/7G. Check full
system/Docker hierarchy, ancestor deduplication and uncapped visibility before
launch AND go, sum<55GiB, missing data denies. Check barriers/hashes before
slot reservation. Global Lean lock outside22:30-14:00 London. No uncapped
build, cap raise, unchanged resource-failure retry or shared-tool/cache edits.
Record exact commands, source/dependency/binary hashes/revision/flags, exit,
wall/RSS/swap and full axioms (N/A for non-Lean). Separate universal Kani,
native reference, source helper, trace and hardware claims; retain failures.
