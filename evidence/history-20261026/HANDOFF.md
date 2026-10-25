# History worker final handoff

Status: stopped at100/100 charged Lean submissions, not ledger closure.
Branch codex/cx-history-20261026. Initial revision b57e886291a629af05b3fd7bcc497f1fe4f71500.
Only lean/Hist_ modules and this receipt directory changed. No push. No other
worker's worktree or candidates edited. No shipped source, feature, wire format,
parameter, key, account or artifact mutation. No package/manifest replay.

## Ledger delta

Removed row IDs: NONE. Added row IDs: NONE.
L094 history.savedAtCommit, L095 history.loadedAtEntry,
L096 history.noInterveningWrite, L097 p2prime.binding.proof,
L098 p2prime.binding.pub and L180 history protection / Pool-ASQ8 remain OPEN
at the deployed universal endpoint. Do not merge this as a global premise
removal. No checked counterexample against shipped source was found.

## Before and after statements

Hist_BEFORE.txt freezes the original WAdm accepted-pair source from the initial
revision. RowOrder_AcceptedPairHistory and its original continuation consume
CheckpointVersionBinding (savedAtCommit, loadedAtEntry, noInterveningWrite)
and P2Prime for separately supplied accepted e1/e2. Those arbitrary entries
are not necessarily a causal same-key pair.

Hist_AFTER.txt is the exact source of Hist_TraceCausal.accepted_pair_causal;
Hist_100/stdout.log prints its full elaborated theorem and exposed Step/Trace,
CheckpointVersionBinding, P2Prime and charged Program definitions.
On computed runtime loads, actual accepted TX1/TX2, the SAME original source
cut witnesses, schedule, Claims, SDK observations and native writer facts are
retained. The caller continuation has no old history or P2Prime input. It
returns the existing caller facts OR a charged collision event. It also exports
the SAME raw source Trace.run, actual semantic getter/validation/encoder, and
readerPublics outer = [s.pub]. No independently accepted source call is an
input to this strengthened factory.

The changed family has EXPLICIT additional obligations: runtime Trace between
the computed commit and load, causal checkpoint key equality, pure SDK keyEq
interpretation, fixed-before-H containing Program returning four actual input
byte strings, a uniform whole-program first-read Q, and association of those
returned bytes with the same source cuts. These are model/refinement gaps,
not adopted crypto assumptions. This is a different causal family, NOT a
weakening of the original theorem over unrelated entries. Existing extraction,
stdlib, runtime/allocator/syscall, child-cone and SessionA preparation/primitive
trust remains. Full statements must be inspected before any integration claim.

## Checked source results

Actual stage1 zero-check inversion plus emitted writer marker82/length1768
makes a second accepted initialization of that protected checkpoint impossible.
Source-derived owner/readonly/signer/executable checks and distinct-account
loops establish per-step protection, including source TX2's no-data-write
behavior. Hist_TraceProtection/Hist_Persistence lift this to nonempty histories
and fill all three old history fields on actual computed commit/load bytes.
Hist_CommittedSdk.version connects the exact native std-copy post1 payload
slot consumed by RowOrder/D189 to the selected checkpoint, using original
writer preparation instead of assuming a marker or saved size.

The records remain distinct: ASQ8 request320 (Pool encoding may324 with bump
hints), ASF8 public1880, Pool immutable forest checkpoint192 at TX2 slot2, and
verifier checkpoint1768 at TX1 slot2 / TX2 slot6. Hist_CheckpointSeparation
proves CP2 and CP6 actual keys/cells distinct from the source alias check.
This does not prove all lifecycle/writer behavior of the deployed Pool program.
Hist_Asq8Guards/ReaderAuthority prove the actual Pool-owned readonly account
checks, not the missing complete Pool-ASQ8 storage history instance.

Proof/public buffers can have arbitrary owners. Checkpoint protection alone
therefore cannot give P2Prime. The budgeted collision route is used instead;
no hash injectivity premise. Hist_ByteAssociation uniquely pins the four-byte
selection between source witnesses when actual validation/op22 provenance is
retained. Hist_WholeEncoderTrace ties the actual TX2 public argument to that
encoder inside the complete source trace.

## Bound and success conditioning

For a fixed adaptive containing Program chosen BEFORE H, with uniform
whole-source first-read budget Q, four appended complete-byte reads preserve
its output and yield P2Prime OR the existing BinRawByteCollisionTargets.event
on that same enlarged log. Hist_ByteExperiment.collision_bound gives
6*(Q+4)^2/2^256. Hist_JointCharge/JointBinding combine canonical replay1040 and
those four reads in ONE enlarged log: loss6*(Q+1044)^2/2^256. Source/adversary
preprocessing, rejected submissions and verifier queries must all be in Q.
No numerical whole-source Q,100-bit conclusion or campaign work metric is
claimed. In particular1921/2961 inner bounds are not whole-account bounds.

Hist_SuccessBinding.successful_equal_or_collision says pointwise: successful
matching proof/public digests imply complete byte identity OR that same charged
bad event. Its successfulMatches premise is explicit; it is not a proof that
arbitrary deployed acceptance implies digest matching. No conditional mass
bound is obtained by dividing out an unproved success probability. No replay
is free and no collision loss is hidden in a new trust structure.

## Non-vacuity and limitations

Hist_Nonvacuity.trace_exists constructs an initialized1768-byte protected cell
and a NONEMPTY legal foreign-write/rollback trace with retention. This proves
local trace satisfiability, not a full joint cryptographic accepted witness.
Hist_RUST002 is a two-test optimized fixture using the actual unmodified Rust
entrypoint and production-matched selected dependencies: initialized marker
values1/82/255 reject for splits10/11, and release guard rejects lifecycle tags
1/2/4/5/6. Fixture measurements are not exhaustive verification. KANI001 failed
during compilation/linking before verification (lld std::system_error resource
unavailable); no Kani theorem or source counterexample follows. No unchanged
retry, cap increase or infrastructure repair was attempted.

The inherited exact-ELF accepted-pair fixture/source comparison is recorded in
Hist_source-pins.json and prior stage receipts. No fresh accepted joint witness
or three-ELF rebuild is claimed. Runtime account-ownership trust is accepted;
classification of arbitrary deployed histories into Hist_Store.Trace and
same-key causal pairing is still to be proved. The concrete fixed-before-H
whole-source Program/output association and uniform Q remain to be constructed.
Immutable global-worker handoff0869cf6479 independently leaves these latter
experiment obligations open. Only read-only immutable git inspection was used.

## Frozen target and verification receipts

Hist_source-pins.json pins all selected unmodified source/Cargo hashes and:
- default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4
- devnet 63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299
- Pool 121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548

The existing coherent SInt2 workspace/cache and unchanged launchers were used.
Every scope: MemoryHigh6G, MemoryMax8G, MemorySwapMax0, TasksMax64. Lean4.32.0,
-j1 -M7000 -DElab.async=false. Optimized Rust only. No caps raised; no time/memory
kills; no unchanged full regression. Source-only proof additions invalidate no
shipped artifact pin; these are experimental source proofs, not release adoption.

Hist_validation.json and Hist_validate.py map EVERY current Hist module to its
passing exact-source SHA256 snapshot and list every invocation's exact target,
command, revision anchor/dirty status, exit, wall seconds, peak RSS, swap and
#print axioms. Detailed dependency object fingerprints, tool binary hashes and
scope readings are in each numbered receipt. Revision fields are ancestor
anchors with dirty-source snapshots, not claims of clean release builds.

Final count:100 charged Lean submissions =97 actual invocations (61 passing,
36 elaboration failures) +3 own-dependency prelaunch failures016/018/091.
All56 current Hist modules match passing exact snapshots. Failed outputs,
including recovery sorryAx diagnostics, are excluded from proof evidence.
Final focused audit100: exit0,1.930039s,5189436KiB peak RSS,swap0.
Across all97 Lean invocations:180.084118s cumulative measured wall,
5222548KiB largest reported peak RSS,swap0 throughout. Only standard axioms
propext/Classical.choice/Quot.sound occur in accepted top theorem audits.
One of30 Kani attempts used (compiler failure), two optimized Rust fixtures.
The exhausted100-submission Lean budget is the stopping condition; no further
proof compilation, Kani workaround or release replay is authorized by this run.
