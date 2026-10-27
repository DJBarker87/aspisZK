# JHe TX1 fixture30 handoff

Status: **partial; budget exhausted.** Exactly 100 Lean processes (65 exit0, 35 failed), 0/10 Kani runs. No attempt 101; no push. All 100 statuses are settled. Successful theorem audits use only propext, Classical.choice and Quot.sound. Recovery sorryAx from failed attempts receives no credit.

## Owner-requested deliverables

1. `saved.val = JFx_NativeBytes.checkpoint.val` from the actual writer return: **OPEN**. The length, first16 bytes, exact constructed image, and actual proof/public/body-checksum requests are proved. These do not imply all1768 bytes coincide.
2. `JHe_TX1.accepted1` unconditional or with only the SHA-realization hypothesis: **OPEN**. No theorem with that name is supplied. `JHe_TX1Frontier.wrapper_of_child` is a checked helper with the actual installed `AdapterRw.first_decoded` success as an explicit remaining premise; it is not the allowed SHA-only endpoint.
3. Joint pair: **OPEN**. No JHf-prefixed source was merged in this worktree. The corrected JHb second bank contains the retained checkpoint, not an arbitrary source-selected return.

## Exact checked progress

- `JHe_SavedWitness.inhabited` selects the successful candidate's actual saved vector. It packages candidate and op16 success on the same execution, length1768, header identity, exact body length1736, and three digest equations on the actual proof, public and constructed body. It does not supply a retained successful output as an input.
- `JHe_WriterTrace.source` proves the chronological append-content-writer trace, proof/public/checksum, with the checksum request constructed from that body. It is a local Lean trace, not global rejected-prefix or ELF trace transport.
- `JHe_Run.inhabited`, `JHe_ReferenceRun.writer`, `JHe_WriterSelected.returns/length/original`, and `JHe_OriginalSelected.source` join the actual prepare/query/flush run to the ORIGINAL Tx1Q writer returning the SAME saved vector. Existing JHc query/flush and certificate proofs are reused unchanged.
- `JHe_ImmutableState.source` identifies the prepared transcript-state bytes with JFq_State.value. It does not identify final query rhs/power/flushed weights with retained checkpoint fields.
- `JHe_NativeAssociation.source` and `JHe_ConfigDigest.source` separately associate the corrected installation's current ops and digest with that original-writer candidate.
- `JHe_SdkDistinct.source`, `JHe_SdkInputGate.*`, `JHe_SdkReads.*`, `JHe_SdkCheckpoint.source/zero`, and `JHe_SdkCodec.*` prove the concrete source-order guards/reads/codec calls on JHb_World.e1, its actual58295-byte header+proof account,1880-byte public account and zero1768-byte checkpoint account. JHe_ZeroGate uses bounded induction rather than whole-buffer reduction.
- `JHe_SdkParent.source` derives actual stage1_owned success from the SAME installed first_decoded child success and saved length. `JHe_WrapperReady.source` then supplies the actual copy wrapper. `JHe_TX1Frontier.wrapper_of_child` composes them and exposes the remaining child premise exactly.
- `JHe_HeadlineConfiguration.source` proves the data-only fission equals IDa_Deployed's configuration. `JHe_FinalInstallation.source` proves the extra FIp pass is idempotent, with nine record fields and23 query fields isolated. `JHe_HeadlineSdk.source/sdk` associates the EXACT extra-FIp/IDa configuration in RPx's extraction hypothesis with JHe_Natives.configuration/sdk. This removes an installation mismatch from the fixture construction; it does not remove a premise from RPx.

The precise frontier is:

```lean
AdapterRw.first_decoded (JHe_Natives.sdk base stage)
  (S6N_Getters.publicValue JGx_RealStatement.value)
  JFx_NativeBytes.publicInput JFx_NativeBytes.proof 10#usize
    = ok (.Ok saved)
```

Together with `saved.val.length=1768`, this yields the actual wrapper result
`ok (.Ok (saved,JHe_WrapperReady.post saved,()))` on JHb_World.e1. Neither this success premise nor a replacement SDK success may be counted as discharged.

## SHA-only route and resource obstruction

Unconditional original candidate proof and SDK association each check separately. Their import union exceeded -M7000 at047,057,060. Earlier044 failed memory-heavy concrete record rewriting;045's generic record-update proof fixed that local shape.061's wide453-field record failed;069's merged tree consumer failed. No memory cap was raised, and no timed-out/memory-failed job was rerun unchanged. See JHe_MEMORY44.md, JHe_MEMORY69.md, JHe_MEMORY93.md and each failing receipt.

The explicit permitted fallback proposition is:

```lean
class AspisR1.JHe_SHARealization : Prop where
  tree0 : ∀ i : Fin 157, JFp_SHADigest.digest (JHe_SHAInputs0.input i) = JHe_SHAInputs0.expected i
  tree1 : ∀ i : Fin 157, JFp_SHADigest.digest (JHe_SHAInputs1.input i) = JHe_SHAInputs1.expected i
  tree2 : ∀ i : Fin 139, JFp_SHADigest.digest (JHe_SHAInputs2.input i) = JHe_SHAInputs2.expected i
```

The three equation modules and aggregate pass071–074. This is exactly453 batch digest equations, with no acceptance/output-identity field. JHe_SHA_FISSION.json pins every original input/output expression and source hash. Indexed lookup normalization is explicit; SHA is not unfolded. `JHe_C_Tree0A` passes097 using this hypothesis. Other consumers and the proposed realization-inhabited proofs are **UNCHECKED**, archived as .lean.txt in JHe_UNCHECKED; they are not active Lean candidates. The whole realization proposition has no checked inhabitant in this round. Generator `--check` validates active sources and archived generated drafts; running it without `--check` recreates unchecked consumer files and is not verification.

Attempt075's recursion errors were ordinary elaboration failures; explicit lookup reduction plus A/B/C consumer fission replaces that shape. Attempt093's whole-record timeout was split094, then the query-field timeout was split096. Neither heartbeat nor time limits were raised. One unchanged ordinary-error rerun063 happened after a failed generator preflight; it is retained and gets no credit. No unchanged memory/timeout rerun occurred.

## Before/after, recount and non-vacuity

The adopted actual top is `AspisR1.RPx_Deployed.deployed`, frozen3 / ARX_Root. Before and after source statements are byte-identical: JHe_BEFORE_RPx_Deployed.lean.txt / JHe_AFTER_RPx_Deployed.lean.txt. A fresh separate pinned-cohort audit099 prints its type/value and axioms. L154 remains a statement parameter, not a discharge.

By the existing ledger's quantified atomic-law-family/conjunction-leaf method, with witnesses, guard carriers, deployment rows and event fixed:

| Statement | Before | After | Removed |
|---|---|---|---|
| RPx headline |83T/0P/13G|83T/0P/13G|0T/0P/0G|
| FJv_Top comparison |83T/3P/13G|83T/3P/13G|0T/0P/0G|
| RPx deployment expansion |89T/15P/13G|89T/15P/13G|0T/0P/0G|
| FJv deployment expansion |89T/18P/13G|89T/18P/13G|0T/0P/0G|

See JHe_LEDGER_DELTA.json and JHe_STATEMENT_COMPARE.json. No headline premise was added, changed or removed. The SHA and actual-child premises belong to separate unfinished fixture helpers, not an altered headline.

**Non-vacuity actually established:** an unconditional source candidate/original-writer execution on the retained proof/public input, with its source-selected output. **Not established:** inhabitance of ALL hypotheses of the actual headline, nor a real-byte joint transaction pair. The missing byte equality is substantial: the retained second bank uses JFv_World.saved. Actual query postconditions currently supply canonicality and sizes, not all concrete final rhs/power/flushed-weight values required by that equality.

Remaining pair conjuncts, exactly in scope: full actual-saved/retained-checkpoint byte identity; actual installed first_decoded success (unconditional or only the named SHA hypothesis) and hence accepted1; JHf's actual accepted2 on that same SDK/world tuple; the resulting same-saved checkpoint/persistence/game linkage. Runtime admissions, complete game/hypothesis inhabitance and native/ELF association are not supplied by the local writer witness. Approved RuntimePersistence remains a runtime trust item.

## Validation, pins and next step

JHe_GATE_TABLE.md summarizes key exact targets, exits, wall times, peak RSS and swap. Per-attempt receipt.json has source revision/dirty flag, source SHA, Lean binary SHA, dependency hashes, cgroup and printed axioms. The complete100-attempt index is JHe_ATTEMPTS.jsonl; JHe_VALIDATION.json and JHe_SOURCES.json index current checked sources. A passing source snapshot is not a blanket coherent release replay of every historical dependency cohort.

Every host Lean command used lake env lean -j1 -M7000 with MemoryHigh6G/MemoryMax8G/MemorySwapMax0/TasksMax64 and admission allowed:true plus exit0. One scope at a time. No Rust, Kani, SBF, Aeneas extraction or frozen-manifest replay ran. Focused SDK roots audited098, headline separately099, original writer roots100. All65 successful attempts print only standard axioms where they print axioms. Aggregate Lean receipt wall970.278s, maximum RSS7196428KiB including failures, swap0.

Reuse coherent SInt2 and its unchanged dependency objects. Primary Aeneas object pins are JHe_AENEAS_OBJECT_PINS.json; the separate headline path was pinned read-only after099 in JHe_HEADLINE_AENEAS_OBJECT_PINS.json, all219 hashes matching primary. Own JHe compiled objects were removed after100 under local-lean rule9; exact paths/hashes are in JHe_CACHE_CLEANUP.json. Other prefixes/caches and all keys were untouched.

Only JHe-prefixed Lean modules and this evidence directory changed. JHe_FREEZE.json records revision/features/wire/toolchain and inherited default f8c0ec72…, devnet63ad3e9c…, Pool121f3e29… pins. No shipped-file change or ELF rebuild trigger. No release/native/source-to-ELF claim.

D188: JHe_D188.md lists reached mutable iterator/element writes not credited as cleared; the specified SDY bodies stay cleared, low_base_p_digits is excluded and bridged by LPk. No new native credit.

Next concrete work: import every checked JHe/JHc result; finish the split SHA consumer chain (tree0B/C, tree1A/B/C, tree2A/B/C, RootReads/Batch/PreBatch/BatchFrontier/TX1Candidate/Child) under a new authorized budget, then feed actual child success into the checked wrapper frontier. Independently identify final query accumulator and flushed weights, proof/public hashes and constructed-body checksum to close all1768 bytes. Do not promote the checked16-byte header to full identity, and do not promote the child-success helper to accepted1. Recount only when an actual headline premise is removed.
