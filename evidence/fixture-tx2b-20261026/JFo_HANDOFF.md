# TX2 real-byte continuation — accepted2 not established

Branch `codex/cx-fixture-tx2b-20261026`. New `JFo_` modules and this receipt
directory only. No push, merge, session A worktree/candidate edit or shipped
source change. **JFo_TX2.accepted2 is not delivered; the 100-bit target and
full joint non-vacuity remain not established.** No new vacuity counterexample
has been proved.

## Checked statement and limitations

`JFo_WeightRestore.source` proves symbolic weight writeback, and
`JFo_Weights.source` instantiates all64 actual ordered weights from the retained
checkpoint. `JFo_Tail.source/native` compose the complete reader tail on those
same bytes. `JFo_DecodedAccumulator.source` independently identifies the physical
accumulator decoder from the checked reads, using a generic state lemma to avoid
reducing a concrete64-entry list. `JFo_ReaderFixture.inhabited` joins those facts
without reader-success or decoder-success premises.

`JFo_Resume.source` and `JFo_ResumeNative.source` prove forward authenticated
resume and the native/installed op18 readers. **Exactly three hash-call equations
remain explicit premises**: proof hash, physical public hash and checkpoint
checksum. The inherited SHA256 diagnostic preflight is not a kernel SHA256 proof.
These are not computed wrapper-acceptance theorems.

`JFo_Pending.source` computes the native pending allocation on the decoded64
weights. `JFo_Powers.source` derives a successful actual powers return and its
canonical exact powers, from computed canonical gamma limbs, without a powers-
success premise. `JFo_Opening.call/selected` identify actual source opening
returns with their real proof ranges, with no opening-success premise.
The individual `JFo_Opening10_0`–`JFo_Opening21_3` candidates target all48
installed native field reads for the remaining12 query openings; the final
validation manifest, not this candidate range, determines which are checked.

Full query folding/equality checks, geometry, accumulator updates and post-query
flush are still unproved here, as are batch1, installed finish and the second
accepted wrapper. No output-equality assumption, constant-success native or
success dictionary replaces those obligations. The retained JFx proof/public/
1768-byte checkpoint are unchanged. TX1 must still prove accepted1 and equality
of its SAME saved Vec with these exact checkpoint bytes.

## Actual top, ledger and freeze

The latest actual top present here is `AspisR1.Rc10_Top.deployed`.
JFo_BEFORE_Rc10_Top.lean.txt and JFo_AFTER_Rc10_Top.lean.txt preserve its complete,
byte-identical source statements; JFo_STATEMENT_COMPARISON.json records hashes.
The quantified atomic-law ledger method retains common witnesses, guards,
carriers, dictionaries and deployment rows. Actual83T/12P/13G/0C; deduplicated
actual plus non-alias deployment89T/16P/13G/0C. Removed, added and changed are
each0T/0P/0G/0C. Quantifiers, conclusion, failure event, metric/constants,
frozen3 and approved runtime trust items are unchanged. The concrete helper
facts get no actual-top premise-removal credit. No crypto/security premise was
discharged or reclassified as trust.

No shipped file or cfg(kani) harness changed, so no ELF rebuild trigger fired.
No Rust, Kani, SBF, full frozen-manifest replay, unrelated runtime/adversarial
suite, wallet or key operation ran. INHERITED artifact pins only:
- default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4
- devnet63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299
- Pool121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548

## Validation method and retained failures

Every launched Lean module uses the unchanged SInt2 coherent workspace and
existing admission/host launchers, one scope at a time, -j1,-M7000,
MemoryHigh6G/MemoryMax8G/MemorySwapMax0/TasksMax64. Existing unchanged objects
and their inherited closure provenance are reused; this is focused cached
proof evidence, not a fresh coherent frozen-release replay. Per-attempt JSON,
receipt/stdout/time/source snapshots pin exact target, command, source revision/
hash, selected dependency hashes, exit, wall, RSS, swap, limits and full axioms.
JFo_RECORDS_MANIFEST.json retains rejected attempts; only exact-current-hash,
exit0 receipts in JFo_VALIDATION.json count as accepted results.

Attempt014's unchanged-dependency inventory raised FileNotFoundError for
OraclePortFrozen2Headline before Lean; it produced no result receipt. The exact
launcher output, source hash, admission receipt and absent-receipt classification
are retained. The narrow JFo_PrefixRead/SuffixRead/Index proofs avoid the unrelated
JFt_LocalWindow headline import; no launcher or existing module was repaired,
substituted, edited or bypassed, and no existing shared object was overwritten.
This was a source-import alternative, not a claim that the absent cache was fixed.

Attempt041 hit default heartbeats after an untyped existential made powers
elaboration search its result type.042 supplies the explicit array carrier and
passes; the timed-out source was not rerun unchanged. Concrete accumulator
congruence hit default recursion in024 and was replaced by the symbolic
JFo_AccumulatorState lemma. Further rejected attempts concern namespace/type
inference, reader cursor/projection matching, finite index representation and
small-window arithmetic normalization. All original failures remain visible;
recovery sorryAx output is never accepted. No cap or heartbeat/depth option was
raised. No memory-killed job was rerun.
