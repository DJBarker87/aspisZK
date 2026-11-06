# NKR digest final review: TX1:251 and TX1:250

**Target not yet established. Both digest packets, and all six NKR row packets, remain `CANDIDATE_NOT_GATE_APPROVED` / `INCOMPLETE_COMBINED_IMPORT`. Authoritative ledger delta is zero.** Focused proofs and native controls below do not confer CLOSED or next-ledger credit.

This is a read-only review of retained source and receipts. Only this Markdown document was written; no Lean/Rust source, launcher, gate configuration or compiled object was changed, and no proof scope was launched.

## Exact focused claim and pins

The positive root is `AspisR1.NKR_DigestComposed.source`, owner `NKR_DigestComposed.lean`, for both251 and250. Receipt [NKR_L168/receipt.json](NKR_L168/receipt.json) records exit0, wall15.181149792s, peak6,190,964KiB, swap0, source revision `3a22b72743370fbf5cedbaa66a36401a3d3445c5` with dirty-source hashes. Its source SHA256 is `d1f78879292f8830d39e0842347a68966c233cd2b681049ef69a3d8afba71622`; the current file matches that retained hash. Its printed axiom line is exactly `[propext, Classical.choice, Quot.sound]`. Full type and hypotheses are retained in [NKR_ROOT_STATEMENTS.md](NKR_ROOT_STATEMENTS.md) and [NKR_ROOT_HYPOTHESES_REVIEW.md](NKR_ROOT_HYPOTHESES_REVIEW.md).

The frozen Rust revision is `4bb3b3f51e16b4525f1d10336e2b0bcbbd775387`. The row packets pin body hashes:

|Row|Frozen function|Body SHA256|
|---|---|---|
|251|`public_digest_packed_selector_tensor`|`ef1afaa5cf67dbc47980119f3ff3b539d486059903b9fd7d24621a68d6191d17`|
|250|`public_digest_packed`|`fc44daa9ba77a01784a47faf64017e7a61bd0043ede2e00149451cb05ce08e4c`|

The final endpoint is literal complete two-cell equality: both optimized reference and `NKR_DigestWrapper.cohort` return the SAME `out`. That cohort runs the actual emitted old `FIq_Native...public_digest_lanes`, obtains its full eight-cell result `old`, and applies the existing base4 pack to both four-cell groups. `old` and its canonicality remain conclusions. The intermediate `NKR_DigestComplete.model` is eliminated by the association proof; it is not substituted for the adopted whole-old-body endpoint.

## SAME-argument chain and channels

|Stage|Actual arguments and reply association|Complete channels/frame|
|---|---|---|
|Four prefix blocks|In frozen order:242at high56/anchor,242at high26/nullifier,246at actual recipient/high29,242at high32/change; every call uses the SAME `openings.z`|Each actual two-cell reply feeds two additions at the previous full3x2state. `NKR_DigestPrefixStep.four` composes four arbitrary-prestate3event steps. Groups0/2 are framed; group1 is carried forward. Some/None both remain.|
|Append235|Actual live snapshot index and frontier20x8, SAME opened16 and full high64|Both returned two-cell arrays are retained as all four cells: local0indices0/1 and local12indices2/3. No channel is replaced by an independent reply.|
|Four append additions|Actual previous3x2state plus those four cells|Updates groups0/2; group1 is unchanged. The complete post is `afterLevels pre m`.|
|Next-root242|Actual high53, SAME opened16, actual candidate-afterstate next-root|Both reply cells feed group1 additions. The next full post is `afterRoot m`; groups0/2 remain the append posts.|
|Carry and245|Carry comes from the actual live index; source totality proves its value and bound0..20. The caller proves `min(carry,19)` selects exactly high33+index and candidate.next_frontier[index]|The SAME carry value, selected digest and opened16 reach245. Both active and inactive arms are retained, including carry20. Both returned cells feed the two additions, yielding `afterCarry m` with all three groups.|
|Low suffix|Actual low0/11/12 and the preceding complete local sums|Inherited `NKI_LowMixCaller.source` composes three native-supported five-call blocks from ZERO2. Actual constructor/cache/product laws and canonical domains are instantiated; both final cells remain.|
|250 forwarding|The deployed selector-tensor cfg branch forwards the SAME complete Public/Openings/Selectors to251|The new projected wrapper family covers all25component kinds, every nested public/frontier/opening/selector coordinate, option presence/value and variant. `NKR_DigestWrapperView.ext` derives full-carrier equality; both returned cells equal the251 reply.|

`NKR_DigestChildren.Clauses` and `Canonical` are outputs produced internally. `NKR_DigestInvocation` instantiates the source clauses at these actual arguments and arithmetic replies. Its four new middle primitives use precisely the previous full post as the next prestate. The final root exports that primitive chain, the new four-step prefix trace, the projected wrapper primitive and its derived full-carrier summary, plus source/cohort equality. It does not require an inverse association of an independently chosen raw log.

The old whole-prefix/middle relations are explicitly historical derived summaries. Their readonly input fields are source/P7 borrow framing, not new native assertions. They are absent as primitive certificates from the final root. K020, K022 and K034 timeouts grant no credit; K018's input-unwind failure also grants none.

## Six digest pairs within the26-pair table

[NKR_NATIVE_PAIRS.json](NKR_NATIVE_PAIRS.json) contains26pairs across the job. The six digest pairs below are the relevant subset; the other20 are not extra digest evidence. This review checked both receipt hashes against the table, positive SUCCESSFUL and negative FAILED stdout, and retained admission/source/graph/lock records for all12runs.

|Positive/control|Actual primitive|Positive wall s / peak KiB|Typed use|
|---|---|---:|---|
|K058/K059|`NKR_Digest_prefix_step_cut`|17.173 /651132|One actual binding plus two additions, arbitrary3x2prestate; four-step Lean composition|
|K060/K061|`NKR_Digest_split_append_window_cut`|30.240 /647468|Exact full append arguments and four reply cells|
|K062/K063|`NKR_Digest_split_levels_add_cut`|7.831 /635472|Four operand pairs and complete3x2post/frame|
|K064/K065|`NKR_Digest_split_root_window_cut`|19.089 /638100|Next-root arguments, two additions and complete post/frame|
|K066/K067|`NKR_Digest_split_carry_window_cut`|20.412 /649520|Index/carry/min arguments, two additions and complete post/frame|
|K068/K069|`NKR_Digest_wrapper_argument_window_cut`|35.442 /1149720|Projected full argument family and both returned cells|

All six positives exit0; all six matched controls exit1 with verification FAILED, rather than timeout or unwinding failure. All12receipts record swap0, admission exit0+allowed:true, MemoryHigh6G/MemoryMax8G/MemorySwapMax0/TasksMax64, offline Cargo, successful frozen-graph validation without edge errors, source-check errors empty, and unchanged frozen Cargo.lock. The lock hash is `5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef`. Resolved feature lists remain in each graph record; the validator's closure result is not a claim that excluded workspace-only tooling packages were built.

The exact KMX patch hash in common inputs is `bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67`. Common source inputs match within each positive/control pair; only the negative inversion configuration changes. The admitted digest sources are pinned as prefix-step `2205e30d801d33119871f5d82850426487a75ae3a565d5ea9576601dfb8d34a9`, middle splits `16ab42e2ed17b638c97ef5532aede22cc1684340a1518f6725a35dd29f0ba0d1`, and projected wrapper `47486a32df5925a4bdab1e817fb0230e135b578344b66903fa603e1605048a67`.

Inputs are fully arbitrary valid native carriers, generated with flat primitive arrays. The discarded one-hot representative proposal was not used to generalize a restricted native domain. No native field multiplication, writable static or Option<fn>-dependent credit is introduced. Low-mix multiplication support is inherited and paired with named Lean laws as documented in [NKR_DigestStubs.md](NKR_DigestStubs.md).

## Premises, tool trust and adoption

The root takes actual Public/Openings/Selectors data and only these proof domains: canonical opened.z16/high64/low16, plus `Domain public` naming canonical anchor/nullifier/change/next-root, recipient digest when Some, and the actual live/candidate frontier digests. Carry/min obligations are derived internally. There is no endpoint equation, desired returned carrier, successful-child premise, arbitrary operation dictionary, Run, selected execution witness or cohort-equality premise. Canonicality is not silently weakened to a fixture or Boolean-opening restriction. An enclosing caller must still establish these SAME-input domains; this review does not create a new headline/game assumption or independently prove every upstream caller domain.

The Rust-harness-to-Lean primitive association is a reviewed(ai)(5) transcription under P6/D188 composition-trust optionA. Kani's native semantics, compiler/ABI, exact KMX/std interpretation and source-to-release-artifact correspondence are retained boundaries. This is **tool-trust reclassification, not trust removal**. Lean then supplies child-domain discharge, field laws, frame joins, finite induction and complete cohort association. Neither standard-only axioms nor the native PASS verdicts erase those boundaries.

The row packets classify NJX242/245/246 as CLOSED in ledger19 and consume them at SAME arguments. NKI235 remains a candidate awaiting the next authoritative ledger, including its234dependency. Its complete four-cell output is used without assuming child success; its adoption is still pending. New250 additionally depends on adoption of new251. No review or candidate label can bypass these dependency conditions.

## Gate failure is decisive for credit

Both permitted combined-import attempts, L182 and L184, exited1. The retained diagnostics identify source-level lookup/parsing of the private helper display name `rows_ext` from `NKR_SumCopyFull`; quoting the displayed private name in L184 still produced unknown identifier/constant errors. This is not evidence of a digest counterexample, but it is an incomplete acceptance gate and cannot be waived as unrelated.

Consequently, focused L168 and the six native pairs establish retained component evidence only. A diagnostic private-level raw axiom audit is not a replacement for successful combined import, NFX scan and the required complete gate. All six packets225/232/251/250/220/218 remain local-gate-incomplete; authoritative delta remains0, neither digest row is CLOSED, and TX1:256 and the100-bit per-attempt/privacy/two-transaction release target remain unestablished. No further scope or source repair was performed by this review.
