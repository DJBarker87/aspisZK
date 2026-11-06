# NKQ native cuts and source support

Target not yet established. No complete native parent or composed row is claimed. `NKQ_NATIVE.patch` is the retained scratch-only patch against frozen revision `4bb3b3f51e16b4525f1d10336e2b0bcbbd775387`; research crates/programs are unchanged. All native runs used the frozen lock graph, offline resolution, deployed library features, optimized compilation, and the exact KMX mitigation. Per-attempt source/graph/lock hashes and negative controls are retained. Native domains below are component domains, not added root preconditions.

| Positive / failing control | Scope proved | Limitation |
|---|---|---|
| K003 / K004 | Exact KMX pointer-copy calibration | No parent theorem |
| K006 / K007; stability K008 / K009 | Actual137 returns the parser error and preserves an arbitrary input cell; all wire error tags | Transfer constructor, 13831 bytes, local unreachable Hash; parser oracle, not parser correspondence |
| K010 / K011 | Six original-challenge fields copied at136 | Source helper, not actual parent log |
| K012–K019 | Old mask windows | SUPERSEDED: coupled reply; receive no credit |
| K020 / K021 | Terminal inequality guard | Source helper only; full pre/post absent |
| K022 / K023 | Circle equality guard | Source helper only; full pre/post absent |
| K024 / K025 | Extra[28] selection | Source helper only |
| K026 / K027 | Root32 try_into copy at arbitrary cell | Source helper only |
| K028 / K029 | Mask input claim/alpha frames, unchanged log.cell/reply, return reply | Component oracle; no mask arithmetic value claimed |
| K031 / K032; stability K037 / K038 | Actual094 wrong-k rejection | Transfer/local Hash; no successful suffix |
| K033 / K034 | Actual094 parse rejection, every candidate error tag | Same restricted carrier; parse oracle |
| K035 / K036 | Actual094 scan rejection after parse success | Same restricted carrier; both child interpretations still to instantiate |
| K039 / K040; stability K041 / K042 | Actual136 rounds rejection, all wire error tags and root-cell frame | Transfer/local Hash; arbitrary transcript; no later suffix |
| K043 / K044 | Mask low[i] input, independent canonical reply | Arbitrary canonical3x29 claims,10 alphas, i<16; observer window only |
| K045 / K046 | Mask high[i%10] input, independent canonical reply | Same domain |
| K047 / K048 | Mask blind claims[0][27] input | Same domain |
| K049 / K050 | Mask alpha[i%10] input | Same domain; reply never equated to alpha |
| K051 / K052 | Prepare semantic slice sizes/pointers | ENTRY_ONLY; child return/post/abort not proved |
| K053 / K054 | Prepare values slice sizes/pointers | ENTRY_ONLY |
| K055 / K056 | Prepare semantic logical view | ENTRY_ONLY; no lifetime/frame result |
| K057 / K058 | Tx1 initial scratch29ZERO | ENTRY_ONLY |
| K059 / K060 | Folded-root arbitrary byte value | ENTRY_ONLY |
| K061 / K062 | Folded-root proof-cell frame | ENTRY_ONLY |
| K063 / K064 | Batch arguments at batch0 | ENTRY_ONLY; child081 remains open |
| K065 / K066 | Geometry arguments queries,0,k | ENTRY_ONLY |
| K067 / K068 | Pending weights64 argument | ENTRY_ONLY |
| K069 / K070 | Checkpoint argument sizes/values | ENTRY_ONLY; no returned bytes/native parent |

Compile-only failures: K001 missing frozen cfg path; K002 exact KMX allocator_api requirement; K005 early-bound Prefix lifetime; K030 parse_shape returns Variant, not unit. Repairs changed the scratch scaffolding, not frozen function bodies. No timeouts, memory kills, increased caps or retries of killed/timed-out shapes occurred.

## Typed bridge boundary

`NKQ_MaskCuts.LowCut/HighCut/BlindCut/AlphaCut/FrameCut` transcribe exactly the five observed mask windows; each cites the pinned Rust source hash and its passing/failing pair. `arguments` composes them at SAME c,a,i,reply and derives the complete immutable claim/alpha frames by array extensionality. These are explicit proposed native-cut hypotheses, not Lean proofs of Rust; NKQ-F3 below prevents admitting them as complete native iteration certificates. The theorem does not close136 and must not be installed as a root carrying a free child Result. Other native checks above are calibration/component receipts, not installed full native-parent cuts.

`NKQ_FromFnIndices.total` uses induction over the emitted array-construction index list. `NKQ_MaskLowStep/HighStep` prove one emitted closure iteration on arbitrary index/state with the actual bounds and state frame; `NKQ_MaskArrays` derives the exact16/10 constructors. `NKQ_ClaimsMatrix/ClaimsDomain`, `NKQ_AlphaDomain`, `NKQ_FinishMaskDomain`, `NKQ_RecordDomains/StrictDecode/FinishSlots` establish caller domains from SAME parser branches and actual returned values. They do not assume selected claim arrays, selected successful decoder results or endpoint equations at a root.

`NKQ_ObservedStages`, `NKQ_ObservedContinuations`, `NKQ_ObservedTrace`, `NKQ_FinishStages`, `NKQ_PrepareStages/PrepareBuffer`, and `NKQ_Tx1Stages` factor the adopted source models and preserve their exact Rust Err and outer fail/div alternatives. Their arbitrary operation dictionaries/source-success cases are **source-support parameters**, inadmissible as concrete native root premises. No complete native source-state/log-prefix induction for any of the four parents was constructed. The source factorization and emitted-array induction must not be described as that missing native fold.

## Remaining cuts, in execution order

136 needs complete prefix-to-claims carry; actual original-challenge record; terminal256 SAME-argument/result/error transport; mask076 full-value/domain installation; actual getter/decode/field/guard/circle/state/root construction carries; every first Err/abort and complete final Verified fields/query log. Domains for the mask and extra/beforeZ1 slots are proved, but their whole native parent transport remains open. No multiplication was attempted in Kani.

137 needs complete parse-success/public-transcript/begin/finish argument and mutation frames, exact rejected log prefixes and final Result; its136 child is open. 087 needs allocation/split/expansion/view/semantic/Prepared::new owned-state and lifetime frames around op9 and every failure path; child137 is open. 094 needs the normal parse/scan/prepare/accum/root/batch/geometry/pending/query/finish/checkpoint source-state/log fold and all first failures; children084,087,081 remain open. Entry windows do not fill these cuts.

## Read-only merged-child update

Research2553129fd7f6444fe85210c66e6a671d7b6aa721 now contains NKI terminal4 and NKL batch-merkle3 packets.256 and081 remain OPEN.084 has the merged, audited NKL_ScanRoot candidate pending authoritative ledger adoption; it is eligible for future SAME-argument consumption under the job rule, but no084 packet is consumed by NKQ because the094 complete native parent cuts/root are absent. Baseline NKN ledger status stays OPEN; do not confuse that baseline label with lack of a candidate. Thus094 lacks081/087, plus its own complete native assembly and084 candidate installation/domain proof;084 no longer needs a new scanner proof. See NKQ_CHILD_RECHECK.json.

## NKQ-F2: selected error-oracle domain

The rejection stubs select their Err tag from the SAME original bytes/root. Every enum tag is exercised, but this couples the error to the input: the receipts do not quantify an independent arbitrary child error for every fixed original input. They establish the indicated native prefix under that particular oracle only. They cannot instantiate the actual CLOSED138/134/086 or084 result at SAME input without an additional transport proof, and no such transport or row credit is claimed. Future full rejection cuts must cover independently selected replies (or prove the exact actual selector relation) with unchanged caller frames and fresh matched controls; the current allowance has no native runs left. This is an additional own-native-cut gap, not a new caller precondition or trust item.

## NKQ-F3: native array-step association missing

The mask helper executes the full fixed16/10 core::array::from_fn constructors while observing one arbitrary cell; it is not a native one-iteration certificate on an arbitrary partially initialized pre-state. NKQ_MaskLowStep/HighStep and FromFnIndices establish the emitted Lean steps/induction, but no native/model iteration association was proved. Under the binding loop method, the mask window receipts therefore remain component observations and do not discharge an admitted whole constructor/native136 cut. NKQ_MaskCuts.arguments is a conditional mathematical composition of its explicit Low/High/Blind/Alpha/Frame hypotheses; those hypotheses are proposed typed windows, not fully admitted native one-step certificates. Future native single-iteration/frame controls and source-state prefix composition are required. Zero row credit remains unchanged.
