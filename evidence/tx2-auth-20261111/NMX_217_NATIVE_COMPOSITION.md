# TX2:217 segmented native/reference packet

Frozen target: `r1_pool_adapter.rs:448–520` at
`4bb3b3f51e16b4525f1d10336e2b0bcbbd775387`. Replacement for failed actual-body
Aeneas extractions: the explicitly authorized (ah) reference/segment route.
Reviewed-transcription label: **ReviewedTranscription-TX2:217**. The lead owns
its trust-appendix entry; this job edits no trust row. This is a P6 source/native
packet, not an Aeneas extraction of the actual decoder and not a whole-buffer
Kani unwind. The row is submitted only as a CANDIDATE for the next ledger gate.

Primary reference: the byte-identical `NCV_reference.rs::decode_lane_ref`,
emitted by pinned NCV_E008 as `NCV_Reference.decode_lane_ref` (Funs SHA256
`a5ed82cbdb22fa1f2a824984e730c3c4f1fe3b2237c138ee561419aef20fb379`).
`NMX_R3_LaneTotal.value` covers every raw slice length and every Result;
`NMX_R3_LanePort.pure_eq` ports every mathematical byte list, materializing a
slice only after its own first length check. `NMX_R3_LaneAllocation.complete`
restores precisely the final Box's successful return OR silent abort. No
allocation, abort or event is introduced on any earlier error arm.

## Source order and same arguments

| Frozen occurrence | Native packet / interpreted primitive | Lean association and domain discharge |
|---|---|---|
| first `bytes.len()!=768` | actual function K005/K006; all-usize guard K012/K013 | LaneLength, ReferenceLength, LaneTotal; all non768 lengths rejected before a read; no input extent premise |
| lane magic/version/count/arity/depth | inherited NDB_K041/K042 | LaneHeader, ByteCompare; original bytes0..8, lane-count conversion included |
| format binding bytes8..40 | NDB_K043/K044 | Constants.binding, Slices.range_total/image, LaneHeader |
| reserved bytes73..80 `.iter().any` | K025/K026 | BoolReject.any_ne, Zero.value, exact seven-byte window in LaneHeader |
| master copy bytes40..72 and zero test | std item / KMX value laws for copy; K019/K020 for native array zero | PrimaryWindow.bytes32, Slices and LaneMaster; exact32 extent derived from the first guard |
| tree view bytes80..768 | std slice law | Slices.drop_total, NativeWindow.extent, LaneTree; tree length688 internal |
| tree magic/version/depth/hash/encoding | NDB_K039/K040 | LaneTree; original tree0..8 |
| `u64::from_le_bytes(tree[8..16])`; capacity | pinned std little-endian law and native scalar comparison | Word64.value/fixed and LaneCounter.capacity/value; all u64, including >capacity rejected |
| first actual `decode_digest_canonical(tree[16..48])` | CLOSED TX2:146; native all32byte differential NDB_K007/K008, also reached by K015/K016 | DigestBridge.value at SAME32byte root window; LaneDigest; all child errors mapped to InvalidAccountData |
| frontier zero initialization | Rust array aggregate/std item | PrimaryFrontierRun initial Prefix0 and FrontierTotal; no allocation |
| one arbitrary `iter_mut().enumerate()` pre-state, level<20 | NDB_K059/K060 selection/write/frame | NativeFrame.write_unique composes universal selected and untouched coordinates into full updated-array equality |
| loop child `tree[48+32*level .. +32]` and assignment | proof_for_contract K015/K016 on exact frozen assignment; modifies(node) | NativeWindow.frontier_window, FrontierWords, DigestBridge; NativeStep.accepted uses full write/frame; native before-value is computed from incoming arbitrary node, not assumed as a row clause |
| loop vacant-node guard | proof_for_contract K017/K018 on exact frozen predicate, modifies() | ScalarShift plus FrontierCarrier; NativeStep.accepted/rejected; level<20 and next<=capacity established by source loop and preceding capacity rejection |
| loop induction / all early exits | one native iteration only; NO20-step native unwind | PrimaryFrontierRun, FrontierFailure/Reject, FrontierTotal and FrontierBridge; symbolic arbitrary-index induction, all first-failure positions; NativeStep gives same emitted body at native post-state |
| final next==0/root!=EMPTY20 guard | NDB_K037/K038 | LaneFinish, Constants.empty and DigestEquality; every raw root representation and every u64 |
| exact returned record and final Box | proof_for_contract K027/K028 on exact frozen initializer after separate guard; deep equality of ALL fields; modifies() | NativeFrame.lane, LaneFinish, LaneCarrier; original bump byte72, lane byte5, master, next, root, all20 frontier rows; LaneAllocation restores both allocation outcomes |
| every Err / mapping / `?` | NDB_K029/K030, K015/K016; no stub_verified | LaneTry.source/fold, LaneQuestionCuts, LaneTotal; exact InvalidAccountData and empty event prefix |

The elementary native predicates differ from the primary reference only by the
proved byte/value representations. Their source uses, literal constants and
addresses are recorded above; original buffers are immutable. The source-order
fold is `NMX_R3_DecoderFold.source_eq_reference`; its root and full allocation
observation theorem are `NMX_R3_DecoderFold.root` and `.complete`. The row root
has no own-input clauses, child-success premise, extent premise, free Ops,
PoolLib or DeployedIds construction. Its universally quantified pointwise
allocation choice represents both outcomes of the existing std allocation item.
The native contract postconditions in NativeStep are intermediate segment
outcomes supplied by the native certificates, not parent caller restrictions.

Native tool-semantic transport and the reviewed transcription are retained
option-A trust classifications, not removed assumptions. The packet does not
claim a single Kani verification of the whole expected-length function: its
certificate is the authorized source-ordered segments plus rule-B Lean induction.
The NDB snippets alone were partial; this packet adds all-result reference folds,
precise original-window/extent laws, universal native write/frame association,
complete final-record construction, and allocation observations. The remaining
judgment of the native contextual composition is explicitly the ledger gate's.

## Exclusions

K021 combined128byte prefix and K023 final guard plus203-coordinate projection
both hit the unchanged90second CBMC limit. Neither contributes credit; neither
was rerun unchanged. Their split replacements use the component chain above,
K025/K026 and K027/K028. K022/K024 were never launched. K010's missing Arbitrary
compile error is NOT an intended failing control. No stub_verified on a
Result<Box<...>> (or any other return type) is installed or used by this packet;
its interface-calibration pilot is excluded. Every used native property has its
own passing actual-body/segment run and intended semantic failing control.

NDB reuse is checked in `NMX_217_NDB_COMPONENTS.json`: frozen source, deployed
feature sets, offline frozen dependency graph, unchanged Cargo.lock, exact KMX
patch, passing checks and intended negative assertion failures. New runs retain
the same information individually. Harness edits exist only in the scratch
copy and the retained patch. Repository crates/programs/Cargo.lock are unchanged.
