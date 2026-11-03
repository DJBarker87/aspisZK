# Slice S continuation

Final checkpoint: 68/97 composed rows CLOSED, 37/61 functions, 2/7 roots. Imported baseline: 50/97 rows and the validator root. The new encoder root is CLOSED; five roots remain OPEN. This is partial slice completion, not a release soundness result. Sections below retain stage history; the final ledger and handoff are authoritative.

Imported model theorem: `NEM_ValidatorComposed.result_state_effects`; full statement and native certificate components are retained in `evidence/slice-s-compose5-20261102/NEM_COMPOSED.md`. Its only native qualifications are the root PacketDomain/PhysicalInterpretation and approved trust, including P6/D188 option A reclassification. Encoder root now CLOSED after native and model composition checks; see the section below.

NEQ_L001 rechecks imports and prints the validator theorem axioms: propext, Classical.choice, Quot.sound. This is summary-based #print axioms, not a claim of a complete raw walk or release replay.

Late mutation stage: K002 support; K003 inverted ensures fails; K004 real-body frame passes and K005 same unimplied assertion under stub_verified fails; K006 modifies violation fails. K008 caller complete outside-window frame passes; K009 wrong window and K010 unjustified inside-window value fail. K007 was an excluded error-wrapper type error. K011 native tail passes; K012/013/014 wrong late place, payment place and suffix byte fail. L002 proves same allocation borrow/rejoin, arbitrary full child poststate frame and payment-disjoint preservation. No new composed row yet.

## Encoder root closed

Model theorem (no inner hypotheses):

```lean
theorem result_state_effects {State : Type} (s : Statement) (state : State) :
    let observed := run pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1
      NEM_PaymentReached.pay NEM_LateOracle.late atomic_statement.encode_digest_canonical s
    (observed.1,state,observed.2) =
      (NBN_StatementEncoderSummary.observe (AspisS6OuterNativeInstalled.encode s),
       state,(NED_EncoderTrace.run s).2) := by
  dsimp only
  rw [substitution,NED_EncoderTrace.erases]
```

Native components: K002..010 fixed1520/full nested-Result interface controls; K011..014 same late/payment arguments, full child mutation, errors/order and one suffix-copy step; K015..035 ten actual header scalar/copy windows and failing controls; K036..039 validator/common/zero prefix; K040/041 typed1880 returned-byte carrier and corrupt-byte control; K042/043 frozen expression geometry. The windows compose using NEQ_LateBorrow, NEQ_RootFrame and the pinned KMX value/induction laws. NEQ_EncoderDomains.reached_domains supplies exact same-argument call domains; header_length discharges144-byte prefix geometry. NEM conservative alternative certificates are retained unchanged.

Remaining native conditions are only the root own typed PacketDomain/PhysicalInterpretation and approved runtime/tool trust. P6/D188 option A is trust reclassification. The native link is the checked hybrid certificate, not a kernel-only Rust theorem. The model theorem preserves full Result, external state and the ordered argument-bearing trace, including rejection prefixes. #print axioms: propext, Classical.choice, Quot.sound (L007); frame L009 and domains L011 use only permitted axioms. These summary-based prints do not claim raw-walker completeness.

No shipped Rust changed. Frozen revision4bb3b3f51e16b4525f1d10336e2b0bcbbd775387; features/dependency graph, offline lock, cgroup limits and tool hashes are checked in every native receipt. No ELF rebuild trigger. NEQ_ENCODER_VALIDATION.json confirms encoder1/1 CLOSED, validator2/2 CLOSED: 51/97 rows,2/7 roots. NEQ_ENCODER_TESTS.log records18 passing tests, including full-ledger missing-root, wrong-edge-prestate (refreshed review hash), and missing-child mutations, each keeping the encoder OPEN. NEQ_EDGES.json has57 certified internal edges and72 OPEN; edge certification alone does not close the caller.

## Result validator descendant closed

`NEQ_ResultValidator.result_state_effects` (L017) equates the full native-oracle G Result, unchanged arbitrary external state and exact ordered lane/afterstate calls to the adopted `validate_result` model. No inner hypotheses remain. `lane_domain` and `after_domain` fix the same nullifier and verified afterstate from the actual typed result. K044 is the exact frozen caller instrumented with local full-Result records; K045/046/047 wrong lane place, afterstate place and reply fail. Source erasure is exact and immutable inputs/pure CLOSED children give the complete external frame. NEQ_result_validator_checks.py and inherited NDT gates accept the certificate. This is P6/D188 option A trust reclassification.

NEQ_RESULT_VALIDATOR_VALIDATION.json confirms **52/97 rows CLOSED,2/7 roots**, with59 certified internal edges and70 OPEN. The emit_result root remains OPEN: result encoder and result-against-statement have no selected native claims in the pinned baseline. Native result-encoder windows are support only, not composed credit.

All six new descendant theorem #print axioms contain only propext, Classical.choice, Quot.sound (L017 exit0, wall2.545449175s, RSS5305928KiB,swap0; exact source/dependency/revision and cgroup fields in NEQ_L017/receipt.json). L012..016 are excluded elaboration/simplification failures, not accepted theorem evidence.

The large overlay is committed as NEQ_LEDGER_DELTA.json.xz plus uncompressed .sha256. Five transport mutation tests pass. The running result-validator test process had imported the previous plain-JSON reader before compression: both actual full-ledger composition mutations passed, then its later gate setup hit FileNotFoundError. Those passing composition tests were not repeated; the missing gate class is run separately with the current hash-checking reader. No proof was resubmitted or evidence gate relaxed.

## Nullifier and parser descendants closed

NEQ_NULLIFIER_VALIDATION.json confirms54/97: both actual borrowed nullifier getters have exact native place/lifetime pairs (K083/084, K085/086), uniform frozen source projection checks, and NEQ_NullifierDomains full raw-field/state/effect model instances (L019). Six gate mutations pass. K082 was an excluded own Rust or-pattern type error; it was corrected to two arms without renaming the harness.

NEQ_DECODE_VALIDATION.json confirms **60/97 composed rows;2/7 roots CLOSED**. Added complete header, M31-from-bytes and canonical-digest parser members, all on raw typed bytes with every rejection and successful value. K087..095 have matched changed-value and changed-guard/argument controls. L020 reuses exact emitted definition laws for Result/state/effects and supplies actual four-byte call domains; L021 derives the canonical returned M31 value from its guard. No field multiplication or protocol loop was evaluated. The frozen digest decoder is explicitly unrolled8; every arbitrary observed output limb and every error is checked. No new local bridge status is inferred for OPEN NDT rows.

The emitter remains OPEN for the exact obligations in NEQ_EMIT_OBSTACLES.md. The immutable parser descendants proceed under the next root's subtree. Native fixed-width and common-decoder checks are additional WIP until their full model/frame/call-domain certificates are validated.

## Final composed result

**68/97 rows CLOSED;37/61 functions;2/7 roots.** Baseline50/97: added18 rows. NEQ_VALIDATION_FINAL.json is authoritative. Five root theorems are not claimed, and no whole-root bridge is hidden as a leaf hypothesis. NEQ_STOP_AUDIT.json enumerates every member and why further model lemmas cannot supply its missing native witness.

| Root | Rows CLOSED | Model theorem / obstacle |
|---|---:|---|
| validate_pool_v1_pair_forest_terminal_statement_v1 |2/2| imported NEM_ValidatorComposed.result_state_effects |
| encode_pool_v1_pair_forest_terminal_statement_v1 |1/1| NEQ_EncoderOracle.result_state_effects |
| emit_result |0/1| combined native timeout, unselected result leaves, op53 effect-frame obstruction |
| decode_pool_v1_pair_forest_terminal_request_v1 |0/1| full320 parent/native returned Request association missing |
| reconstruct_asq8_statement |0/1| native common/Box construction/caller association missing |
| decode_public_statement_box |0/1| native full decoder/Box wrapper association missing |
| scan_proof_buffer |0/1| native one-iteration/runtime slice+reply association missing |

For each CLOSED root the MODEL theorem has no inner Prop hypotheses. Native correspondence is a separately validated hybrid certificate, with only the root's own typed PacketDomain/PhysicalInterpretation and approved runtime/tool trust retained. P6/D188 option A is reclassification, never removal. RuntimePersistence remains approved; the headline, L154 statement parameter and narrowed D188 are unchanged. This is not a kernel-only theorem from Rust or a100-bit soundness conclusion.

The imported validator's full statement is retained below (no reproof). Native components are NEE_K052/053 and NEL_K006/007, CLOSED same-call payment/lane/late laws and unchanged NEM_root_checks.py. NEQ_L001 reprints its permitted axioms; final audit reprints it with all new theorems.

```lean
theorem result_state_effects {State : Type} (s : Statement) (state : State) :
    let observed := NEE_ValidatorOracle.run NEM_PaymentReached.pay NEM_LaneReached.lane
      NEM_LateOracle.late s
    (observed.1,state,observed.2) =
      (pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1 s,
       state,(NED_ValidatorTrace.run s).2) := by
  have same := NEE_ReachedRootModel.result_and_effects NEM_PaymentReached.pay
    NEM_LaneReached.lane NEM_LateOracle.late s
    (fun a reached => NEM_PaymentReached.payment_reached NEM_LaneReached.lane
      NEM_LateOracle.late s a reached)
    (fun d reached => NEM_LaneReached.lane_reached NEM_LateOracle.late s d reached)
    (fun a out reached => NEM_LateOracle.late_reached s a out reached)
  rw [same]
```

Validator axioms: propext, Classical.choice, Quot.sound. Encoder full statement is above; its source and all definitions are in NEQ_EncoderOracle.lean. The typed1880 Result is preserved through NED's already proved faithful observation and NEQ_RootFrame.array_ext; complete returned bytes are checked natively by K040/041. Root ambient qualifications remain exactly as stated above.

## Final descendant stages

Generic unwrap conversions and common decode add four rows after60. K096..101 check complete owned4/8/32-byte success payloads; K106/107 check the actual borrowed32 place. Generic emitted Ok/Err laws are reused in L022; no new native Err/panic credit is claimed. Actual callers derive successful fixed conversion from bounds. K102..105 establish exact borrowed digest windows, full child Results and every returned Common field/error prefix. L023 supplies concrete G substitution with no inner hypotheses.

Both public payment decoders add four rows after64. K109..116 check exact typed216 native bodies, full arbitrary common/digest/validator replies, every returned field and error order with matched wrong argument/reply/value controls. L024 gives full-Slice model substitutions including WrongLength. L026 gives the element-parametric borrowed-width guard and same complete fixed216 value; L027 discharges all source windows and resolves the primitive u32 fee before pruning false M31/WideExact targets. The new guard shape is explicit in NEQ_ZST_FINDING.md: K118/119 prove ONLY the all-usize scalar status guard. K117's extra zero-sized pointer assertion remains excluded; concrete u8 places are separate native certificates. This is P6/D188 reclassification with no new trust row.

K120 failed own generator token compilation. The corrected prefix patch is committed UNRUN; it closes no root or edge. Native budget is exactly120/120. Actual outcome classifications, including controls versus excluded attempts, are in NEQ_ATTEMPT_CLASSIFICATION.json. No failed, timed-out or unrun source is accepted as a proof.

All accepted new theorem prints use only propext, Classical.choice, Quot.sound (some none). These are summary-based #print axioms; no raw-walker completeness or fresh release closure replay is claimed. Exact command, target, source revision/hash, dependency/library pins, limits, exit, wall, RSS, swap and prints are in every per-attempt receipt and NEQ_ATTEMPTS.jsonl.

Final consolidated axioms audit: NEQ_L028, exit0, wall2.74751663999632s, peak5259204KiB, swaps0; source revision5ef45dcc191a4cf867d8aa6011a15f63b7e56264 with recorded dirty source hashes. Every new theorem prints only standard axioms or none. Exact output: NEQ_L028/stdout.log; final statement imports: NEQ_FinalAudit.lean. Final edge inventory:75 CLOSED,54 OPEN,129 total. No additional root closure follows from edge count.
