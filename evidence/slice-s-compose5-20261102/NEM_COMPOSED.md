# Current NEM result

**50/97 composed rows CLOSED; 1/7 roots CLOSED.** Added 28 rows to NEL baseline22. 110/110 Kani and21/80 Lean used. This is incomplete; no headline soundness or release claim. Native semantic transport remains P6/D188 option A reclassification; RuntimePersistence and all approved trust rows remain.

| Root | Rows CLOSED | Theorem/status |
|---|---:|---|
| decode_public_statement_box | 0/1 | OPEN: no composed root theorem claimed |
| validate_pool_v1_pair_forest_terminal_statement_v1 | 2/2 | `NEM_ValidatorComposed.result_state_effects` |
| encode_pool_v1_pair_forest_terminal_statement_v1 | 0/1 | OPEN: no composed root theorem claimed |
| reconstruct_asq8_statement | 0/1 | OPEN: no composed root theorem claimed |
| decode_pool_v1_pair_forest_terminal_request_v1 | 0/1 | OPEN: no composed root theorem claimed |
| scan_proof_buffer | 0/1 | OPEN: no composed root theorem claimed |
| emit_result | 0/1 | OPEN: no composed root theorem claimed |

The sole closed root has no inner callee hypotheses. Its full concrete same-call model G theorem appears below; the native corollary additionally retains only the root own typed PacketDomain/PhysicalInterpretation and approved tool/runtime trust. Six unproved native root associations are not hidden as named leaf hypotheses. Exact obstacles for every remaining member and edge are in NEM_STOP_AUDIT.json and NEM_EDGES.json. All 33 new theorem audits use only propext, Classical.choice, Quot.sound.

The following stage notes retain the evidence history. NEM_VALIDATION_FINAL.json is the final row result, not intermediate counts.

# NEM slice S composition

Target not yet established. Baseline: **22/97 composed rows CLOSED, 0/7 roots**.
Frozen Rust: `4bb3b3f51e16b4525f1d10336e2b0bcbbd775387`.
Adopted headline: `AspisR1.RPx_Deployed.deployed`; SInt2 coherent objects.

The unchanged NEL validator and its NED/NEE/NEJ checks are imported read-only.
NEM adds checks only. Source/module/object import hashes: NEM_HOST_PINS.json.
No native root theorem is established. Its intended conclusion remains exact
native/cohort Result, state and ordered effects on its own PacketDomain and
PhysicalInterpretation, with only approved trust rows and RuntimePersistence.
P6/D188 amendment-five option A is reclassification, never trust removal.

Order: payment child (per-window frames, same-call binding, NEE reached-child
instance), output-lane child, late child, then validator root and later roots.
New native iterator work completes a payment descendant obligation; no local
support result is counted as a composed row before the complete certificate.

Shipped crates/programs are unchanged; no ELF rebuild trigger. No release
manifest or new release claim. Privacy, two transactions, RuntimePersistence,
L154, narrowed D188, and 100-bit PER-ATTEMPT target remain unchanged.

Digest descendant stage: **23/97 composed rows CLOSED; 0/7 roots**. NEM_L001 instantiates the accepted next-row/suffix induction on the same raw digest and arbitrary external frame; both printed axiom sets are [propext, Classical.choice, Quot.sound]. Native NEM_K002/003 and K004/005 pass/fail under the frozen dependency/feature/source gates. K001 was an excluded missing frozen include input error; fixed by restoring the pinned includes, with no changed property. Ten new mutation tests pass, including mutations with refreshed review hashes. Payment/common and all roots remain OPEN.

Common stage: **26/97 composed rows CLOSED; 0/7 roots**. The earlier digest-only receipt had 23 rows because TX2 inventory uses syntax rather than expression; NEM_validate now checks either exact inventory representation. Common source windows, untouched byte 7/reserved suffix, total child domains and same-call native instances are checked together. No root closure is claimed.

Payment child stage: **30/97 composed rows CLOSED; 0/7 roots**. Native rejection prefixes and all five suffix call/window instances include matched corrupt-reply/argument/value controls. NEM_PaymentReached.payment_reached supplies NEE's first reached-child law on the same statement argument. NEM_L002 and L004 print standard axioms only. L003 recursion-depth failure is excluded; L004 uses a direct indexed-list rewrite. Withdrawal amount is a primitive u32; the conservative M31/WideExact alternatives are explicitly resolved from the frozen field type and native amount call.

Output-lane child stage: **34/97 composed rows CLOSED; 0/7 roots**. First-byte and output-lane callers reuse NEL's unchanged total native argument/Result/order and corrected corrupt-reply control pairs. NEM_L005 supplies the second reached-child law with standard axioms. No new Kani proof or new trust item was needed for this stage.

Late validator descendants: **38/97 composed rows CLOSED; 0/7 roots**. NEM_K026..031 and K033/034 combine exact scalar prefixes with one arbitrary frontier iteration; NEM_L006 reuses NBH induction and emitted association with standard axioms. K032 is an excluded nested-module qualification error repaired in K033. K035..038 separately establish actual std u8 fill value and complete frame for both output widths; their controls fill with the wrong value and fail. NEM_STD_FILL.json pins the compiler specialization to write_bytes (no protocol-loop unwinding). Encoder and parent late instances remain OPEN.

Late encoder descendants: **42/97 composed rows CLOSED; 0/7 roots**. Each of 15 header/root windows has a native value/frame pair; extra wrong-root controls establish actual child places. Native count, typed destination geometry and small byte updates are separate, replacing the excluded NEL_K054 shape. NEM_L009 supplies instantiated same-cursor/full-frame laws and imported induction with standard axioms. L007/L008 (slice carrier simplification errors) and K059 (misspelled own constant) are excluded. Fixed initialization, all-length rejection prefixes and actual std fill are checked separately. Named legacy decode qualifications are replaced by a direct encoder proof reaching no decoder; no decoder row gets credit.

## Validator root closed

46/97 composed rows CLOSED; first root 2/2 rows CLOSED. NEM_L018 compiled the concrete same-call model G theorem below. The hybrid native corollary follows from the frozen caller association, CLOSED child certificates and approved composition-trust option A, with only the root own typed PacketDomain/PhysicalInterpretation ambient qualifications. This is P6/D188 trust reclassification, not removal. No inner bridge/domain/interpretation hypothesis remains. External state is unchanged; the local mutable late buffer does not escape.

```lean
import NEM_LateOracle
set_option autoImplicit false
noncomputable section
namespace NEM_ValidatorComposed
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder NBN_StatementResult

/-- Concrete model G for the three SAME calls certified natively. The hybrid
native correspondence is checked separately by NEM_validate; this theorem
introduces no inner callee domain, interpretation, or bridge hypothesis. -/
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

#print axioms result_state_effects
end NEM_ValidatorComposed
```

Axioms: propext, Classical.choice, Quot.sound. Native caller source erasure, complete Results, ordered effects and same child places are checked by NEM_root_checks.py against NEE_K052/053 and NEL_K006/007. Original NEM native_pair remains unchanged; a separate inherited-pair adapter checks the original differently named positive/negative harnesses, identical patches and all frozen/cap/feature/lock gates. 42 mutation tests passed.

## Transition-kind caller instances

NEM_L019 closes the three typed getter/parser instances using inherited NBN_U05.encoder_kind and NBD_TerminalProjection.source_kind; no adopted getter is invented. K102..110 provide actual native calls, arbitrary prestate scalar frames and every invalid parser byte, with six failing controls. The controller expected exit 10 on K103 but the pinned Kani returned 1 for its expected verification failure; the own controller was corrected to require exactly exit1 plus the failure banner, then continued from K104 without rerunning K103. All 110 Kani attempts are used. The additive validator reports 50/97 rows CLOSED (first root remains 2/2, other roots OPEN).

```lean
import NBN_U05
set_option autoImplicit false
noncomputable section
namespace NEM_KindInstance
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder NBN_StatementResult

def write (before : Nat → U8) (value : U8) (j : Nat) : U8 :=
  if j=5 then value else before j

/-- Actual enclosing encoder's SAME variant tag, with the complete scalar-write frame. -/
theorem statement_window (s : Statement) (before : Nat → U8) (j : Nat) :
    write before (NBN_EncoderBytes.tag s) j =
      if j=5 then (match s with | .PrivateTransfer _ _ => 1#u8 | .Withdrawal _ _ => 2#u8)
      else before j := by
  rw [NBN_U05.encoder_kind]
  rfl

/-- A payment carrier keeps its SAME public value and variant when joined to any common carrier. -/
def join (c : NBD_TerminalProjection.Common)
    (p : Sum NBN_ValidatorSummary.Transfer NBN_ValidatorSummary.Withdrawal) : Statement :=
  match p with | .inl t => .PrivateTransfer c t | .inr w => .Withdrawal c w

theorem payment_window (c : NBD_TerminalProjection.Common)
    (p : Sum NBN_ValidatorSummary.Transfer NBN_ValidatorSummary.Withdrawal)
    (before : Nat → U8) (j : Nat) :
    write before (NBN_EncoderBytes.tag (join c p)) j =
      if j=5 then (match p with | .inl _ => 1#u8 | .inr _ => 2#u8) else before j := by
  cases p <;> exact statement_window _ before j

/-- The caller supplies this SAME header byte. Both valid and every invalid byte preserve state. -/
theorem parser_result_frame {State : Type} (header : Nat → U8) (state : State) :
    (pool_v1.pair_forest_terminal.transition_kind (header 5),state) =
      (ok (NBD_TerminalProjection.kind (header 5)),state) := by
  rw [NBD_TerminalProjection.source_kind]

#print axioms statement_window
#print axioms payment_window
#print axioms parser_result_frame
end NEM_KindInstance
```

All three theorem audits: propext, Classical.choice, Quot.sound. These compose scalar-member rows; they do not close any later enclosing root.

## Later-root review and source dispatch resolution

Four terminal encoder inventory alternatives are resolved before pruning: the actual receiver is Statement for transition_kind and primitive u64 for checkpoint_sequence.to_le_bytes. NEM_EncoderReceiver.sequence_width (NEM_L020) and NEM_KindInstance.statement_window are the source/width/tag witnesses, with successful full-file typechecking in NEM_K102 and its failing control. This adds no composed row and does not certify the mutable late window. TX2 parser constructor keys use syntax rather than expression; the gate now checks both exact schema variants, with a dedicated mutation regression. Final count remains 50/97.

NBU_K042/043 were reviewed read-only: their encoder cut returns Result<()> and uses a late closure that leaves output untouched. It cannot transport the exact returned 1880 bytes or arbitrary mutation of the same late window. These are precise remaining native obligations, not missing arithmetic lemmas. NED_CodecComposition.encoder already supplies the concrete emitted/model substitution; it is reused, not reproved or presented as native closure.

NEM_L021 audits all 33 new theorem names at their exact accepted source hashes. Only propext, Classical.choice and Quot.sound occur. No complete frozen release manifest was run: six requested roots remain OPEN, so this is not a formal release result.
