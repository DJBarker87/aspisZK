# Slice S composition after rule 16

**6/97 composed rows CLOSED; 0/7 roots CLOSED. Target not yet established.**
This supersedes the 12/97 stage-3 claim and intermediate 10/97 figure.
Frozen source: 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387; headline
AspisR1.RPx_Deployed.deployed on the coherent SInt2 owners. The six accepted
rows are transfer_common, withdrawal_common and payment digest_is_canonical
in TX1/TX2. See NEE_VALIDATION_SUMMARY.json and NEE_RULE16_AUDIT.md.

NativeContractSemanticTransport is P6/D188 option A RECLASSIFICATION, not trust
removal. RuntimePersistence, the approved trust rows, L154, privacy, 100-bit
per-attempt soundness and the two-transaction design are unchanged.

| Slice root | Composed rows CLOSED | Status |
|---|---:|---|
| decode_public_statement_box | 0 | OPEN |
| validate_pool_v1_pair_forest_terminal_statement_v1 | 0 | OPEN |
| encode_pool_v1_pair_forest_terminal_statement_v1 | 0 | OPEN |
| reconstruct_asq8_statement | 0 | OPEN |
| decode_pool_v1_pair_forest_terminal_request_v1 | 0 | OPEN |
| scan_proof_buffer | 0 | OPEN |
| emit_result | 0 | OPEN |

No native-root theorem with the authorized hypothesis list has been proved.
No model function is relabelled as frozen native code. The other six roots
were not started, following the binding first-root order.

## First root: caller support and exact model theorem

K052/K053 pass/fail the original oracle_domain_positive/negative properties
with harness-local records, arbitrary full child Results, exact argument
checks, full 1520-byte mutable reply havoc and ordered call logging. Both
positive branch covers are reached. The exact source projection is recorded
in NEE_LOCAL_VALIDATOR_PROJECTION.json; per-attempt patches are authoritative.
This is ruling-(y) caller support, not part-(2) child-frame discharge.
K054 and its smaller prefix split K055 timed out; neither earns credit.

The complete new MODEL statement is NEE_ReachedRootModel.result_and_effects:

```lean
theorem result_and_effects (pay : Pay) (lane : Lane) (late : Late) (s : Statement)
    (payment_bridge : ∀ a, Call.payment a ∈ (NEE_ValidatorOracle.run pay lane late s).2 →
      pay a = NED_ValidatorTrace.payment a)
    (output_lane_bridge : ∀ d, Call.lane d ∈ (NEE_ValidatorOracle.run pay lane late s).2 →
      lane d = NBN_FirstByteDependency.lane enc d)
    (late_bridge : ∀ a out, Call.late a out ∈ (NEE_ValidatorOracle.run pay lane late s).2 →
      ignore (late a out) = ignore (NBN_LateSummary.run enc a out)) :
    NEE_ValidatorOracle.run pay lane late s =
      (pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1 s,
       (NED_ValidatorTrace.run s).2)
```

The explicit remaining inner laws are payment_bridge, output_lane_bridge and
late_bridge on reached calls only. The final law compares the caller-observed
late status; NEE_ValidatorMutation proves arbitrary temporary-output mutation
is discarded. No root output equality is hidden inside PhysicalInterpretation.
This model theorem alone supplies NO native child instance or frame.

NEE_L029 checks this statement; NEE_L024 checks six arbitrary-reply domain/
ordered-prefix facts, including exact same nullifier and 1520-byte late prestate.
NEE_L028 checks reached-only substitution through rejection, child errors and
divergence. NEE_L025..027 failed elaboration drafts are retained and excluded.
Accepted new theorems use only [propext, Classical.choice, Quot.sound].
NEE_L030 is the one final focused axioms audit, not a full frozen replay.

The reused complete raw validator cohort equality remains
NEE_RawValidatorCohort.result (L017): for every typed model statement s,
rawValidator (NED_ReconstructCarriers.toRaw s) equals ok of the mapped complete
NED_ValidatorStatus.status s. Its only input is typed s; its printed axioms
are the standard three. This is an emitted/model equality, not native credit.

## Remaining native obligations

Common getter and tuple projection: historical direct oracle MODULES contain
written statics and are conservatively suspended; borrowed stub_verified
admission also lacks a semantic unimplied control (K039 is codegen failure).
Payment encoders: exact encode_common indexed native frame remains OPEN after
K054/K055; full callers' own frames/Results remain to be composed. Output-lane
and late encoders: local-record one-step checks and model inductions do not
supply their remaining selected native child frames/physical instances.
NEE_EDGES.json retains all 129 internal edges with certificates or obstacles;
NEE_STOP_AUDIT.json lists every one of the 61 members, retained inner names,
model source matches and exact native/Lean continuation obligations.

Budgets: 55/55 Kani, 30/150 Lean. Kani exhaustion was followed by Lean-only
work. No further pure model statement can substitute for an unproved native
frame; the member-by-member stop audit explains the under-80% Lean stop.
