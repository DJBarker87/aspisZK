# Slice S composition (in progress)

Current checked result: **12/97 composed rows CLOSED; 0/7 roots CLOSED**.
The frozen target is 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387 and the
headline is AspisR1.RPx_Deployed.deployed on the coherent SInt2 owners.
NativeContractSemanticTransport is P6/D188 option A **reclassification**, not
assumption removal. RuntimePersistence, L154 and the security contract remain.

The closed leaf functions are M31::to_le_bytes, statement common getter,
statement_public_common, transfer_common, withdrawal_common and payment
relation digest_is_canonical. Their twelve TX1/TX2 rows and full certificates
are in NEE_VALIDATION.json / NEE_LEDGER_DELTA.json. Exact actual-function
contracts use explicit empty modifies, arbitrary complete typed inputs,
matching failing controls, deployed features, frozen offline dependency graph
and exact KMX patch. No stub_verified, function pointer, field multiplication,
SHA or whole protocol loop is used in these direct contracts. Imported model
proofs are reused, not re-proved. All inner named leaf hypotheses are explicitly
discharged by these same-input/frame/carrier certificates.

The M31 self and WideExact alternatives are resolved by the frozen u32 receiver,
the emitted primitive theorem and distinct 4/32-byte widths. The original slice
spec and NED checks are unchanged. NEE additionally accepts certificates for
self edges already retained by NDT but omitted from the slice edge list; absent
or wrong certificates keep the row OPEN. Seventeen mutation tests pass,
including a wrong model theorem even after resealing its metadata.

## First root: validator (native composition remains OPEN)

The complete **emitted/model**, not native-root, statement now proved is:

```lean
∀ s : NBN_StatementResult.Statement,
  AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_forest_terminal.
    validate_pool_v1_pair_forest_terminal_statement_v1
      (NED_ReconstructCarriers.toRaw s) =
  Aeneas.Std.Result.ok
    (NED_LateValidatorCohorts.mapResult
      NED_ErrorCarriers.toRawPoolV1PairForestTerminalFormatErrorV1
      (NED_ValidatorStatus.status s))
```

Theorem: NEE_RawValidatorCohort.result, NEE_L017, hypotheses: typed `s` only.
`#print axioms`: [propext, Classical.choice, Quot.sound]. This closes the
previously unfinished raw validator aggregation by small source prefix,
continuation, payment and tail transports; no full-root simplification or
heartbeat increase. NEE_ValidatorOracle.substitution/result/effects give
ruling (y)'s model substitution and same ordered argument log.
NEE_ValidatorMutation.result_and_effects proves arbitrary whole-buffer reply
mutations are discarded even on error/divergence. Accepted statements and
full attempt fields are in each Lean receipt; failed drafts are excluded.

NED_K034/K035 and its separately checked argument windows remain the binding
caller-certificate inputs. NEE_K002/K003/K004 are excluded timed-out combined
extensions, not additional credit. Native root closure still needs the
remaining exact child frames/call-domain certificates and their physical
instantiation. No desired caller equality is hidden in PhysicalInterpretation.

## Remaining roots

encode_pool_v1_pair_forest_terminal_statement_v1, emit_result,
decode_pool_v1_pair_forest_terminal_request_v1, reconstruct_asq8_statement,
decode_public_statement_box and scan_proof_buffer have **no new composed
native theorem**. They remain OPEN and have not been started, respecting the
binding one-root order. Their inherited member/edge obstacles remain in
NED_REMAINING.json and NEE_EDGES.json. No theorem statement or axioms audit is
invented for an unproved root.
