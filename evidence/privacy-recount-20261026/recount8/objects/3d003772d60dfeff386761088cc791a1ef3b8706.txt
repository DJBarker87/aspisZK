# Fixture installation audit while the host gate is closed

No new counterexample or fixture certificate is established by this audit.
The historical proof names below are checked in predecessor receipts, not
recompiled here. Both deployed P-and-T fixture instances remain open.

The source sibling report explicitly leaves installed full-compiler fixture
success open. FrozenInput carries a compilation as DATA. FrozenPublic uses a
retained `compile_call` proof; it does not construct that successful call.
Its `Records` dictionary is an owned reference with a frozen root table;
actual shipped Records equality is not inferred from equal witness words.

PV_RunJoin_TrustFixtures.both_fibres provides canonical transfer/withdrawal
witnesses and generic T models. Its data is not TrustEndpoint.trustData at
any actual deployed runtime/boundary. It proves no RemainingProofs.trace.
Thus it cannot be reused as the requested deployed P conjunction.

PV_RunJoin_ErrorViewObstruction.empty_native_log_disagrees proves a necessary
failure-path check: the reencoded source-success branch has a nonempty log,
so a truthful empty native log cannot match it. The premises still include
an exact successful source coin. FailurePremiseObstruction additionally needs
the SAME deployed world outside the unchanged bad event, and that world's
native observer decoder. Neither is supplied merely by the existence of an
OS-error constructor or by the prior dlsym rejection. The generic obstruction
is not a checked shipped-row counterexample and is not a stopping condition.

Options A/B remain unadopted. No fixture construction may choose away errors,
change the bad event, fabricate the observer log, or define the extracted
producer equal to the target source experiment to obtain an easy P proof.
The actual extracted producer must be defined from the operational execution
and then proved to refine that experiment.

D162's route is the actual RealR1_client::prove_for_proof_accounts function:
it calls prove_masked_retrying_with with Variant::S2, the supplied SAME
compilation/hash/store, and a callback that calls proof_account(k) BEFORE
StateOnlyAttemptSecrets::generate_for_mask_nonce. The adapter does not run or
prove the compiler; success belongs to the caller/planner source join.
Keys are public inputs here; no private key or account was created or touched.

## Per-fixture status after native root checks

| Fixture | Canonical witness fibre | Actual selected compiler/admission | Concrete Runtime/Boundary and all remaining P | T | Deployed P ∧ T |
|---|---|---|---|---|---|
| Transfer | Historical both_fibres evidence retained | OPEN: same actual selection/dictionaries, successful compile, admission | OPEN: actual caller/carrier/initializer/complete observer association and trace | Same three fields, hypothetical | OPEN |
| Withdrawal | Historical both_fibres evidence retained | OPEN: same actual selection/dictionaries, successful compile, admission | OPEN: actual caller/carrier/initializer/complete observer association and trace | Same three fields, hypothetical | OPEN |

Seven fixed native root cells are verified; they supply no fixture compiler
success, admission instance, or complete source trace. The generic causal
constructor provides initial-ledger independence and strict-prefix frames
without deleting OS-error outcomes, but its equality to the actual deployed
initializer/context producer is still an installation obligation. Neither
fixture is being declared vacuous or non-vacuous from those generic facts.

## Why public binding is not inferred from canonical input data

The pinned PV_Src_NativeInput.publicInput definition projects the request AND
`transition i.compiled.public_statement`. FrozenInput.Data carries `compiled`
as data, and does not prove that it is returned by `run`. Consequently an
abstract public equality on the honest witness does not by itself install
the selected native public statement. Actual compiler success and the
compiler/public refinement must be supplied for the SAME compiled record.
A convenient selected family or a generic T model cannot fill this join.
This is a source-definition obstruction to an unsupported inference, not a
checked shipped ROW counterexample or a claim that the fixture is vacuous.
