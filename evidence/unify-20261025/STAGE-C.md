# Class C audit and corrected downstream endpoint

## L089 and L090

Before (both old fields): `∀ event, marked event tag → ∃ segments, layout`.
After: `∀ event, marked event tag → actual_invoked_Rust_Ok event → ∃ segments, layout`.
The fields are exactly `Op5T_Marks.FirstMarks` and `SecondMarks`; their full
expansions, including `accepted`, are in Uni_010. No record field asserts the
whole accepted-pair conclusion. The guard tests the invoked operation and its
actual arguments, not a returned event's arbitrary payload.

`Uni_Accepted.accepted_pair_unified` uses only the guarded fields throughout
its Op5T/D189 chain. The original theorems remain unchanged. Replacing their
old universal fields with guarded fields is a genuine weakening authorised
by the lead, not a proof that the original fields hold.

For TX1, reuse Op5T_Marks.accepted_source_marks and the checked wrong-split
counterexample. For TX2, Uni_SecondMarks.accepted_source_marks proves the
literal authenticated source trace has resume/batch1/query1/finish on every
successful call. Uni_SecondMarks.successful_fixture constructs such a trace
with installed shape/finish and explicitly selected remaining test leaves.
It is a source-control fixture, not a deployed multiproof certificate.
Uni_RejectedSecond.rejected_source shows the installed shape on empty bytes
returns Parse after op3 alone. `no_global_second_mark_association` proves
that old SecondMarks cannot describe this faithful prefix: old marks force
resume even though the source never reaches it. This is an interface
contradiction under global source association, not a shipped-code bug.

L089/L090's old C law families disappear from the corrected chain. Their
success-guarded source association obligations remain P. Neither a theorem
about source-site projection nor a successful fixture identifies the arbitrary
SDK ChildConeJoin log. Op5T_CarrierGap remains applicable in principle; union
installation does not authenticate an arbitrary erased port.

## L155

Before: globalJoin.verifier quantifies over arbitrary logical Input, whose
proof function is independent of the bytes supplied to Rust. Uni_CanonicalPerAttempt.no_global_join
proves that ANY physical verifier accepting once cannot satisfy that law:
replace its logical proof with a constant message, preserving physical inputs;
the source still accepts and the frozen2 model rejects by constructor schedule.
Stop trying to instantiate that FALSE interface for the deployed source.

After: `Uni_CanonicalPerAttempt.final_soundness` accepts a ByteProver
(arbitrary adaptive oracle program returning two unrestricted byte lists),
Physical rust, the existing L157 canonical raw join and L159 binding on lift P.
It derives the annotated canonical join by Port1_CanonicalJoin.two_pass and
returns EXACTLY OraclePortHeadlineFrozen2PerAttempt.Claims D (lift P) Q runtime.
It preserves the extractor, relation, abort terms, repeated/adaptive
`(Q+34)*B + kappa(Q+1161) + 2^-126 + 2^-454`, Qmax and 100-bit target.
There is no lower Q bound. This closes the previously missing CANONICAL
per-attempt composition; it does not prove the raw canonical instance.

L155 is retired for that corrected downstream path, not proved. Its replacement
L157 was ALREADY counted P. Physical and StoredCarrierBinding were also already
counted. L156's original unrestricted annotated law is not consumed here;
its old ledger row is left unchanged as requested, with no discharge credit.
The pair theorem itself never assumed a globalJoin. Connecting its actual
runtime/effects to this downstream endpoint still requires L157/L159 and the
source-associated child interpretation. No new post-existential premise is
used to claim those rows discharged.

## Non-vacuity for the deployed source

`source-fixture-audit.json` pins the retained successful LiteSVM transfer-13
pair at the EXACT default ELF f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4.
The original runtime receipt exits0; both stage error fields are null and
comparison.both_admitted_pairs_accepted=true. This task freshly compared all
562 admitted source hashes in that build receipt to this worktree: all match.
Proof/public hashes and complete runtime/build references remain in the pinned
input manifest. This is stronger than a source-shaped fake-leaf fixture for
showing that the deployed program actually accepts. It is reused evidence,
not a new runtime execution or new ELF build. Historical failed readonly/1
is explicitly excluded; only successful readonly/2 is selected.

Uni_Audit.extraction_satisfiable also constructs the extraction boundary on
the exact union by choosing its owned native bodies. This establishes that
boundary's consistency, not deployment correctness. Neither this nor the
successful ELF fixture is a kernel proof of joint inhabitation of ALL SDK,
crypto, source-log, runtime-history and model-binding premises. Those remain
explicit P/T boundaries. Consequently no complete deployed security or
100-bit claim is made.

## Validation

Uni_004 failed on list-append normalization; Uni_005 fixes the proof.
Uni_006 failed on a non-definitional scalar comparison; Uni_008 first rewrites
the existing symbolic proof-size lemma, then decides only the tiny length
comparison. Diagnostic sorryAx output from failed elaborations is excluded.
No sorry/axiom/admit/native_decide was written. No timeout, memory kill,
raised cap, unchanged prover retry, package replay, Rust or Kani run occurred.
All successful top theorems have standard-only axioms; Uni_010 is the single
final full axioms/statement audit, not a package replay.
