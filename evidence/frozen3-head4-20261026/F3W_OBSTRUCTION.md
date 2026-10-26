# Checked rejected-run obstruction

The rejection branch of an UNGUARDED complete-eval join is false.
F3W_Obstruction.no_unconditional_raw_join (attempt018, exit0) states this on the
ACTUAL F3T_Installed.source and canonical F3T_ByteCarrier.input and F3_Model.verifier,
with the EXACT Hiq_RecordedJoint/BinRawByteCollisionTargets event at Q=0.
Only propext, Classical.choice and Quot.sound occur.

Quantifiers checked:

    forall c hashv D,
      forall (account : Submission -> Program Bytes State A)
             (project : Submission -> A -> Parsed × Queries)
             (select : Submission -> A -> RuntimeInputs × RuntimeInputs),
        (forall s H, firstReads [] (eval H (account s)).log <= 1921) ->
        NOT (forall s H,
          eval H (source c hashv (input c s)) =
            eval H (F3_Model.verifier D (input c s))
          OR event iv 2965
            (eval H (Hiq_RecordedJoint.program (account s) (project s) (select s)))).

A separate account program is allowed for EACH s; this is not an objection
based on an arbitrarily unrelated fixed account trace. Any concrete complete
account experiment satisfying the retained zero-adversary-query budget is
covered. The event is the bound's charged event, not a new event or a renamed
prefix collision.

Proof shape:
1. s.publicBytes = List.replicate (Usize.max+1) 0; s.stored = []. This is a
   symbolic Lean value. No enormous byte list or Finset is evaluated/generated.
2. source checks Port1_Driver.asSlice before entering either verifier. The
   public cannot fit its extracted Slice carrier, so eval source = ([],false),
   for every configuration and every H. This is F3W_Rejection.oversized_eval.
3. Frozen3's COMPLETE verifier always has a nonempty first sampler log,
   independently of decoder, byte validity, decision or acceptance:
   F3W_Rejection.model_log_nonempty. Consequently the complete evals differ
   for EVERY H (oversized_ne). This does not claim the model accepts.
4. F3T_AccountCharge.bound gives charged-event mass <= accountLoss(0) < 1.
   OracleProgramLawExt.lazyMean_eq_of_eval implies some H has NO charged event:
   if every H hit, its mass would equal 1. F3W_CollisionFree.account_clean checks
   this symbolically, without enumerating the oracle space. Combining that H
   with (2)-(3) refutes the disjunction, not just strict equality.

Exact missing restriction: source acceptance, or an explicitly weaker
accepted-run relation. Without it, the requested rejected full-eval branch
cannot be obtained from L159, history, owner correctness or runtime trust.
L159 constrains actual accepted runtime observations; it cannot turn an empty
source rejection log into the sampler-first model's nonempty log for every
finite byte list. Checking that both verdicts are false would not repair log
equality. A representability/domain restriction would change the stated all-byte
universe; even representable early rejections would still require separate
analysis. No such restriction, model gating, trust item or event change is added.

IMPORTANT distinction: F3U_CollisionJoin.Join ALREADY has the source-acceptance
guard. This obstruction does NOT refute that inherited interface. The task's
phrase "accepted installed source" can mean that guarded interface, whereas
its requested rejected-branch method suggests the stronger unguarded one.
The quantifier clarification was requested; no answer has arrived as of this
stage. No claim that the guarded deliverable is false is made. Its remaining
charged complete-account transport is OPEN; F3W_Canonical.accepted is a checked
source-derived continuation, not a replacement raw_join_or_collision theorem.

Per the explicit STOP-and-report instruction, no unguarded raw theorem is
installed and no further proof campaign is pursued after this checked
obstruction. Budget at obstruction:18/100 actual Lean compiles (14 pass,4
elaboration failures);0/0 Kani. Final audit/evidence collection follows; unused
budget is not permission to work around a false statement or alter its universe.
No headline or accepted-instance/non-vacuity construction was attempted.
