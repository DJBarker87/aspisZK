import Port1_StoredCarrier

/-! The 19:35 interface: raw joins quantify byte submissions; annotation may
change ghost words only. This does not assume a global source/model join. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port1_CanonicalJoin
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open OraclePortStoredExperimentC4 OraclePortStoredAdmissionC4 OraclePortRuntimeBindingC7
open OraclePortFrozen2Join Port1_StoredCarrier

def AcceptedVerifierJoin (D : LiteralByteProtocol.Decoder) (rust : Verifier) : Prop :=
  ∀ (s : Submission) H, (eval H (rust (input s))).2 = true →
    eval H (rust (input s)) = eval H (verifier D OraclePortFrozen2.dV_frozen2 (input s))

/-- Only the experiment's source-indexed class is needed, including arbitrary
prover oracle computations and both annotation passes. -/
structure AcceptedRunJoin (D : LiteralByteProtocol.Decoder) (rust : Verifier) : Prop where
  verifier : AcceptedVerifierJoin D rust
  annotated : ∀ (P : Prover), (∀ H, Carried (eval H P).2) → ∀ H,
    (eval H (annotatedWith D rust P)).2.2 = true →
      eval H (annotatedWith D rust P) =
        eval H (annotated D OraclePortFrozen2.dV_frozen2 P)

theorem carried_join (D : LiteralByteProtocol.Decoder) (rust : Verifier)
    (physical : Physical rust) (join : AcceptedVerifierJoin D rust)
    (i : Input) (carried : Carried i) (H : Bytes → State)
    (accepted : (eval H (rust i)).2 = true) :
    eval H (rust i) = eval H (verifier D OraclePortFrozen2.dV_frozen2 i) := by
  obtain ⟨s,pub,stored,rows⟩ := carried
  have source : rust i = rust (input s) := physical i (input s) (congrArg (·.pubBytes) pub) stored
  have model : verifier D OraclePortFrozen2.dV_frozen2 i =
      verifier D OraclePortFrozen2.dV_frozen2 (input s) := by
    unfold OraclePortStoredExperimentC4.verifier
    rw [stored,pub]
    exact OraclePortCanon.verifier_congr D _ _ _ _ rows
  rw [source] at accepted ⊢
  rw [model]
  exact join s H accepted

theorem two_pass (D : LiteralByteProtocol.Decoder) (rust : Verifier)
    (physical : Physical rust) (raw : AcceptedVerifierJoin D rust) :
    AcceptedRunJoin D rust := by
  refine ⟨raw,?_⟩
  intro P carried H accepted
  have backward : ∀ w i, rust (enrich w i) = rust i := by
    intro w i
    exact physical _ _ rfl rfl
  have before : (eval H (originalWith rust P)).2.2 = true := by
    simpa only [annotatedWith_eval,backward,originalWith_eval] using accepted
  have first : eval H (originalWith rust P) =
      eval H (originalWith (verifier D OraclePortFrozen2.dV_frozen2) P) := by
    rw [originalWith_eval] at before
    simp only [originalWith_eval,carried_join D rust physical raw _ (carried H) H before]
  have carriedSecond : Carried
      (enrich (build D (view (eval H (originalWith rust P))))
        (eval H (originalWith rust P)).2.1) := by
    apply enrich_carried
    simpa only [originalWith_eval] using carried H
  rw [annotatedWith_eval] at accepted ⊢
  have second := carried_join D rust physical raw _ carriedSecond H accepted
  rw [first] at second ⊢
  change _ = eval H (annotatedWith D (verifier D OraclePortFrozen2.dV_frozen2) P)
  simp only [annotatedWith_eval,second]

/-- The exact premise required by the existing runtime binding, with no
unrestricted raw-input law and no discarded rejected oracle prefixes. -/
theorem accepted_experiment (D : LiteralByteProtocol.Decoder) (rust : Verifier)
    (join : AcceptedRunJoin D rust) (P : ByteProver) (H : Bytes → State)
    (accepted : (eval H (annotatedWith D rust (canon (lift P)))).2.2 = true) :
    eval H (annotatedWith D rust (canon (lift P))) =
      eval H (annotated D OraclePortFrozen2.dV_frozen2 (canon (lift P))) :=
  join.annotated _ (canon_lift_carried P) H accepted

#print axioms carried_join
#print axioms two_pass
#print axioms accepted_experiment
end AspisR1.Port1_CanonicalJoin
end
