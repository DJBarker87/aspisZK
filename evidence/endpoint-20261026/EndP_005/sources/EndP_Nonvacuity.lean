import EndP_Endpoint
set_option autoImplicit false
noncomputable section
namespace AspisR1.EndP_Nonvacuity
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open OraclePortRuntimeBindingC7 Port1_StoredCarrier

/-- Every literal submission, including malformed bytes, inhabits the carrier
and zero-query hypothesis; no accepted-run assumption is introduced. -/
theorem byte_prover (s : Submission) :
    (∀ H : Bytes → State, (eval H (.done s : ByteProver)).1.length ≤ 0) ∧
    (∀ H : Bytes → State, Carried (eval H (lift (.done s))).2) := by
  exact ⟨fun _ => Nat.le_refl 0, lift_carried (.done s)⟩

/-- The retained joins are jointly consistent in a rejecting model. This is
not an accepted deployed fixture or an instantiation of the Port1 children. -/
theorem rejecting_model (D : LiteralByteProtocol.Decoder) (P : ByteProver) :
    Physical (fun _ => .done false) ∧
    Port1_CanonicalJoin.AcceptedVerifierJoin D (fun _ => .done false) ∧
    StoredCarrierBinding D (fun _ => .done false) (lift P) (.done none) := by
  refine ⟨fun _ _ _ _ => rfl, ?_, ?_⟩
  · intro s H accepted
    cases accepted
  · intro H run returned accepted
    cases returned

/-- Non-vacuity obligation for ANY accepting physical source: the obsolete
unrestricted join really is impossible; our endpoint does not require it. -/
theorem accepting_source (D : LiteralByteProtocol.Decoder) (rust : Verifier)
    (physical : Physical rust) (H : Bytes → State) (i : OraclePortStoredExperimentC4.Input)
    (accepted : (eval H (rust i)).2 = true) :
    ¬ OraclePortFrozen2Join.AcceptedVerifierJoin rust
      (OraclePortStoredExperimentC4.verifier D OraclePortFrozen2.dV_frozen2) :=
  Uni_CanonicalPerAttempt.no_global_join D rust physical H i accepted

#print axioms byte_prover
#print axioms rejecting_model
#print axioms accepting_source
end AspisR1.EndP_Nonvacuity
end
