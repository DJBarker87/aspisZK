import StoredCarrierPresentedModel

/-! Runtime-only remainder at the explicitly constructed logical instance.
Not a deletion-only change to the arbitrary-runtime/frozen-source endpoint. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.StoredCarrierPresentedHeadline
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open OraclePortStoredExperimentC4 OraclePortRuntimeBindingC7 OraclePortFrozenOrderJoin
open StoredCarrierPresentedModel

/-- All numeric, extraction and failure-event conclusions are exactly Claims
of the adopted per-attempt endpoint, at this explicit logical runtime. -/
theorem final_soundness
    (D : LiteralByteProtocol.Decoder) (P : Prover) (Q : Nat)
    (hqueries : ∀ H : Bytes → State, (eval H P).1.length ≤ Q)
    (rust : Verifier)
    (hash : Bytes → State) (pub : Input → Bytes) (current : Input → R9PoolRuntimeBinding.Inputs)
    (h_Rust_equals_dV : AcceptedRunJoin D rust)
    (h_P2_prime : P2PrimeForInputs hash pub current) :
    OraclePortHeadlineFrozenPerAttempt.Claims D P Q (runtime D rust P hash pub current) :=
  OraclePortHeadlineFrozenPerAttempt.final_soundness D P Q hqueries rust _
    h_Rust_equals_dV (binding D rust P hash pub current h_P2_prime)

#print axioms final_soundness
end AspisR1.StoredCarrierPresentedHeadline
end
