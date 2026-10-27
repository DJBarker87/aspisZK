import Uni_CanonicalPerAttempt
set_option autoImplicit false
noncomputable section
namespace AspisR1.EndP_Endpoint
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open OraclePortRuntimeBindingC7 Port1_StoredCarrier
open OraclePortHeadlineFrozen2PerAttempt (Claims failureModel)

/-- L158/L183 on the SAME source instance. Physical is proved from the
literal byte driver, rather than an extra caller-supplied premise. -/
theorem two_pass (D : LiteralByteProtocol.Decoder) (adapter : AdapterRw.Ops)
    (impl : VTop_OracleCode.Implementation) {Hash : Type}
    (digest : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (raw : Port1_CanonicalJoin.AcceptedVerifierJoin D (Port1_Driver.rust adapter impl digest hash)) :
    Port1_CanonicalJoin.AcceptedRunJoin D (Port1_Driver.rust adapter impl digest hash) :=
  Port1_CanonicalJoin.two_pass D _ (driver_physical adapter impl digest hash) raw

/-- L184: the existing per-attempt Claims, with no annotation or physical
premise left to instantiate. L157 and L159 retain their original meanings. -/
theorem final_soundness (D : LiteralByteProtocol.Decoder) (P : ByteProver) (Q : Nat)
    (hqueries : ∀ H : Bytes → State, (eval H P).1.length ≤ Q)
    (adapter : AdapterRw.Ops) (impl : VTop_OracleCode.Implementation) {Hash : Type}
    (digest : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash) (runtime : Runtime)
    (raw : Port1_CanonicalJoin.AcceptedVerifierJoin D (Port1_Driver.rust adapter impl digest hash))
    (binding : StoredCarrierBinding D (Port1_Driver.rust adapter impl digest hash) (lift P) runtime) :
    Claims D (lift P) Q runtime :=
  Uni_CanonicalPerAttempt.final_soundness D P Q hqueries _ runtime
    (driver_physical adapter impl digest hash) raw binding

/-- Exact repeated/adaptive expression, without a positive lower bound on Q. -/
theorem failure_bound (D : LiteralByteProtocol.Decoder) (P : ByteProver) (Q : Nat)
    (hqueries : ∀ H : Bytes → State, (eval H P).1.length ≤ Q)
    (adapter : AdapterRw.Ops) (impl : VTop_OracleCode.Implementation) {Hash : Type}
    (digest : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash) (runtime : Runtime)
    (raw : Port1_CanonicalJoin.AcceptedVerifierJoin D (Port1_Driver.rust adapter impl digest hash))
    (binding : StoredCarrierBinding D (Port1_Driver.rust adapter impl digest hash) (lift P) runtime) :
    failureModel runtime ≤ ((Q+34 : Nat) : Rat)*PerAttemptEnvelope.B +
      BinCombinedMerkleCollision.kappa (Q+1161) + 1/(2:Rat)^126 + 1/(2:Rat)^454 :=
  (final_soundness D P Q hqueries adapter impl digest hash runtime raw binding).2.2.2.1

/-- The contract's whole-experiment, zero-adversary-query statement. -/
theorem zero_queries (D : LiteralByteProtocol.Decoder) (P : ByteProver)
    (hqueries : ∀ H : Bytes → State, (eval H P).1.length ≤ 0)
    (adapter : AdapterRw.Ops) (impl : VTop_OracleCode.Implementation) {Hash : Type}
    (digest : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash) (runtime : Runtime)
    (raw : Port1_CanonicalJoin.AcceptedVerifierJoin D (Port1_Driver.rust adapter impl digest hash))
    (binding : StoredCarrierBinding D (Port1_Driver.rust adapter impl digest hash) (lift P) runtime) :
    failureModel runtime ≤ 1/(2:Rat)^100 :=
  (failure_bound D P 0 hqueries adapter impl digest hash runtime raw binding).trans
    StartChargeNumeric.zero_queries

#print axioms two_pass
#print axioms final_soundness
#print axioms failure_bound
#print axioms zero_queries
#print final_soundness
end AspisR1.EndP_Endpoint
end
