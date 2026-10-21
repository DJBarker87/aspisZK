import OraclePortFrozen2Join
import OraclePortAccLogCones

/-! The existing total S-cone refinement shape, now targeting dV_frozen2.
Caller decomposition, inventory and model identification remain explicit;
this theorem does not manufacture current source-cone inhabitants. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortFrozen2Join
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open OraclePortStoredExperimentC4 OraclePortRuntimeBindingC7 OraclePortJoinSplit
open OraclePortAccLog (ConeLogJoin)

theorem acceptedVerifierJoin_of_cones {σ : Signature} (D : LiteralByteProtocol.Decoder)
    (rust : Verifier) (source model : Implementation σ) (tree : Input → Calls σ Bool)
    (h_cones : ∀ cone, ConeLogJoin source model cone)
    (inventory : List Site) (_h_S10 : S10Join inventory tree)
    (h_source : ∀ i, rust i = interpret source (tree i))
    (h_model : ∀ i, interpret model (tree i) = verifier D OraclePortFrozen2.dV_frozen2 i) :
    AcceptedVerifierJoin rust (verifier D OraclePortFrozen2.dV_frozen2) := by
  intro H i _
  rw [h_source i,← h_model i]
  exact OraclePortAccLog.interpret_valueJoin source model h_cones (tree i) H

theorem acceptedRunJoin_of_cones {σ : Signature} (D : LiteralByteProtocol.Decoder)
    (rust : Verifier) (source model : Implementation σ) (tree : Input → Calls σ Bool)
    (h_cones : ∀ cone, ConeLogJoin source model cone)
    (inventory : List Site) (h_S10 : S10Join inventory tree)
    (h_source : ∀ i, rust i = interpret source (tree i))
    (h_model : ∀ i, interpret model (tree i) = verifier D OraclePortFrozen2.dV_frozen2 i)
    (stable : ∀ w i H, (eval H (rust (enrich w i))).2 = (eval H (rust i)).2) :
    AcceptedRunJoin D rust :=
  acceptedRunJoin_of_stable D rust
    (acceptedVerifierJoin_of_cones D rust source model tree h_cones inventory h_S10 h_source h_model)
    stable

/-- Total per-cone joins need no extra source-enrichment stability premise:
the complete program equality and model enrichment law supply it. -/
theorem acceptedRunJoin_of_total_cones {σ : Signature} (D : LiteralByteProtocol.Decoder)
    (rust : Verifier) (source model : Implementation σ) (tree : Input → Calls σ Bool)
    (h_cones : PerConeJoins source model)
    (inventory : List Site) (_h_S10 : S10Join inventory tree)
    (h_source : ∀ i, rust i = interpret source (tree i))
    (h_model : ∀ i, interpret model (tree i) = verifier D OraclePortFrozen2.dV_frozen2 i) :
    AcceptedRunJoin D rust := by
  apply total_join_accepted D rust
  intro i
  exact (h_source i).trans ((interpret_eq h_cones (tree i)).trans (h_model i))

#print axioms acceptedVerifierJoin_of_cones
#print axioms acceptedRunJoin_of_cones
#print axioms acceptedRunJoin_of_total_cones
end AspisR1.OraclePortFrozen2Join
end
