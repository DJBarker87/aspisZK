import OraclePortJoinSplitStd
import OraclePortFrozen2Join

/-! The explicit std/allocation owner targets the current two-transaction
accepted-run interface. Both full caller identities remain substantive
hypotheses; a CFG order certificate cannot provide either identity. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortS10StdFrozen2
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open OraclePortStoredExperimentC4 OraclePortJoinSplitStd OraclePortRuntimeBindingC7

structure OrderingJoin {σ : Signature} (D : LiteralByteProtocol.Decoder)
    (rust : Verifier) (source model : Implementation σ) (tree : Input → Calls σ Bool) : Prop where
  source_order : ∀ i, rust i = interpret source (tree i)
  model_order : ∀ i, interpret model (tree i) =
    verifier D OraclePortFrozen2.dV_frozen2 i

theorem acceptedRunJoin_of_cones {σ : Signature} (D : LiteralByteProtocol.Decoder)
    (rust : Verifier) (source model : Implementation σ) (tree : Input → Calls σ Bool)
    (inventory : List Site) (joins : PerConeJoins source model)
    (_coverage : S10Join inventory tree)
    (order : OrderingJoin D rust source model tree) :
    OraclePortFrozen2Join.AcceptedRunJoin D rust := by
  apply OraclePortFrozen2Join.total_join_accepted
  intro i
  exact (order.source_order i).trans
    ((interpret_eq joins (tree i)).trans (order.model_order i))

#print axioms acceptedRunJoin_of_cones
end AspisR1.OraclePortS10StdFrozen2
end
