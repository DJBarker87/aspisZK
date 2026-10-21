import OraclePortJoinSplitStd
import OraclePortFrozenOrderJoin

/-! The std extension composes into the unchanged accepted-run target.
Neither caller identity is inferred from a CFG or an inventory. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortJoinSplitStdFrozen
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open OraclePortStoredExperimentC4 OraclePortJoinSplitStd OraclePortRuntimeBindingC7

structure OrderingJoin {σ : Signature} (D : LiteralByteProtocol.Decoder)
    (rust : Verifier) (source model : Implementation σ) (tree : Input → Calls σ Bool) : Prop where
  source_order : ∀ i, rust i = interpret source (tree i)
  model_order : ∀ i, interpret model (tree i) =
    verifier D OraclePortFrozenOrder.dV_frozen i

theorem acceptedRunJoin_of_cones {σ : Signature} (D : LiteralByteProtocol.Decoder)
    (rust : Verifier) (source model : Implementation σ) (tree : Input → Calls σ Bool)
    (inventory : List Site) (joins : PerConeJoins source model)
    (_coverage : S10Join inventory tree)
    (order : OrderingJoin D rust source model tree) :
    OraclePortFrozenOrderJoin.AcceptedRunJoin D rust := by
  apply OraclePortFrozenOrderJoin.total_join_accepted
  intro i
  exact (order.source_order i).trans
    ((interpret_eq joins (tree i)).trans (order.model_order i))

#print axioms acceptedRunJoin_of_cones
end AspisR1.OraclePortJoinSplitStdFrozen
end
