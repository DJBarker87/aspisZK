import NMT_345CheckpointData
set_option autoImplicit false
noncomputable section
namespace NMT_345
open Aeneas Aeneas.Std Result NMT_stage1_owned
structure PublicData (W : Type) extends CheckpointData W where
 publicData : Slice U8
structure Decoded (W : Type) extends PublicData W where
 statement : aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1
structure Candidate (W : Type) extends Decoded W where
 candidate : Array U8 688#usize
structure ProofData (W : Type) extends Candidate W where
 proofData : Slice U8
structure Bounds (W : Type) extends ProofData W where
 proofStart : Usize
 proofEnd : Usize
structure Returned (W : Type) extends Bounds W where
 checkpoint : alloc.vec.Vec U8
end NMT_345
