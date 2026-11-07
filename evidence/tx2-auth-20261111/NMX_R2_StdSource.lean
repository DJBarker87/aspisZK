import NMX_R2_NativeRoot
set_option autoImplicit false
noncomputable section
namespace NMX_R2_StdSource
open Aeneas Aeneas.Std AdapterRw NMX_SourceModel
/-- The allocating clone interpretation changes no raw source condition.
Every child remains a typed command at its original arguments. -/
theorem source (env : RSL.Env) (aborts : Bool) (failure : Error)
 (verifier : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount)
 (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) :
 NMX_SourceProgram.auth (NMX_R2_StdOps.install env aborts failure)
  verifier accounts pool outputLane slot = NMX_R2_Skeleton.auth verifier accounts pool outputLane slot := by
 unfold NMX_SourceProgram.auth NMX_R2_Skeleton.auth
 simp only [core.cmp.PartialEq.ne.trait_default,core.cmp.PartialEq.ne.default,
  solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey,NMX_R2_StdOps.install,
  NMX_R2_PrimitiveInstall.install,NMX_LeafInstall.install,NGL_CheckpointModel.install,
  Aeneas.Std.bind_tc_ok,decide_not,Bool.decide_eq_true]
#print axioms source
end NMX_R2_StdSource
end
