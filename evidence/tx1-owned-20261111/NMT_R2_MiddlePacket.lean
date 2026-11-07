import NMT_R2_ResultTry
import NMT_345MiddleFold
set_option autoImplicit false
noncomputable section
namespace NMT_R2_MiddlePacket
open Aeneas Aeneas.Std NMT_345 NMT_R2_ResultTry NMT_stage1_owned

def middle {W : Type} (c : Calls) (s : Decoded W) : Result (core.result.Result (ProofData W) PE) := do
 let validation ← c.c7 s.statement
 NMT_R2_ResultTry.bind (c.c2 r1_pool_adapter.owned.stage1_owned.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestTerminalFormatErrorV1ProgramError validation ()) fun _ => do
  let common ← c.c6 s.statement
  let encoded ← c.c9 common.lane_transition.candidate_afterstate
  NMT_R2_ResultTry.bind (c.c2 r1_pool_adapter.owned.stage1_owned.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairVerifierTransportErrorV1ProgramError encoded ()) fun candidate =>
   NMT_R2_ResultTry.bind (r1_pool_adapter.owned.OwnedAccount.data c.c10 s.proofAccount) fun proof =>
    NMT_R2_ResultTry.pure ⟨⟨s,candidate⟩,proof⟩

theorem source {W : Type} (c : Calls) (s : Decoded W) (next : ProofData W → Result Ret) :
 NMT_R2_ResultTry.bind (middle c s) next = middleFold c s next := by
 simp only [middle,Bind.bind,NMT_R2_ResultTry.outer,NMT_R2_ResultTry.assoc,NMT_R2_ResultTry.pure_left]
 rfl
#print axioms source
end NMT_R2_MiddlePacket
end
