import NMT_345MapValidatorStep
import NMT_345MapEncoderStep
import NMT_345CommonCall
import NMT_345TryCongr
import NMT_345BoundaryProofData
import NMT_CallTree
set_option autoImplicit false
noncomputable section
namespace NMT_345
open Aeneas Aeneas.Std Result NMT_stage1_owned

def middleFold {W : Type} (c : Calls) (s : Decoded W) (next : ProofData W → Result Ret) : Result Ret := do
 let validation ← c.c7 s.statement
 tryStep (c.c2 r1_pool_adapter.owned.stage1_owned.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestTerminalFormatErrorV1ProgramError validation ()) fun _ => do
  let common ← c.c6 s.statement
  let encoded ← c.c9 common.lane_transition.candidate_afterstate
  tryStep (c.c2 r1_pool_adapter.owned.stage1_owned.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairVerifierTransportErrorV1ProgramError encoded ()) fun candidate =>
   tryStep (r1_pool_adapter.owned.OwnedAccount.data c.c10 s.proofAccount) fun proof =>
    next ⟨⟨s,candidate⟩,proof⟩

theorem middle_fold {W : Type} (c : Calls) (s : Decoded W) :
 raw07 c s = middleFold c s (raw10 c) := by
 unfold middleFold
 rw [validator_call]
 apply AspisR1.NMT_CallTree.result_congr
 intro validation
 rw [map_validator_step]
 apply try_congr
 intro _
 rw [common_call]
 apply AspisR1.NMT_CallTree.result_congr
 intro common
 rw [encoder_call]
 apply AspisR1.NMT_CallTree.result_congr
 intro encoded
 rw [map_encoder_step]
 apply try_congr
 intro candidate
 rw [boundaryProofData]
#print axioms middle_fold
end NMT_345
