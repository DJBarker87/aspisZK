import NMT_345MapValidator
import NMT_345Raw_09
import NMT_345Encoder
import NMT_345Common
set_option autoImplicit false
noncomputable section
namespace NMT_345
open Aeneas Aeneas.Std Result NMT_stage1_owned
structure EncoderReply (W : Type) extends Decoded W where
 common : Common
 reply : core.result.Result (Array U8 688#usize) EncodeError

def mapEncoder (c : Calls) {W : Type} (s : EncoderReply W) : Result Ret := do
 let r ← c.c2
  r1_pool_adapter.owned.stage1_owned.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairVerifierTransportErrorV1ProgramError
  s.reply ()
 let cf ← core.result.Result.Insts.CoreOpsTry.branch r
 match cf with
 | core.ops.control_flow.ControlFlow.Continue candidate => raw09 c ⟨s.toDecoded,candidate⟩
 | core.ops.control_flow.ControlFlow.Break residual =>
   core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
    (alloc.vec.Vec U8) (core.convert.FromSame PE) residual

theorem common_encoder_calls {W : Type} (c : Calls) (s : Decoded W) :
 raw08 c s = (do
  let common ← c.c6 s.statement
  let reply ← c.c9 common.lane_transition.candidate_afterstate
  mapEncoder c ⟨s,common,reply⟩) := rfl

theorem encoder_map_std {W : Type} (c : Calls) (s : EncoderReply W) :
 mapEncoder (installMapErr c) s =
 match s.reply with
 | .Ok candidate => raw09 (installMapErr c) ⟨s.toDecoded,candidate⟩
 | .Err _ => .ok (.Err .InvalidAccountData) := by
 cases h : s.reply <;> rfl
#print axioms common_encoder_calls
#print axioms encoder_map_std
end NMT_345
