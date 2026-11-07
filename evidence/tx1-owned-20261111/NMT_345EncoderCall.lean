import NMT_345MapEncoder
set_option autoImplicit false
noncomputable section
namespace NMT_345
open Aeneas Aeneas.Std Result
structure CommonFrame (W : Type) extends Decoded W where
 common : Common
/-- The single encoder occurrence, before its separate map_err. -/
def callEncoder {W : Type} (c : Calls) (s : CommonFrame W) : Result Ret := do
 let reply ← c.c9 s.common.lane_transition.candidate_afterstate
 mapEncoder c ⟨s.toDecoded,s.common,reply⟩
theorem encoder_call {W : Type} (c : Calls) (s : CommonFrame W) :
 callEncoder c s = (c.c9 s.common.lane_transition.candidate_afterstate >>= fun reply =>
 mapEncoder c ⟨s.toDecoded,s.common,reply⟩) := rfl
#print axioms encoder_call
end NMT_345
