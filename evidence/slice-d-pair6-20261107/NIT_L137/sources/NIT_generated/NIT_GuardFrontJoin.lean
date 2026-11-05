import NIT_NativeGuardJoin
set_option autoImplicit false
namespace AspisR1.NIT_GuardFrontJoin
open Aeneas Aeneas.Std Result NIT_Cuts NIT_PairControl NIT_GuardComposition
open NIT_GuardResult (from_cut)
open NIT_ErrorTransport (unitReply)

/-- Source control after entered child replies; mutations are separately
supplied by their CLOSED callee frames on exactly the same places. -/
def control (shared : Bool) (regular partialReply high : RU) (tail : Result NR) : Result NR :=
 match regular with
 | .Err e=>ok (.Err e)
 | .Ok _=>if shared then
   match partialReply with
   | .Err e=>ok (.Err e)
   | .Ok _=>match high with | .Err e=>ok (.Err e) | .Ok _=>tail
   else tail

/-- All returning native guard paths, all eight error identities, and the
unchanged arbitrary full tail Result. No field value or success is assumed. -/
theorem native_control (shared : Bool) (l : SameGuard) (regular partialReply high guard : RU)
 (tail : Result NR) (hr : l.regular=unitReply regular)
 (hp : l.«partial»=unitReply partialReply) (hh : l.high=unitReply high)
 (cut : cutSameGuard shared l (unitReply guard)) :
 dispatch guard tail=control shared regular partialReply high tail := by
 rw [from_cut shared l regular partialReply high guard hr hp hh cut]
 cases shared <;> cases regular <;> cases partialReply <;> cases high <;> rfl

#print axioms native_control
end AspisR1.NIT_GuardFrontJoin
