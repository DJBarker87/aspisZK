import NMC_LocalWindows
import NLU_TerminalTransport
import S2W_D189Wrappers
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMC_Models
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NMC_Window
abbrev Q := NLC_Finish.Q
/-- Root error uses the full Verified-typed carrier. Continuations carry the
selected local value separately; neither is collapsed to a Unit validator. -/
abbrev Reply := Result (Sum (NLC_Finish.Out Unit) (Option Q))
abbrev PublicReply := core.result.Result Q FIq_Terminal.Error
abbrev DecodeReply := core.result.Result NLC_Finish.Words r1_wire.Error
noncomputable def qeq (a b : Q) : Bool := by classical exact decide (a=b)
noncomputable def peq (a b : NLC_Finish.Point) : Bool := by classical exact decide (a=b)
def continued {A : Type} (s : Context A) (value : Option Q) : Observation A Reply :=
 ⟨ok (.inr value),s,[]⟩
/-- Exact existing allocator action at the implicit Box exit. Abort has no
post-heap; context then denotes the last ENTERED cleanup frontier. -/
def errorExit {A : Type} (allocator : S2W_D189Wrappers.Allocator A)
 (s : Context A) (error : r1_wire.Error) : Observation A Reply :=
 let identity:=s.frame.claims.identity
 let entered:=[ResourceEvent.dropEntered identity 1392 4]
 match allocator.cleanup s.allocator with
 | .fail reason=>⟨.fail reason,s,entered⟩
 | .div=>⟨.div,s,entered⟩
 | .ok after=>
   ⟨ok (.inl (.Err error)),{s with allocator:=after,heap:=NMC_Parent.write s.heap identity none},
    entered++[.dropReturned identity,.parentError error]⟩
def mapPublic {A : Type} (allocator : S2W_D189Wrappers.Allocator A)
 (s : Context A) (reply : PublicReply) : Observation A Reply :=
 match reply with
 | .Err _=>errorExit allocator s .Public
 | .Ok terminal=>continued {s with frame:={s.frame with terminal:=terminal}} none
def terminalGuard {A : Type} (allocator : S2W_D189Wrappers.Allocator A)
 (s : Context A) (masked : Q) : Observation A Reply :=
 if qeq s.frame.running masked then continued s none else errorExit allocator s .Terminal
def circleGuard {A : Type} (allocator : S2W_D189Wrappers.Allocator A)
 (s : Context A) (_ : Unit) : Observation A Reply :=
 if peq s.frame.z0 s.frame.z1 then errorExit allocator s .EqualCirclePoints else continued s none
def writePartial {count : Nat} (before : Partial count) (i : Fin count) (value : Q) : Partial count :=
 {before with initialized:=i.val+1,cells:=fun j=>if j=i then some value else before.cells j}
def low {A : Type} (s : Context A) (i : Fin 16) : Observation A Reply :=
 let value:=NLU.cell (NLU.cell s.frame.claims.value 0 (by decide)) i.val (by change i.val<29;omega)
 continued {s with low:=writePartial s.low i value} (some value)
def high {A : Type} (s : Context A) (i : Fin 10) : Observation A Reply :=
 let value:=NLU.cell (NLU.cell s.frame.claims.value 0 (by decide)) (16+i.val) (by change 16+i.val<29;omega)
 continued {s with high:=writePartial s.high i value} (some value)
def blind {A : Type} (s : Context A) (_ : Unit) : Observation A Reply :=
 continued s (some (NLU.cell (NLU.cell s.frame.claims.value 0 (by decide)) 27 (by decide)))
def extra28 {A : Type} (s : Context A) (_ : Unit) : Observation A Reply :=
 continued s (some (NLU.cell s.frame.extra 28 (by decide)))
def stateBefore {A : Type} (s : Context A) (_ : Unit) : Observation A Reply :=
 continued {s with frame:={s.frame with state:=s.frame.transcript.state}} none
def decode25 {A : Type} (allocator : S2W_D189Wrappers.Allocator A)
 (s : Context A) (reply : DecodeReply) : Observation A Reply :=
 match reply with
 | .Err error=>errorExit allocator s error
 | .Ok extra=>continued {s with frame:={s.frame with extra:=extra}} none
def decode26 {A : Type} (allocator : S2W_D189Wrappers.Allocator A)
 (s : Context A) (reply : DecodeReply) : Observation A Reply :=
 match reply with
 | .Err error=>errorExit allocator s error
 | .Ok before=>continued {s with frame:={s.frame with before:=before}} none
end AspisR1.NMC_Models
end
