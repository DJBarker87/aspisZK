import NIT_ControlCuts
set_option autoImplicit false
namespace AspisR1.NIT_GuardResult
open Aeneas Aeneas.Std Result NIT_Cuts
abbrev RU := NIT_ErrorTransport.NativeReply Unit
open NIT_ErrorTransport (unitReply)

theorem unit_injective : Function.Injective (@unitReply Unit) := by
 intro x y same
 cases x with
 | Err e =>
  cases y with
  | Err f => exact congrArg core.result.Result.Err
      (NIT_ErrorTransport.error_injective (core.result.Result.Err.inj same))
  | Ok b => cases same
 | Ok a =>
  cases y with
  | Err f => cases same
  | Ok b => cases a;cases b;rfl

def expected (shared : Bool) (regular partialReply high : RU) : RU :=
 match regular with
 | .Err e=>.Err e
 | .Ok _=>if !shared then .Ok () else
   match partialReply with
   | .Err e=>.Err e
   | .Ok _=>match high with | .Err e=>.Err e | .Ok _=>.Ok ()

theorem model (shared : Bool) (l : SameGuard) (regular partialReply high : RU)
 (hr : l.regular=unitReply regular) (hp : l.«partial»=unitReply partialReply)
 (hh : l.high=unitReply high) :
 unitReply (expected shared regular partialReply high)=(sameExpected shared l).1 := by
 cases shared <;> cases regular <;> cases partialReply <;> cases high <;>
  simp_all [expected,unitReply,sameExpected]

/-- The native guard cut, not an endpoint premise, determines the full error
or unit value from the actual logged child replies. All eight errors survive. -/
theorem from_cut (shared : Bool) (l : SameGuard) (regular partialReply high out : RU)
 (hr : l.regular=unitReply regular) (hp : l.«partial»=unitReply partialReply)
 (hh : l.high=unitReply high) (cut : cutSameGuard shared l (unitReply out)) :
 out=expected shared regular partialReply high := by
 apply unit_injective
 exact cut.2.1.trans (model shared l regular partialReply high hr hp hh).symm

theorem witness (shared : Bool) (regular partialReply high : RU) :
 ∃ l : SameGuard,l.regular=unitReply regular ∧ l.«partial»=unitReply partialReply ∧
 l.high=unitReply high ∧ cutSameGuard shared l (unitReply (expected shared regular partialReply high)) := by
 obtain ⟨l,hr,hp,hh,cut⟩ := NIT_ControlCuts.same_guard shared (unitReply regular)
  (unitReply partialReply) (unitReply high)
 refine ⟨l,hr,hp,hh,?_⟩
 rw [model shared l regular partialReply high hr hp hh]
 exact cut

#print axioms unit_injective
#print axioms model
#print axioms from_cut
#print axioms witness
end AspisR1.NIT_GuardResult
