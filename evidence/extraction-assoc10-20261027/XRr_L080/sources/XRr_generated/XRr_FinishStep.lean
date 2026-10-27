import XRr_EnumerateFrame
open Aeneas Aeneas.Std Result ControlFlow XRk_ResultTools XRn_Join_Release
set_option autoImplicit false
namespace XRr_FinishStep
abbrev It := XRr_EnumerateFrame.It aspis_core.field.QM31
abbrev Back := It → It
abbrev State := It × Back
def Inv (s : State) : Prop := ∀ target, (s.2 target).iter.slice.length=target.iter.slice.length
def measure (s : State) : Nat := s.1.iter.slice.length-s.1.iter.i
theorem source (b : verifier.BatchedWeights) (s : State)
 (r : ControlFlow State Back) (inv : Inv s)
 (run : verifier.BatchedWeights.finish_loop.body b s.1 s.2=ok r) :
 match r with
 | .done back => ∀ target, (back target).iter.slice.length=target.iter.slice.length
 | .cont next => Inv next ∧ measure next<measure s := by
 unfold verifier.BatchedWeights.finish_loop.body at run
 obtain ⟨o,rest,hnext,run⟩ := pair_bind_success _ _ _ run
 rcases rest with ⟨it,restore⟩
 have frame := XRr_EnumerateFrame.source _ s.1 it o restore hnext
 cases o with
 | none =>
   cases Result.ok.inj run
   intro target
   exact (inv _).trans (frame.2.1 target none)
 | some pair =>
   rcases pair with ⟨index,old⟩
   obtain ⟨w,_,run⟩ := bind_success _ _ _ run
   cases Result.ok.inj run
   refine ⟨?_,?_⟩
   · intro target
     exact (inv _).trans (frame.2.1 target (some (index,w)))
   · change it.iter.slice.length-it.iter.i<s.1.iter.slice.length-s.1.iter.i
     obtain ⟨hi,hlt⟩ := frame.2.2
     rw [frame.1,hi]
     omega
#print axioms source
end XRr_FinishStep
