import PV_STX2_IntrinsicSemantics_CopyNonOverlapping
set_option autoImplicit false
noncomputable section
namespace PV_STX2_CopyReplyInterpretation
open Aeneas Aeneas.Std PV_STX_Machine PV_EVHB_OWNER
/-- Conditional on owner acceptance of the translator patch. Interpret the
emitted native copy success using the OWNER byte action. Every other answer,
including pending, failure, divergence and abort, retains its exact world. -/
def interpret {E : Type} (source target count : Nat) (r : Reply OWNER E PV_STX2_Syntax.Data) :
    Reply OWNER E PV_STX2_Syntax.Data :=
  match r.answer with
  | .returned (.ok _) => {r with world := PV_EVHB_OwnerHeap.copied r.world source target (count*4)}
  | _ => r
/-- Conditional on owner acceptance of the translator patch. The named
intrinsic equation is consumed here; input is the pre-action byte map. -/
theorem success {E : Type} (source target count : Nat) (w : OWNER)
    (answer : PV_STX2_Syntax.Data) (events : List E) :
    (interpret source target count ⟨.returned (.ok answer),w,events⟩).world.world.memory =
      fun address => if target ≤ address ∧ address < target+count*4 then
        w.world.memory (source+(address-target)) else w.world.memory address :=
  PV_STX2_IntrinsicSemantics_CopyNonOverlapping_installed w source target count
/-- Conditional on owner acceptance of the translator patch. Answer and
observable events are never changed by the intrinsic interpretation. -/
theorem reply_preserved {E : Type} (source target count : Nat)
    (r : Reply OWNER E PV_STX2_Syntax.Data) :
    (interpret source target count r).answer = r.answer ∧
      (interpret source target count r).events = r.events := by
  cases r with
  | mk answer w events =>
    cases answer with
    | pending => exact ⟨rfl,rfl⟩
    | fault f => exact ⟨rfl,rfl⟩
    | returned result => cases result <;> exact ⟨rfl,rfl⟩
#print axioms interpret
#print axioms success
#print axioms reply_preserved
end PV_STX2_CopyReplyInterpretation
