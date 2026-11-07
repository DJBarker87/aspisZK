import NLV_State
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLV
open Aeneas Aeneas.Std Result
def emptyOwnership : Ownership := ⟨fun _=>none,fun _=>0,fun _=>false⟩
/-- Private driver ownership starts empty BY CONSTRUCTION, rather than a new
global-state premise. Proof/public snapshots are the actual input values. -/
def initial (i : NLJ_Tx1.Input) (frame : NLJ_Packets.Frame094) : State :=
 ⟨⟨i,.guard⟩,{frame with proof:=i.proof,publicBytes:=i.publicBytes},emptyOwnership,[]⟩
theorem initial_admission (i : NLJ_Tx1.Input) (frame : NLJ_Packets.Frame094) :
 InputAdmission (initial i frame) := ⟨rfl,rfl⟩
theorem initial_private (i : NLJ_Tx1.Input) (frame : NLJ_Packets.Frame094) (kind : OwnedKind) :
 (initial i frame).ownership.allocations kind=none := rfl
theorem initial_external (i : NLJ_Tx1.Input) (frame : NLJ_Packets.Frame094) :
 (initial i frame).external.externalBytes=frame.externalBytes ∧
 (initial i frame).external.externalMetadata=frame.externalMetadata ∧
 (initial i frame).external.authority=frame.authority := ⟨rfl,rfl,rfl⟩
#print axioms initial_admission
#print axioms initial_private
#print axioms initial_external
end AspisR1.NLV
end
