import PV_W5_F31ExceptionalReply
import PV_STX2_ToVecConstructorExtract
set_option autoImplicit false
set_option pp.proofs false
noncomputable section
namespace PV_W5_F31SuccessStore
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_EVHB_OWNER
open PV_STX2_SliceMachine PV_STX2_Source7ConstructorEntry

def returned (s : Store Data) (a : Nat) (length alloc layout value : Data) :=
  write (write (entered s a length alloc layout) ⟨s.nextActivation,0,[]⟩ (some value))
    ⟨a,4,[]⟩ (some value)

theorem received (D : Carrier OWNER Data) (s : Store Data) (parents : List Frame)
    (a : Nat) (length alloc layout value : Data) (w : OWNER)
    (events prior : List PV_RJ4IDB.NativeEvent) :
    PV_W5_F31Replies.received D s parents a length alloc layout ⟨.returned (.ok value),w,events⟩ prior =
      ⟨.running ⟨{activation:=a,remaining:=PV_STX2_Source7CtorF31.program.body.drop 7},parents,
        returned s a length alloc layout value⟩,w,prior++events⟩ := rfl

theorem argument (s : Store Data) (a i : Nat) (length alloc layout value : Data)
    (live : a<s.nextActivation) (index : i≠4) (not2 : i≠2) (not0 : i≠0)
    (not8 : i≠8) (not13 : i≠13) (not15 : i≠15) :
    (returned s a length alloc layout value).cells ⟨a,i,[]⟩ = s.cells ⟨a,i,[]⟩ := by
  have distinct : a≠s.nextActivation := by omega
  simp only [returned,write]
  simp only [Address.mk.injEq,and_self,and_true,and_false,true_and,false_and,index,distinct,ite_false]
  rw [entered,PV_W5_LeafBoundary.arguments_frame _ _ _ _ _ distinct]
  simp [prepared,write,index,not2,not0,not8,not13,not15]

theorem suffix_frame (s : Store Data) (a cap : Nat) :
    PV_W5_F59Frame.StoreFrame s (PV_STX2_Source7QF31Suffix.stored s a cap) a := by
  constructor
  · exact Nat.le_refl _
  · intro p outside older
    rcases p with ⟨pa,pi,pp⟩
    change pa≠a at outside
    simp [PV_STX2_Source7QF31Suffix.stored,PV_STX2_Source7QF31Return.stored,
      PV_STX2_Source7QF31Assert.stored,PV_STX2_Source7QF31Capacity.stored,
      PV_STX2_Source7QF31Layout.stored,write,outside]

theorem returned_frame (s : Store Data) (a : Nat) (length alloc layout value : Data) :
    PV_W5_F59Frame.StoreFrame s (returned s a length alloc layout value) a := by
  have base := PV_W5_F31ExceptionalReply.entered_frame s a length alloc layout
  constructor
  · exact base.1
  · intro p outside older
    have fresh : p.activation≠s.nextActivation := Nat.ne_of_lt older
    have own : p≠(⟨a,4,[]⟩ : Address) := by intro h; exact outside (congrArg Address.activation h)
    have child : p≠(⟨s.nextActivation,0,[]⟩ : Address) := by intro h; exact fresh (congrArg Address.activation h)
    simpa only [returned,write,if_neg own,if_neg child] using base.2 p outside older

theorem extracted_frame (s : Store Data) (a : Nat) (inner : Data) :
    PV_W5_F59Frame.StoreFrame s (PV_STX2_Source7QResultIntoF31.stored s a inner) a := by
  constructor
  · exact Nat.le_refl _
  · intro p outside older
    rcases p with ⟨pa,pi,pp⟩
    change pa≠a at outside
    simp [PV_STX2_Source7QResultIntoF31.stored,write,outside]

#print axioms returned_frame
#print axioms extracted_frame

#print axioms suffix_frame

#print axioms received
#print axioms argument
end PV_W5_F31SuccessStore
