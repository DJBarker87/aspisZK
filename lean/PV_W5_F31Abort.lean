import PV_W5_F31ErrorReply
set_option autoImplicit false
set_option pp.proofs false
noncomputable section
namespace PV_W5_F31Abort
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_EVHB_OWNER
open PV_STX2_SliceMachine

def cleanup : List PV_STX2_SliceSyntax.Node :=
  [PV_STX2_Source7CtorF31.node11,PV_STX2_Source7CtorF31.node12,
   PV_STX2_Source7CtorF31.node13,PV_STX2_Source7CtorF31.node14,
   PV_STX2_Source7CtorF31.node15,PV_STX2_Source7CtorF31.node16,
   PV_STX2_Source7CtorF31.node17,PV_STX2_Source7CtorF31.node18]
def stored (s : Store Data) (a : Nat) :=
  [14,13,8,7,3,2,1,15].foldl (fun t n => write t ⟨a,n,[]⟩ none) s

theorem native9 (D : Carrier OWNER Data) (K : Control) (H : PV_W5_F35Modes.HType)
    (s : Store Data) (parents : List Frame) (a : Nat) (w : OWNER) :
    PV_STX2_SliceMachine.advance D K (fun _ => none) H 9
      ⟨.running ⟨{activation:=a,remaining:=PV_W5_F31ErrorCall.after},parents,s⟩,w,[]⟩ =
      ⟨.fault .abort (stored s a),w,[]⟩ := rfl

theorem source9 (resources : Resources) (encode : Encode)
    (D : Carrier OWNER Data) (K : Control) (H : PV_W5_F35Modes.HType)
    (s : Store Data) (parents : List Frame) (a : Nat) (w : OWNER)
    (prior : List PV_RJ4IDB.NativeEvent) :
    PV_STX2_Source7IterationBindings.advance resources encode D K (fun _ => none) H 9
      ⟨.running ⟨{activation:=a,remaining:=PV_W5_F31ErrorCall.after},parents,s⟩,w,prior⟩ =
      ⟨.fault .abort (stored s a),w,prior⟩ := by
  have tr := PV_STX2_CallSummaryLast.run resources encode D K (fun _ => none) (fun _ => none) H
    cleanup (PV_STX2_Source7CtorF31.node19::PV_STX2_Source7CtorF31.program.body.drop 8)
    a parents s w prior
    (by
      intro node hn
      simp only [cleanup,List.mem_cons,List.not_mem_nil,or_false] at hn
      rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals exact Or.inr ⟨_,rfl,True.intro,True.intro⟩)
    (by
      intro node hn
      simp only [cleanup,List.mem_cons,List.not_mem_nil,or_false] at hn
      rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals rfl)
    (by intro t; exact ⟨True.intro,rfl⟩)
  have native := congrArg (PV_STX2_SlicePrefixEvents.prepend prior) (native9 D K H s parents a w)
  rw [←PV_STX2_SlicePrefixEvents.advance_prepend] at native
  simp only [PV_STX2_SlicePrefixEvents.prepend,List.append_nil] at native
  exact tr.trans native

theorem frame (s : Store Data) (a : Nat) : PV_W5_F59Frame.StoreFrame s (stored s a) a := by
  constructor
  · exact Nat.le_refl _
  · intro p outside older
    rcases p with ⟨pa,pi,pp⟩
    change pa≠a at outside
    simp [stored,write,outside]

#print axioms native9
#print axioms source9
#print axioms frame
end PV_W5_F31Abort
