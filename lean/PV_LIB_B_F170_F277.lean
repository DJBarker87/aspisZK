import PV_LIB_A_PurePoll
set_option autoImplicit false
noncomputable section
namespace PV_LIB_B_F170_F277
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
open PV_W1_LeafBoundary PV_W1_OwnerNativeFrame PV_FN_W4_NativeFootprint
abbrev model := @PV_LIB_A_NativeLeaves.model277
abbrev law := @PV_LIB_A_NativeLeaves.law277
/-- Provider domain follows from the caller world invariant and actual operand
moves. It adds no success or representation-validity premise. -/
theorem caller_domain (C : Carrier OWNER Data) (s t : Store Data) (w : OWNER)
    (a : Nat) (vs : List Data) (parents : List Frame) (loops : List LoopFrame)
    (stack : List Config)
    (wf : PV_W1_OwnerWellFormed.OwnerWellFormed w s.nextActivation)
    (evaluated : PV_FN_W4_NativeContract.evaluated C s w a
      PV_FN_THREAD_f170_Row.native277Call = some (vs,t)) :
    PV_W1_NativeLeaves.Pre
      (PV_FN_W4_NativeContract.entry t a parents loops PV_FN_THREAD_f170_Row.native277Rest
        PV_FN_THREAD_f170_Row.native277Call vs stack) w := by
  change PV_W1_OwnerWellFormed.OwnerWellFormed w t.nextActivation
  rw [PV_FN_W4_NativeContract.counter C s t w a _ vs evaluated]
  exact wf
abbrev certified := @PV_LIB_A_NativeLeaves.certified277
abbrev actual_machine := @PV_LIB_A_PurePoll.installed277
#print axioms model
#print axioms law
#print axioms caller_domain
#print axioms certified
#print axioms actual_machine
end PV_LIB_B_F170_F277
