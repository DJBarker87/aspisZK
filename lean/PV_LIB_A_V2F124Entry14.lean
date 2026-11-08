import PV_LIB_A_V2ActualBindings14
import PV_LIB_A_CallNumbers13
import PV_STX2_LiveNumbering
import PV_THR2_F124
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_V2F124Entry14
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_THR2_SourceStoreLibrary PV_LIB_StoreActionTable
open PV_LIB_A_StructuredFrontier13
abbrev src := PV_LIB_A_PrefixNativeCalls14.src124
abbrev rest := PV_LIB_A_PrefixNativeCalls14.rest124
abbrev steps (C : Carrier OWNER Data) := PV_LIB_A_StructuredFrontier13.steps C src rest
abbrev after (C : Carrier OWNER Data) := PV_LIB_A_StructuredFrontier13.after C src rest PV_THR2_F124.live

/-- The actual1916 call enters BODY124 on ORIGINAL v2, or retains its operand
gap. It is never polled as an opaque native constructor on the full table. -/
theorem run (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (body124 : P (fn src) = some PV_THR2_F124.live)
    (resources : Resources) (encode : Encode) (H : Handler)
    (values : Values OWNER PV_RJ4IDB.NativeEvent) (q : State) :
    PV_LIB_StoreActionTable.advance C K P resources encode H values (steps C q) q = after C q := by
  apply PV_LIB_A_V2Frontiers14.structured
  · decide
  · intro t a parents loops vs
    cases vs with
    | nil => exact ⟨rfl,rfl⟩
    | cons v vs => cases vs <;> exact ⟨rfl,rfl⟩
  · intro t a parents loops vs
    apply PV_THR2_IntrinsicFrameOrdinary.run
    intro eq
    have bad := congrArg PV_THR2_OffPath.functionId eq
    cases bad
  · intro s a w; rfl
  · exact body124

/-- Reuse the slice live-numbering push theorem BY NAME at the actual issued
124 frame. Entry numbering is derived; no callee return counter is equated. -/
theorem numbered (s : Store Data) (a : Nat) (parents : List Frame) (loops : List LoopFrame)
    (payload : Data) (live : a < s.nextActivation)
    (lower : PV_STX2_LiveNumbering.StackBelow s.nextActivation a parents) :
    PV_STX2_LiveNumbering.Numbered
      (PV_THR2_IntrinsicFrameEnter.entered s a parents loops rest (fn src) [payload] 3 PV_THR2_F124.live) := by
  let p := PV_THR2_IntrinsicFrameEnter.pending s a parents loops rest (fn src) [payload] 3
  have pending : PV_STX2_LiveNumbering.Numbered p := by
    change a < (PV_THR2_StaticCall.issued s [payload]).nextActivation ∧
      (a < s.nextActivation ∧ s.nextActivation < (PV_THR2_StaticCall.issued s [payload]).nextActivation) ∧
      PV_STX2_LiveNumbering.StackBelow (PV_THR2_StaticCall.issued s [payload]).nextActivation a parents
    rw [PV_LIB_A_CallNumbers13.issued_counter]
    exact ⟨by omega,⟨live,by omega⟩,PV_STX2_LiveNumbering.stack_mono lower (by omega)⟩
  exact PV_STX2_LiveNumbering.push p PV_THR2_F124.live (fn src) s.nextActivation [payload]
    (PV_THR2_StaticReply.wait s (fn src) [payload] 3) pending rfl rfl

#print axioms run
#print axioms numbered
end PV_LIB_A_V2F124Entry14
