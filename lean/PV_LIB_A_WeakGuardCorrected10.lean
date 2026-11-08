import PV_LIB_A_WeakGuardSource10
import PV_LIB_A_DestructorStep10
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_WeakGuardCorrected10
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_THR2_SourceStoreLibrary
open PV_LIB_StoreActionTable PV_LIB_A_WeakGuardSource10 PV_LIB_A_WeakGuardRun10

def stage (s : Store Data) (a : Nat) (p : Address) : Nat → Store Data
  | 0 => write s ⟨a,1,[]⟩ (some (PV_STX2_TypedReferences.reference p .null))
  | 1 => write (stage s a p 0) ⟨a,0,[]⟩ none
  | 2 => write (stage s a p 1) ⟨a,2,[]⟩ none
  | 3 => write (stage s a p 2) ⟨a,3,[]⟩ none
  | 4 => write (stage s a p 3) ⟨a,0,[]⟩ (some PV_LIB_A_DestructorValues10.unitValue)
  | 5 => write (stage s a p 4) ⟨a,2,[]⟩ (some (PV_STX2_TypedReferences.reference p .null))
  | _ => prepared s a p

def configuration (types : List Data) (s : Store Data) (a : Nat)
    (parents : List Frame) (p : Address) (n : Nat) : Config :=
  ⟨{activation := a,remaining := (PV_LIB_A_TypedBody661.program types).body.drop n,
    waiting := if n = 6 then some (waiting types s p) else none},parents,stage s a p n⟩

theorem raw_step (C : Carrier OWNER Data) (K : Control) (b : Bool)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (H : Handler)
    (types : List Data) (s : Store Data) (a : Nat) (parents : List Frame)
    (p : Address) (w : OWNER) (n : Nat) (bound : n < 6) :
    PV_STX2_SliceMachine.step
      (PV_LIB_A_UnwindMatch.carrier (PV_LIB_A_DestructorValues10.carrier C b) K) K P H
      (configuration types s a parents p n) w =
      ⟨.running (configuration types s a parents p (n+1)),w,[]⟩ := by
  have cases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [configuration,stage,PV_LIB_A_UnwindMatch.carrier,PV_LIB_A_GenericDropMachine.unitTag,after,prepared,waiting,issued,entry,PV_STX2_Native.arguments,PV_LIB_A_DestructorValues10.unitValue,PV_STX2_SliceMachine.advance,PV_STX2_SliceMachine.step,
    PV_STX2_SliceMachine.native,PV_STX2_SliceMachine.adopt,
    PV_LIB_A_TypedBody661.program,PV_LIB_A_TypedBody661.block11,
    PV_LIB_A_TypedBody661.node0,PV_LIB_A_TypedBody661.node1,
    PV_LIB_A_TypedBody661.node2,PV_LIB_A_TypedBody661.node3,
    PV_LIB_A_TypedBody661.node4,PV_LIB_A_TypedBody661.node5,
    PV_STX2_Native.step,PV_STX2_Store.bind,PV_STX2_Store.evaluate,
    PV_STX2_Store.operand,PV_STX2_Store.operands,PV_STX2_Store.read,
    PV_STX2_Store.locate,PV_STX2_Store.writeAddress,write,
    carrier,PV_LIB_A_DestructorValues10.carrier,
    PV_THR2_AggregateCompletion.carrier,PV_THR2_OwnInitExactReturnedCases.carrier,
    PV_THR2_EntryDynamic.carrier,PV_THR2_Scalars.carrier,
    PV_STX2_TypedReferences.carrier,PV_STX2_LengthBranch.carrier,
    PV_STX2_Aggregates.carrier,PV_STX2_Aggregates.aggregate,
    PV_THR2_FunctionValues.base,PV_THR2_KeyInstall.carrier,
    PV_THR2_KeyValues.carrier,PV_THR2_ThreadFields.carrier,
    PV_STX2_TypedReferences.roundtrip,call]



/-- Each guard source instruction runs on the repaired OWNER-aware step.
All selectors are discharged from actual emitted instruction shape. -/
theorem corrected_step (C : Carrier OWNER Data) (K : Control) (b : Bool)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent)
    (types : List Data) (s : Store Data) (a : Nat) (parents : List Frame)
    (p : Address) (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config)
    (n : Nat) (bound : n < 6) :
    PV_LIB_A_WeakOwnerFree10.step (PV_THR2_OwnInitExactReturnedCases.carrier C b) K
      P resources encode H values
      ⟨⟨⟨.running (configuration types s a parents p n),w,es⟩,stack⟩,none⟩ =
      ⟨⟨⟨.running (configuration types s a parents p (n+1)),w,es⟩,stack⟩,none⟩ := by
  have raw := raw_step C K b (v2ProvenancePrograms P) H types s a parents p w n bound
  have defined : ∀ site t,
      (PV_STX2_SliceMachine.step
        (PV_LIB_A_UnwindMatch.carrier (PV_LIB_A_DestructorValues10.carrier C b) K) K
        (v2ProvenancePrograms P) H (configuration types s a parents p n) w).status ≠
          .undefined site t := by
    rw [raw]
    intro site t bad
    cases bad
  rw [PV_LIB_A_DestructorStep10.ordinary (interpreted := defined)]
  · rw [show PV_STX2_SliceMachine.step
      (PV_LIB_A_UnwindMatch.carrier
        (PV_THR2_AggregateCompletion.carrier (PV_THR2_OwnInitExactReturnedCases.carrier C b)) K)
      K (v2ProvenancePrograms P) H (configuration types s a parents p n) w = _ from raw]
    simp only [List.append_nil]
  all_goals
    have cases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [configuration,PV_LIB_A_TypedBody661.program,
      PV_LIB_A_TypedBody661.block11,PV_LIB_A_TypedBody661.node0,
      PV_LIB_A_TypedBody661.node1,PV_LIB_A_TypedBody661.node2,
      PV_LIB_A_TypedBody661.node3,PV_LIB_A_TypedBody661.node4,
      PV_LIB_A_TypedBody661.node5,PV_THR2_OwnInitAction.selected,
      PV_THR2_OperatorAction.selected,PV_THR2_OperatorAction.instruction,
      PV_THR2_OwnUniformNeutral.configuration,PV_THR2_OwnUniformNeutral.instruction,
      PV_THR2_Dynamic.active,PV_THR2_Dynamic.operandOf]

#print axioms stage
#print axioms configuration
#print axioms raw_step
#print axioms corrected_step
end PV_LIB_A_WeakGuardCorrected10
