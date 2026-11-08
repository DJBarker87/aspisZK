import PV_LIB_A_PreActionTraceV3
import PV_LIB_A_CloneValidityV2
import PV_LIB_A_ArcPollV2
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_ClonePrologueV2
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_THR2_SourceStoreLibrary
abbrev State := PV_LIB_A_OwnerStoreV3.State
abbrev Handler := PV_LIB_A_OwnerStoreV3.Handler

def stores (s : Store Data) (a : Nat) (n : Nat) : Store Data :=
  let s1 := write s ⟨a,18,[]⟩ none
  let s2 := write s1 ⟨a,23,[]⟩ none
  let s3 := write s2 ⟨a,24,[]⟩ none
  match n with
  | 0 => s
  | 1 => s1
  | 2 => s2
  | 3 => s3
  | _ => write s3 ⟨a,24,[]⟩
      (some (PV_STX2_TypedReferences.reference ⟨a,17,[]⟩ .null))

def source (s : Store Data) (a : Nat) (parents : List Frame) (w : OWNER)
    (es : List PV_RJ4IDB.NativeEvent) (stack : List Config) (n : Nat) : State :=
  ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F361.live.body.drop (59+n)},parents,
    stores s a n⟩,w,es⟩,stack⟩

/-- The five actual pre-poll source shapes, independently of their stores.
No registration/operator/allocation action is classified as neutral. -/
theorem quiet (P : Data → Option PV_STX2_SliceSyntax.Program) (s : Store Data) (a : Nat)
    (parents : List Frame) (w : OWNER) (es : List PV_RJ4IDB.NativeEvent)
    (stack : List Config) (n : Fin 5) :
    PV_LIB_A_PreActionTraceV3.Quiet P (source s a parents w es stack n.val) := by
  refine ⟨PV_LIB_A_PreActionTraceV3.nonwaiting P _ w es stack rfl,?_⟩
  intro c running
  cases running
  fin_cases n <;> refine ⟨rfl,rfl,?_⟩
  · change ¬ (361 = 361 ∧ 12802 = 14320 ∧ false = true ∧ 18 = 45)
    decide
  · change ¬ (361 = 361 ∧ 12803 = 14320 ∧ true = true ∧ 23 = 45)
    decide
  · change ¬ (361 = 361 ∧ 12804 = 14320 ∧ true = true ∧ 24 = 45)
    decide
  · trivial
  · trivial


/-- Named source primitive results build ONLY the local guard trace. The
interpreter transport itself is the single generic induction in PreActionTraceV2.
No constructor or earlier entry prefix is replayed. -/
theorem trace (C : Carrier OWNER Data) (b : Bool) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (H : Handler)
    (s : Store Data) (a : Nat) (parents : List Frame) (w : OWNER)
    (es : List PV_RJ4IDB.NativeEvent) (stack : List Config) :
    PV_LIB_A_PreActionTraceV3.Trace (PV_THR2_OwnInitExactReturnedCases.carrier C b) K P H 5
      (source s a parents w es stack 0) := by
  let B := PV_THR2_OwnInitExactReturnedCases.carrier C b
  have h0 : PV_THR2_IntrinsicState.step B K P H (source s a parents w es stack 0) =
      source s a parents w es stack 1 := by
    exact PV_THR2_IntrinsicFrameSteps.storage B K P H s a parents [] _
      ⟨361,12802,.array [.atom "body",.atom "statements",.number 59]⟩ false 18 w es stack
  have h1 : PV_THR2_IntrinsicState.step B K P H (source s a parents w es stack 1) =
      source s a parents w es stack 2 := by
    exact PV_THR2_IntrinsicFrameSteps.storage B K P H (stores s a 1) a parents [] _
      ⟨361,12803,.array [.atom "body",.atom "statements",.number 60]⟩ true 23 w es stack
  have h2 : PV_THR2_IntrinsicState.step B K P H (source s a parents w es stack 2) =
      source s a parents w es stack 3 := by
    exact PV_THR2_IntrinsicFrameSteps.storage B K P H (stores s a 2) a parents [] _
      ⟨361,12804,.array [.atom "body",.atom "statements",.number 61]⟩ true 24 w es stack
  have h3 : PV_THR2_IntrinsicState.step B K P H (source s a parents w es stack 3) =
      source s a parents w es stack 4 := by
    exact PV_THR2_IntrinsicFrameSteps.localRef _ K P H (stores s a 3) a 17 24 parents [] _
      ⟨361,12805,.array [.atom "body",.atom "statements",.number 62]⟩ b w es stack
  change PV_LIB_A_PreActionTraceV3.Quiet P (source s a parents w es stack 0) ∧ _
  refine ⟨quiet P s a parents w es stack 0,?_⟩
  rw [h0]
  refine ⟨quiet P s a parents w es stack 1,?_⟩
  rw [h1]
  refine ⟨quiet P s a parents w es stack 2,?_⟩
  rw [h2]
  refine ⟨quiet P s a parents w es stack 3,?_⟩
  rw [h3]
  exact ⟨quiet P s a parents w es stack 4,True.intro⟩

/-- The original native call issuance is still a source step. Its receiver
comes from the generated17->24 reference and move, not a supplied alias. -/
theorem issue (C : Carrier OWNER Data) (b : Bool) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (H : Handler)
    (s : Store Data) (a : Nat) (parents : List Frame) (w : OWNER)
    (es : List PV_RJ4IDB.NativeEvent) (stack : List Config) :
    PV_THR2_IntrinsicState.step (PV_THR2_OwnInitExactReturnedCases.carrier C b) K P H
      (source s a parents w es stack 4) =
      ⟨⟨.running (PV_LIB_A_ArcPollV2.config (PV_LIB_A_CloneValidityV2.prepare s a) a parents),w,es⟩,stack⟩ := by
  apply PV_THR2_IntrinsicFrameSteps.call
  simp [operands,operand,PV_STX2_Store.read,locate,writeAddress,write,stores,
    PV_LIB_A_CloneValidityV2.prepare,PV_LIB_A_ArcPollV2.args]

/-- Corrected OWNER-aware history through all five source steps to12950.
Native reply/pending/failure handling begins at the resulting poll and is
provided by ArcPollV2.actual_poll, separately, for the complete reply. -/
theorem run (C : Carrier OWNER Data) (b : Bool) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent)
    (s : Store Data) (a : Nat) (parents : List Frame) (w : OWNER)
    (es : List PV_RJ4IDB.NativeEvent) (stack : List Config) :
    PV_LIB_A_OwnerStoreV3.advance (PV_THR2_OwnInitExactReturnedCases.carrier C b) K P
      resources encode H values 5 (source s a parents w es stack 0) =
      ⟨⟨.running (PV_LIB_A_ArcPollV2.config (PV_LIB_A_CloneValidityV2.prepare s a) a parents),w,es⟩,stack⟩ := by
  rw [PV_LIB_A_PreActionTraceV3.run _ K P resources encode H values 5 _
    (trace C b K P H s a parents w es stack)]
  have chainProof := PV_THR2_Source361Chain59To63.run
    (PV_THR2_OwnInitExactReturnedCases.carrier C b) K P H (source s a parents w es stack 0)
  have eq4 : PV_THR2_IntrinsicState.advance
      (PV_THR2_OwnInitExactReturnedCases.carrier C b) K P H 4
      (source s a parents w es stack 0) = source s a parents w es stack 4 := by
    have cost : PV_THR2_Source361Chain59To63.steps
        (PV_THR2_OwnInitExactReturnedCases.carrier C b) (source s a parents w es stack 0) = 4 := by
      simp only [PV_THR2_Source361Chain59To63.steps,PV_THR2_IntrinsicAtContinuation.steps,
        source,PV_THR2_IntrinsicAtContinuation.Ready,and_self,if_true]
      rfl
    have result : PV_THR2_Source361Chain59To63.after
        (PV_THR2_OwnInitExactReturnedCases.carrier C b) (source s a parents w es stack 0) =
        source s a parents w es stack 4 := by
      simp only [PV_THR2_Source361Chain59To63.after,PV_THR2_IntrinsicAtContinuation.after,
        source,PV_THR2_IntrinsicAtContinuation.Ready,and_self,if_true]
      rfl
    simpa only [cost,result] using chainProof
  rw [show (5 : Nat) = 4+1 from rfl,PV_THR2_IntrinsicComposition.advance_add,eq4]
  exact issue C b K P H s a parents w es stack

#print axioms quiet
#print axioms trace
#print axioms issue
#print axioms run
end PV_LIB_A_ClonePrologueV2
