import PV_FN_THREAD_f6Provider124ActualContinuation
set_option autoImplicit false
noncomputable section
namespace PV_FN_THREAD_f6Provider124Dispatch
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_FN_THREAD_f6Interfaces
open PV_FN_THREAD_f124_BoxContract

/-- A syntax discriminator, not a runtime payload restriction. ScopeData's
emitted type argument is Deduplicated; Packet's is HashConsedValue. -/
def deduplicatedType : Data → Bool
  | .object [("Regular",.object [("kind",_),("generics",.object
      [("regions",_),("types",.array [.object [("Deduplicated",_)]]),
       ("const_generics",_),("trait_refs",_)])])] => true
  | _ => false

theorem distinct124 : PV_THR2_ScopeArcCall.fn ≠ PV_THR2_Source361PacketChildren.fn58 := by
  intro equal
  have bad := congrArg deduplicatedType equal
  cases bad

/-- The pinned provider's retained table masks the ScopeData124 descriptor,
for EVERY fallback, although its local own-entry body contract is generic.
This is why equality at the provider entry cannot establish the global join. -/
theorem scope_masked {E : Type} (x : Input E) :
    PV_FN_THREAD_f124_Continuation.programs x PV_THR2_ScopeArcCall.fn = none := by
  unfold PV_FN_THREAD_f124_Continuation.programs PV_THR2_PacketConstructorLocalTable.table
  change PV_THR2_PacketOriginalTable.table x.P PV_THR2_ScopeArcCall.fn = none
  unfold PV_THR2_PacketOriginalTable.table
  rw [PV_THR2_PacketDataExactTable.away _ _ distinct124]
  · rw [PV_THR2_Source208Table.away]
    · rfl
    · apply PV_THR2_Source208SavedSyntax.different
      change (none : Option (Nat × Nat)) ≠ some (38973,0)
      intro bad; cases bad
  · intro equal
    have bad := congrArg PV_THR2_OffPath.functionId equal
    cases bad
  · intro equal
    have bad := congrArg PV_THR2_OffPath.functionId equal
    cases bad

/-- A concrete original source resolver selecting the actual1916 call.
All other tokens retain the exact provider table. Transport through the124
body still needs a trace-indexed neutrality proof; it is not asserted here. -/
def sourcePrograms {E : Type} (x : Input E) (fn : Data) : Option PV_STX2_SliceSyntax.Program := by
  classical
  exact if fn = PV_THR2_ScopeArcCall.fn then some PV_THR2_F124.live
    else PV_FN_THREAD_f124_Continuation.programs x fn

theorem at1916 {E : Type} (x : Input E) :
    sourcePrograms x PV_THR2_ScopeArcCall.fn = some PV_THR2_F124.live := by
  simp only [sourcePrograms,ite_true]

theorem tables_differ {E : Type} (x : Input E) :
    sourcePrograms x ≠ PV_FN_THREAD_f124_Continuation.programs x := by
  intro equal
  have bad := congrFun equal PV_THR2_ScopeArcCall.fn
  rw [at1916,scope_masked] at bad
  cases bad

/-- Execute ONLY f6's original call-entry step at1916, under its concrete
source resolver. The resulting complete state IS the provider entry. No124
instruction or provider Post is recomputed by this join. -/
theorem enter (C : Carrier OWNER Data) (b : Bool) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (H : Backend PV_RJ4IDB.NativeEvent)
    (resources : PV_EVHB_OwnerHeap.Resources) (encode : PV_EVHB_OwnerHeap.Encode)
    (shape : PV_THR2_TypedRepresentation_ArcInner.Shape)
    (s : Store Data) (a : Nat) (parents : List Frame) (counter thread panicked : Data)
    (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config) :
    let y := PV_FN_THREAD_f6InterfaceSites.arcInput s a parents counter thread panicked w es stack
    let x := PV_FN_THREAD_f6Provider124Entry.convert C b K P H y (PV_THR2_ScopeData.value counter thread panicked)
    PV_THR2_IntrinsicState.advance (PV_THR2_OwnInitExactReturnedCases.carrier C b) K
      (sourcePrograms x) (PV_FN_THREAD_f124_Interface.installed x H resources encode shape).H 1
      ⟨⟨.running (PV_FN_THREAD_f6ScopeData.pending s a parents counter thread panicked),w,es⟩,stack⟩ =
      PV_FN_THREAD_f124_Arbitrary.entry x := by
  let y := PV_FN_THREAD_f6InterfaceSites.arcInput s a parents counter thread panicked w es stack
  let x := PV_FN_THREAD_f6Provider124Entry.convert C b K P H y (PV_THR2_ScopeData.value counter thread panicked)
  let M : Machine PV_RJ4IDB.NativeEvent := ⟨PV_THR2_OwnInitExactReturnedCases.carrier C b,K,
    sourcePrograms x,(PV_FN_THREAD_f124_Interface.installed x H resources encode shape).H⟩
  change PV_THR2_IntrinsicState.advance M.carrier M.control M.programs M.handler 1 _ = _
  rw [PV_FN_THREAD_f6Provider124Entry.same_entry C b K P H y _ (by rfl)]
  apply PV_FN_THREAD_f6InterfaceSites.one_enter M
  · rfl
  · exact at1916 x

#print axioms distinct124
#print axioms scope_masked
#print axioms at1916
#print axioms tables_differ
#print axioms enter
end PV_FN_THREAD_f6Provider124Dispatch
