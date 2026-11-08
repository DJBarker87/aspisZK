import PV_FN_THREAD_f6DerefInterfaces
import PV_FN_THREAD_f6CatchPre
set_option autoImplicit false
noncomputable section
namespace PV_FN_THREAD_f6DerefPre
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_FN_THREAD_f6Interfaces PV_FN_THREAD_f6DerefInterfaces

/-- The three own prefixes and fresh argument binding preserve Scope's
root cell. This uses source writes, not a callee memory assumption. -/
theorem scope_cell {E : Type} (site : PV_FN_THREAD_f6DerefInterfaces.Site) (t : Store Data) (a : Nat)
    (parents : List Frame) (saved : List LoopFrame) (w : OWNER) (es : List E)
    (stack : List Config) (live : a < t.nextActivation) :
    (input site t a parents saved w es stack).store.cells ⟨a,2,[]⟩ =
      t.cells ⟨a,2,[]⟩ := by
  have neq : (⟨a,2,[]⟩ : Address) ≠ ⟨t.nextActivation,1,[]⟩ := by
    intro h
    exact (Nat.ne_of_lt live) (congrArg Address.activation h)
  cases site <;>
    simp [input,preStore,PV_FN_THREAD_f6InterfaceSites.one,
      PV_THR2_IntrinsicFrameEnter.pending,PV_THR2_StaticCall.issued,
      PV_STX2_Native.arguments,PV_FN_THREAD_f6CompletionEntry.prepared,
      PV_FN_THREAD_f6CompletionEntry.guards,PV_FN_THREAD_f6ParkDeref.prepared,
      PV_FN_THREAD_f6FinalDerefRequest.prepared,write,neq]

/-- No source prefix writes an Arc backing activation. Its bounds come from
124's fresh-allocation Post and the intervening monotonically growing stores. -/
theorem backing_cell {E : Type} (site : PV_FN_THREAD_f6DerefInterfaces.Site) (t : Store Data) (a : Nat)
    (parents : List Frame) (saved : List LoopFrame) (w : OWNER) (es : List E)
    (stack : List Config) (p : Address) (outside : p.activation ≠ a)
    (bounded : p.activation < t.nextActivation) :
    (input site t a parents saved w es stack).store.cells
      ⟨p.activation,p.localIndex,[]⟩ = t.cells ⟨p.activation,p.localIndex,[]⟩ := by
  have neq (i : Nat) : (⟨p.activation,p.localIndex,[]⟩ : Address) ≠ ⟨a,i,[]⟩ := by
    intro h
    exact outside (congrArg Address.activation h)
  have fresh : (⟨p.activation,p.localIndex,[]⟩ : Address) ≠ ⟨t.nextActivation,1,[]⟩ := by
    intro h
    exact (Nat.ne_of_lt bounded) (congrArg Address.activation h)
  cases site <;>
    simp [input,preStore,PV_FN_THREAD_f6InterfaceSites.one,
      PV_THR2_IntrinsicFrameEnter.pending,PV_THR2_StaticCall.issued,
      PV_STX2_Native.arguments,PV_FN_THREAD_f6CompletionEntry.prepared,
      PV_FN_THREAD_f6CompletionEntry.guards,PV_FN_THREAD_f6ParkDeref.prepared,
      PV_FN_THREAD_f6FinalDerefRequest.prepared,write,neq,fresh]

/-- At each of 2097,2306,2659 the source reference and the SAME ArcInner
backing supply126's Pre. The backing witness is internal allocation provenance,
not an extra f6 entry premise or a guessed pointee. -/
theorem at_actual126 {E : Type} (M : Machine E) (thread_f126 : f126 M)
    (site : PV_FN_THREAD_f6DerefInterfaces.Site) (t : Store Data) (a : Nat) (parents : List Frame)
    (saved : List LoopFrame) (w : OWNER) (es : List E) (stack : List Config)
    (arc payload : Data) (p : Address) (strong weak : Data)
    (live : a < t.nextActivation) (owner : OwnerWellFormed w t.nextActivation)
    (scopeAt : At M.carrier t ⟨a,2,[0]⟩ arc)
    (representation : arc = PV_THR2_Packet124ReturnData.value
      (PV_STX2_TypedReferences.reference p .null))
    (backing : At M.carrier t p (PV_THR2_KeyValues.pack
      PV_THR2_Packet124Aggregate13.source.2.2.1 [strong,weak,payload]))
    (outside : p.activation ≠ a) (bounded : p.activation < t.nextActivation) :
    let x := input site t a parents saved w es stack
    FullPost M x (fun post _ result => ReadOnlyFrame x post ∧
      ∃ q strong weak, arc = PV_THR2_Packet124ReturnData.value
          (PV_STX2_TypedReferences.reference q .null) ∧
        At M.carrier post q (PV_THR2_KeyValues.pack PV_THR2_Packet124Aggregate13.source.2.2.1
          [strong,weak,payload]) ∧
        result = PV_STX2_TypedReferences.reference {q with fields := q.fields ++ [2]} .null) := by
  apply at_scope_deref M thread_f126 site t a parents saved w es stack arc payload live owner
  · rcases scopeAt with ⟨root,cell,path⟩
    exact ⟨root,(scope_cell site t a parents saved w es stack live).trans cell,path⟩
  · rcases backing with ⟨root,cell,path⟩
    exact ⟨p,strong,weak,representation,root,
      (backing_cell site t a parents saved w es stack p outside bounded).trans cell,path⟩

#print axioms scope_cell
#print axioms backing_cell
#print axioms at_actual126
end PV_FN_THREAD_f6DerefPre
