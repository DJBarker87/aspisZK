import PV_FN_THREAD_f6ProviderInterfaces
import PV_FN_THREAD_f6OwnContinuation
set_option autoImplicit false
noncomputable section
namespace PV_FN_THREAD_f6ProviderCatchPre
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_FN_THREAD_f6Interfaces PV_FN_THREAD_f6InterfaceSites

/-- f6's own Scope construction stores the provider Arc root literally. -/
theorem scope_at {E : Type} (C : Carrier OWNER Data) (b : Bool)
    (t : Store Data) (a : Nat) (parents : List Frame) (p : Address) (capture : Data)
    (w : OWNER) (es : List E) (stack : List Config) (live : a < t.nextActivation) :
    At (PV_THR2_OwnInitExactReturnedCases.carrier C b)
      (catchInput t a parents (PV_FN_THREAD_f222_EntryOwned.root p) capture w es stack).store
      ⟨a,2,[0]⟩ (PV_FN_THREAD_f222_EntryOwned.root p) := by
  have different : (⟨a,2,[]⟩ : Address) ≠ ⟨t.nextActivation,1,[]⟩ := by
    intro h
    exact (Nat.ne_of_lt live) (congrArg Address.activation h)
  refine ⟨PV_THR2_ScopeValue.value (PV_FN_THREAD_f222_EntryOwned.root p),?_,?_⟩
  · simp [catchInput,one,PV_THR2_IntrinsicFrameEnter.pending,
      PV_FN_THREAD_f6OwnContinuation.prepared,PV_THR2_ScopeValue.prepared,
      PV_THR2_ScopeCapturePrefix.prepared,PV_THR2_ScopeCaptureWrap.prepared,
      PV_THR2_StaticCall.issued,PV_STX2_Native.arguments,write,different]
  · rfl

/-- The source writes between124 and125 frame the actual backing cell.
The age bounds are allocation-Post projections; no consumer Arc encoding. -/
theorem backing_at {E : Type} (B : Carrier OWNER Data) (t : Store Data) (a : Nat)
    (parents : List Frame) (p : Address) (capture value : Data)
    (w : OWNER) (es : List E) (stack : List Config)
    (outside : p.activation ≠ a) (bounded : p.activation < t.nextActivation)
    (backing : At B t p value) :
    At B (catchInput t a parents (PV_FN_THREAD_f222_EntryOwned.root p) capture w es stack).store p value := by
  rcases backing with ⟨root,cell,path⟩
  refine ⟨root,?_,path⟩
  rw [(catch_site t a parents (PV_FN_THREAD_f222_EntryOwned.root p) capture w es stack).2.2]
  rw [PV_FN_THREAD_f6OwnContinuation.issued_frame t a parents
    (PV_FN_THREAD_f222_EntryOwned.root p) capture
    (⟨p.activation,p.localIndex,[]⟩ : Address) bounded outside]
  exact cell

/-- Named125 dependency at1989, over provider representation definitions.
Source writes and allocation bounds supply its entry projections; this does
not assume a124 consumer contract or any future126 read. -/
theorem at1989 {E : Type} (C : Carrier OWNER Data) (b : Bool) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (thread_f125 : PV_FN_THREAD_f6ProviderInterfaces.f125
      (⟨PV_THR2_OwnInitExactReturnedCases.carrier C b,K,P,H⟩ : Machine E))
    (t : Store Data) (a : Nat) (parents : List Frame) (p : Address)
    (capture strong weak payload : Data) (w : OWNER) (es : List E) (stack : List Config)
    (above : a < p.activation) (bounded : p.activation < t.nextActivation)
    (owner : OwnerWellFormed w t.nextActivation)
    (backing : At (PV_THR2_OwnInitExactReturnedCases.carrier C b) t p
      (PV_THR2_KeyValues.pack PV_THR2_Packet124Aggregate13.source.2.2.1 [strong,weak,payload])) :
    let M : Machine E := ⟨PV_THR2_OwnInitExactReturnedCases.carrier C b,K,P,H⟩
    let x := catchInput t a parents (PV_FN_THREAD_f222_EntryOwned.root p) capture w es stack
    FullPost M x (fun s _ result =>
      At M.carrier s ⟨a,2,[0]⟩ (PV_FN_THREAD_f222_EntryOwned.root p) ∧
      (∃ strong' weak', At M.carrier s p (PV_THR2_KeyValues.pack
        PV_THR2_Packet124Aggregate13.source.2.2.1 [strong',weak',payload])) ∧
      (K.variant result = some 0 ∨ K.variant result = some 1)) := by
  apply thread_f125 _ a capture p strong weak payload rfl rfl
  · apply one_valid
    · exact Nat.lt_trans above bounded
    · exact owner
  · exact scope_at C b t a parents p capture w es stack (Nat.lt_trans above bounded)
  · exact backing_at _ t a parents p capture _ w es stack (Nat.ne_of_lt above).symm bounded backing

#print axioms scope_at
#print axioms backing_at
#print axioms at1989
end PV_FN_THREAD_f6ProviderCatchPre
