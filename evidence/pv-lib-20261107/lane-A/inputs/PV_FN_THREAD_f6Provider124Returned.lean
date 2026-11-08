import PV_FN_THREAD_f6Provider124Entry
import PV_FN_THREAD_f6ProviderCatchPre
set_option autoImplicit false
noncomputable section
namespace PV_FN_THREAD_f6Provider124Returned
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_FN_THREAD_f6Interfaces
open PV_FN_THREAD_f124_BoxContract

/-- Provider backing provenance and numbering, independent of counter values. -/
theorem backing_bounds {E : Type} (x : Input E) (sv wv : Data)
    (fresh : x.a < x.s.nextActivation) :
    x.a < (PV_FN_THREAD_f124_StorePost.backing x sv wv).activation ∧
    (PV_FN_THREAD_f124_StorePost.backing x sv wv).activation <
      (PV_FN_THREAD_f124_ReturnedPost.store x sv wv).nextActivation := by
  change x.a < x.s.nextActivation+2 ∧ x.s.nextActivation+2 < x.s.nextActivation+9
  constructor <;> omega

/-- The returned provider Post supplies both the emitted NonNull-wrapped Arc
and its initialized pointee, literally in the provider representation. -/
theorem returned_roots {E : Type} (x : Input E) (sv wv : Data)
    (post : PV_FN_THREAD_f124_ReturnedPost.Post x sv wv) :
    let p := PV_FN_THREAD_f124_StorePost.backing x sv wv
    let t := PV_FN_THREAD_f124_ReturnedPost.store x sv wv
    t.cells ⟨x.parent.activation,x.dest,[]⟩ = some (PV_FN_THREAD_f222_EntryOwned.root p) ∧
    At (PV_THR2_OwnInitExactReturnedCases.carrier x.C x.b) t p
      (PV_THR2_KeyValues.pack PV_THR2_Packet124Aggregate13.source.2.2.1 [sv,wv,x.ptr]) := by
  refine ⟨post.1,PV_THR2_KeyValues.pack PV_THR2_Packet124Aggregate13.source.2.2.1 [sv,wv,x.ptr],?_,?_⟩
  · change (PV_FN_THREAD_f124_ReturnedPost.store x sv wv).cells
      (PV_FN_THREAD_f124_StorePost.backing x sv wv) = _
    exact post.2.1
  · rfl

/-- At actual1916's returned branch, the provider's successful Post supplies
all pointee, age and OWNER facts needed by the named125 dependency at1989.
This is an INTERNAL branch join, not an f6 contract or original-interpreter
all-prefix transport. No124 instructions are executed in this proof. -/
theorem to125 (C : Carrier OWNER Data) (b : Bool) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (H : Backend PV_RJ4IDB.NativeEvent)
    (resources : Resources) (encode : Encode) (shape : PV_THR2_TypedRepresentation_ArcInner.Shape)
    (s : Store Data) (a : Nat) (parents : List Frame) (counter thread panicked capture sv wv : Data)
    (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config) (heap : Nat)
    (live : a < s.nextActivation)
    (thread_f125 : PV_FN_THREAD_f6ProviderInterfaces.f125
      (⟨PV_THR2_OwnInitExactReturnedCases.carrier C b,K,P,
        PV_THR2_OwnUniformResourceHandler.lift H⟩ : Machine PV_RJ4IDB.NativeEvent))
    (successful :
      let x := PV_FN_THREAD_f6Provider124Entry.convert C b K P H
        (PV_FN_THREAD_f6InterfaceSites.arcInput s a parents counter thread panicked w es stack)
        (PV_THR2_ScopeData.value counter thread panicked)
      PV_FN_THREAD_f124.Successful x H resources encode shape sv wv heap) :
    let x := PV_FN_THREAD_f6Provider124Entry.convert C b K P H
      (PV_FN_THREAD_f6InterfaceSites.arcInput s a parents counter thread panicked w es stack)
      (PV_THR2_ScopeData.value counter thread panicked)
    let p := PV_FN_THREAD_f124_StorePost.backing x sv wv
    let t := PV_FN_THREAD_f124_ReturnedPost.store x sv wv
    let y := PV_FN_THREAD_f124_ClosedLeak.input x H resources encode shape sv wv
    FullPost ⟨PV_THR2_OwnInitExactReturnedCases.carrier C b,K,P,
        PV_THR2_OwnUniformResourceHandler.lift H⟩
      (PV_FN_THREAD_f6InterfaceSites.catchInput t a parents
        (PV_FN_THREAD_f222_EntryOwned.root p) capture y.w y.es stack)
      (fun post _ result =>
        At (PV_THR2_OwnInitExactReturnedCases.carrier C b) post ⟨a,2,[0]⟩
          (PV_FN_THREAD_f222_EntryOwned.root p) ∧
        (∃ strong' weak', At (PV_THR2_OwnInitExactReturnedCases.carrier C b) post p
          (PV_THR2_KeyValues.pack PV_THR2_Packet124Aggregate13.source.2.2.1
            [strong',weak',PV_THR2_ScopeData.value counter thread panicked])) ∧
        (K.variant result = some 0 ∨ K.variant result = some 1)) := by
  dsimp only at successful ⊢
  let x := PV_FN_THREAD_f6Provider124Entry.convert C b K P H
    (PV_FN_THREAD_f6InterfaceSites.arcInput s a parents counter thread panicked w es stack)
    (PV_THR2_ScopeData.value counter thread panicked)
  have post := successful.2.1
  have roots := returned_roots x sv wv post
  have bounds := backing_bounds x sv wv (by change s.nextActivation+3 < s.nextActivation+4; omega)
  apply PV_FN_THREAD_f6ProviderCatchPre.at1989 C b K P
    (PV_THR2_OwnUniformResourceHandler.lift H) thread_f125
  · change a < s.nextActivation+6
    omega
  · exact bounds.2
  · exact successful.1.2.2
  · exact roots.2

#print axioms backing_bounds
#print axioms returned_roots
#print axioms to125
end PV_FN_THREAD_f6Provider124Returned
