import PV_FN_THREAD_f6Provider124Continuation
import PV_FN_THREAD_f6CatchRequest
set_option autoImplicit false
noncomputable section
namespace PV_FN_THREAD_f6Provider124ActualContinuation
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_FN_THREAD_f6Interfaces
open PV_FN_THREAD_f124_BoxContract

/-- Derive the callback read at the actual1916 entry from f6's original entry
cell and own-source frame. No future callback read is assumed. -/
theorem entry_capture {E : Type} (s : Store Data) (a : Nat) (parents : List Frame)
    (counter thread panicked : Data) (w : OWNER) (es : List E) (stack : List Config)
    (live : a < s.nextActivation) :
    (PV_FN_THREAD_f6InterfaceSites.arcInput s a parents counter thread panicked w es stack).store.cells
      ⟨a,1,[]⟩ = s.cells ⟨a,1,[]⟩ := by
  rw [(PV_FN_THREAD_f6InterfaceSites.arc_site s a parents counter thread panicked w es stack).2.2.1]
  exact PV_FN_THREAD_f6CatchRequest.entry_capture s a parents counter thread panicked live

/-- Actual1916 return to1989 on the exact provider store. All callback and
parent facts are derived from original entry and source issuance. The original
resolver/handler are arbitrary on these20 OWN instructions; no124 internals
are executed. Joining the preceding body run still needs its original-prefix
transport, so this is not the f6 closure. -/
theorem own20 (C : Carrier OWNER Data) (b : Bool) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (H : Backend PV_RJ4IDB.NativeEvent)
    (s : Store Data) (a : Nat) (parents : List Frame) (counter thread panicked capture sv wv : Data)
    (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config)
    (live : a < s.nextActivation) (callback : s.cells ⟨a,1,[]⟩ = some capture)
    (post :
      let x := PV_FN_THREAD_f6Provider124Entry.convert C b K P H
        (PV_FN_THREAD_f6InterfaceSites.arcInput s a parents counter thread panicked w es stack)
        (PV_THR2_ScopeData.value counter thread panicked)
      PV_FN_THREAD_f124_ReturnedPost.Post x sv wv)
    (originalP : Data → Option PV_STX2_SliceSyntax.Program)
    (originalH : PV_STX2_Native.Request Data → OWNER → Reply OWNER PV_RJ4IDB.NativeEvent Data)
    (postWorld : OWNER) (postEvents : List PV_RJ4IDB.NativeEvent) :
    let x := PV_FN_THREAD_f6Provider124Entry.convert C b K P H
      (PV_FN_THREAD_f6InterfaceSites.arcInput s a parents counter thread panicked w es stack)
      (PV_THR2_ScopeData.value counter thread panicked)
    let t := PV_FN_THREAD_f124_ReturnedPost.store x sv wv
    let p := PV_FN_THREAD_f124_StorePost.backing x sv wv
    PV_THR2_IntrinsicState.advance (PV_THR2_OwnInitExactReturnedCases.carrier C b) K originalP originalH 20
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F6.live.body.drop 26},parents,t⟩,
        postWorld,postEvents⟩,stack⟩ =
      ⟨⟨.running (PV_FN_THREAD_f6OwnContinuation.pending t a parents
        (PV_FN_THREAD_f222_EntryOwned.root p) capture),postWorld,postEvents⟩,stack⟩ := by
  let x := PV_FN_THREAD_f6Provider124Entry.convert C b K P H
    (PV_FN_THREAD_f6InterfaceSites.arcInput s a parents counter thread panicked w es stack)
    (PV_THR2_ScopeData.value counter thread panicked)
  have shape := PV_FN_THREAD_f6Provider124Continuation.actual_parent C b K P H
    s a parents counter thread panicked w es stack
  have continued := PV_FN_THREAD_f6Provider124Continuation.run x sv wv capture post
    (by change a < s.nextActivation+3; omega)
    (by change s.nextActivation+3 < s.nextActivation+4; omega) rfl shape
    ((entry_capture s a parents counter thread panicked w es stack live).trans callback)
    originalP originalH postWorld postEvents
  rw [shape] at continued
  exact continued

#print axioms entry_capture
#print axioms own20
end PV_FN_THREAD_f6Provider124ActualContinuation
