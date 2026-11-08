import PV_FN_THREAD_f6Provider124Returned
set_option autoImplicit false
noncomputable section
namespace PV_FN_THREAD_f6Provider124Continuation
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_FN_THREAD_f6Interfaces
open PV_FN_THREAD_f124_BoxContract

/-- The actual provider frame, not a guessed read-only consumer interface,
preserves f6's saved callback while returning the Arc at LOCAL3. -/
theorem capture_frame {E : Type} (x : Input E) (sv wv : Data)
    (post : PV_FN_THREAD_f124_ReturnedPost.Post x sv wv)
    (older : x.parent.activation < x.a) (fresh : x.a < x.s.nextActivation)
    (destination : x.dest ≠ 1) :
    (PV_FN_THREAD_f124_ReturnedPost.store x sv wv).cells ⟨x.parent.activation,1,[]⟩ =
      x.s.cells ⟨x.parent.activation,1,[]⟩ := by
  apply post.2.2.1
  · exact Nat.ne_of_lt older
  · intro i bound
    change x.parent.activation ≠ x.s.nextActivation+i
    omega
  · intro eq
    have bad := congrArg Address.localIndex eq
    exact destination bad.symm

/-- f6's own20 instructions run on the exact provider Post store under ANY
original resolver and full native handler. No124 instruction, final-store
construction or native answer is replayed or substituted. The entry capture
and saved-parent shape are internal projections supplied by the caller prefix.
This lemma alone does not identify the provider's interpreter with the original. -/
theorem run {E : Type} (x : Input E) (sv wv capture : Data)
    (post : PV_FN_THREAD_f124_ReturnedPost.Post x sv wv)
    (older : x.parent.activation < x.a) (fresh : x.a < x.s.nextActivation)
    (destination : x.dest = 3)
    (parent_shape : {x.parent with waiting := none} =
      ({activation := x.parent.activation,remaining := PV_THR2_F6.live.body.drop 26} : Frame))
    (entry_capture : x.s.cells ⟨x.parent.activation,1,[]⟩ = some capture)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (w : OWNER) (es : List E) :
    let t := PV_FN_THREAD_f124_ReturnedPost.store x sv wv
    let p := PV_FN_THREAD_f124_StorePost.backing x sv wv
    PV_THR2_IntrinsicState.advance (PV_THR2_OwnInitExactReturnedCases.carrier x.C x.b)
      x.K P H 20
      ⟨⟨.running ⟨{x.parent with waiting := none},x.parents,t⟩,w,es⟩,x.stack⟩ =
      ⟨⟨.running (PV_FN_THREAD_f6OwnContinuation.pending t x.parent.activation x.parents
        (PV_FN_THREAD_f222_EntryOwned.root p) capture),w,es⟩,x.stack⟩ := by
  dsimp only
  rw [parent_shape]
  have arc := (PV_FN_THREAD_f6Provider124Returned.returned_roots x sv wv post).1
  rw [destination] at arc
  have callback := (capture_frame x sv wv post older fresh (by rw [destination]; decide)).trans entry_capture
  exact PV_FN_THREAD_f6OwnContinuation.run
    (PV_THR2_ThreadFields.carrier (PV_THR2_ScopeLiterals.carrier (PV_THR2_RangeLiterals.carrier x.C)))
    x.K P H _ x.parent.activation x.parents x.b _ capture w es x.stack arc callback

/-- The parent shape required above is derived at the actual1916 source call,
not an additional f6 or endpoint precondition. -/
theorem actual_parent (C : Carrier OWNER Data) (b : Bool) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (H : Backend PV_RJ4IDB.NativeEvent)
    (s : Store Data) (a : Nat) (parents : List Frame) (counter thread panicked : Data)
    (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config) :
    let x := PV_FN_THREAD_f6Provider124Entry.convert C b K P H
      (PV_FN_THREAD_f6InterfaceSites.arcInput s a parents counter thread panicked w es stack)
      (PV_THR2_ScopeData.value counter thread panicked)
    {x.parent with waiting := none} =
      ({activation := a,remaining := PV_THR2_F6.live.body.drop 26} : Frame) := rfl

#print axioms capture_frame
#print axioms run
#print axioms actual_parent
end PV_FN_THREAD_f6Provider124Continuation
