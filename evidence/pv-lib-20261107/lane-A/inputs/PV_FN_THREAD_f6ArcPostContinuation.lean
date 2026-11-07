import PV_FN_THREAD_f6InterfaceSites
set_option autoImplicit false
noncomputable section
namespace PV_FN_THREAD_f6ArcPostContinuation
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_FN_THREAD_f6Interfaces PV_FN_THREAD_f6InterfaceSites

/-- f6's own constructor/aggregate/call-issuance stores preserve LOCAL1.
No124 body, allocation or internal store is unfolded. -/
theorem entry_capture {E : Type} (s : Store Data) (a : Nat) (parents : List Frame)
    (counter thread panicked : Data) (w : OWNER) (es : List E) (stack : List Config)
    (live : a < s.nextActivation) :
    (arcInput s a parents counter thread panicked w es stack).store.cells ⟨a,1,[]⟩ =
      s.cells ⟨a,1,[]⟩ := by
  have neq (k i : Nat) : (⟨a,1,[]⟩ : Address) ≠ ⟨s.nextActivation+k,i,[]⟩ := by
    intro h
    exact (Nat.ne_of_lt (Nat.lt_of_lt_of_le live (Nat.le_add_right _ _)))
      (congrArg Address.activation h)
  have neq0 (i : Nat) : (⟨a,1,[]⟩ : Address) ≠ ⟨s.nextActivation,i,[]⟩ := neq 0 i
  simp [arcInput,one,PV_THR2_IntrinsicFrameEnter.pending,
    PV_THR2_ScopeArcCall.before,PV_THR2_ScopeData.prepared,
    PV_FN_THREAD_f6ConstructorRun.first,PV_FN_THREAD_f6ConstructorRun.second,
    PV_FN_THREAD_f6ConstructorRun.third,PV_THR2_ScopePrologue.prepared,
    PV_THR2_StaticCall.issued,PV_THR2_StaticReply.returnedStore,
    PV_STX2_Native.arguments,write,neq,neq0,Nat.add_assoc]

/-- Specialize124's full Post at its ACTUAL first returned configuration.
The caller capture is derived from the callee's named read-only frame; no
capture-at-future-state premise is introduced. Nonreturned branches remain
covered by at1916 and are not prerequisites of this returned-case lemma. -/
theorem projections {E : Type} (M : Machine E) (thread_f124 : f124 M)
    (s : Store Data) (a : Nat) (parents : List Frame) (counter thread panicked capture : Data)
    (w : OWNER) (es : List E) (stack : List Config) (n : Nat) (post : Store Data) (arc : Data)
    (live : a < s.nextActivation) (owner : OwnerWellFormed w (s.nextActivation+3))
    (captured : s.cells ⟨a,1,[]⟩ = some capture)
    (before : BeforeReturn M (arcInput s a parents counter thread panicked w es stack) n)
    (returned : (run M (arcInput s a parents counter thread panicked w es stack) n).current.status =
      .running ⟨{(arcInput s a parents counter thread panicked w es stack).parent with waiting := none},
        parents,post⟩)
    (suspended : (run M (arcInput s a parents counter thread panicked w es stack) n).suspended = stack)
    (destination : post.cells ⟨a,3,[]⟩ = some arc) :
    NewArcAt M.carrier post (s.nextActivation+3) arc (PV_THR2_ScopeData.value counter thread panicked) ∧
      post.cells ⟨a,1,[]⟩ = some capture := by
  let x := arcInput s a parents counter thread panicked w es stack
  have all := at1916 M thread_f124 s a parents counter thread panicked w es stack live owner
  have atReturn := all n before
  dsimp only at atReturn
  rw [returned] at atReturn
  rcases atReturn with ⟨defined,frame,ownerFrame,ownerPost,events,completed,restored⟩
  have success := restored arc
    ⟨{x.parent with waiting := none},parents,post⟩ rfl rfl rfl destination suspended
  have old : a < x.activation := by
    change a < s.nextActivation+3
    exact Nat.lt_of_lt_of_le live (Nat.le_add_right _ _)
  have captureFrame := success.2 (⟨a,1,[]⟩ : Address) old (by
    intro h
    have bad := congrArg Address.localIndex h
    cases bad)
  refine ⟨success.1,?_⟩
  change post.cells ⟨a,1,[]⟩ = (arcInput s a parents counter thread panicked w es stack).store.cells ⟨a,1,[]⟩ at captureFrame
  exact captureFrame.trans ((entry_capture s a parents counter thread panicked w es stack live).trans captured)

/-- The next20 source transitions reuse the proved own segment BY NAME, on
124's EXPLICIT final store. This is a returned-case composition fragment;
loop, terminal branches and complete f6 assembly are still separate. -/
theorem own_to1989 {E : Type} (base : Carrier OWNER Data) (b : Bool) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (thread_f124 : f124 (⟨PV_THR2_EntryDynamic.carrier base b,K,P,H⟩ : Machine E))
    (s : Store Data) (a : Nat) (parents : List Frame) (counter thread panicked capture : Data)
    (w : OWNER) (es : List E) (stack : List Config) (n : Nat) (post : Store Data) (arc : Data)
    (live : a < s.nextActivation) (owner : OwnerWellFormed w (s.nextActivation+3))
    (captured : s.cells ⟨a,1,[]⟩ = some capture)
    (before : BeforeReturn ⟨PV_THR2_EntryDynamic.carrier base b,K,P,H⟩
      (arcInput s a parents counter thread panicked w es stack) n)
    (returned : (run ⟨PV_THR2_EntryDynamic.carrier base b,K,P,H⟩
      (arcInput s a parents counter thread panicked w es stack) n).current.status =
      .running ⟨{(arcInput s a parents counter thread panicked w es stack).parent with waiting := none},
        parents,post⟩)
    (suspended : (run ⟨PV_THR2_EntryDynamic.carrier base b,K,P,H⟩
      (arcInput s a parents counter thread panicked w es stack) n).suspended = stack)
    (destination : post.cells ⟨a,3,[]⟩ = some arc) (w' : OWNER) (es' : List E) :
    PV_THR2_IntrinsicState.advance (PV_THR2_EntryDynamic.carrier base b) K P H 20
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F6.live.body.drop 26},parents,post⟩,w',es'⟩,stack⟩ =
      ⟨⟨.running (PV_FN_THREAD_f6OwnContinuation.pending post a parents arc capture),w',es'⟩,stack⟩ := by
  have props := projections ⟨PV_THR2_EntryDynamic.carrier base b,K,P,H⟩ thread_f124
    s a parents counter thread panicked capture w es stack n post arc live owner captured
    before returned suspended destination
  exact PV_FN_THREAD_f6OwnContinuation.run base K P H post a parents b arc capture
    w' es' stack destination props.2

#print axioms entry_capture
#print axioms projections
#print axioms own_to1989
end PV_FN_THREAD_f6ArcPostContinuation
