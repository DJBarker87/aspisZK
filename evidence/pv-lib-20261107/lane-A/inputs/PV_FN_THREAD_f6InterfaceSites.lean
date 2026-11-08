import PV_FN_THREAD_f6Interfaces
import PV_FN_THREAD_f6ScopeData
import PV_FN_THREAD_f6OwnContinuation
import PV_FN_THREAD_f6FinalDerefRequest
set_option autoImplicit false
noncomputable section
namespace PV_FN_THREAD_f6InterfaceSites
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_FN_THREAD_f6Interfaces

/-- A single SOURCE-issued argument, not a replacement call resolver. -/
def one {E : Type} (s : Store Data) (a : Nat) (parents : List Frame)
    (loops : List LoopFrame) (rest : List PV_STX2_SliceSyntax.Node)
    (fn value : Data) (dest : Nat) (body : PV_STX2_SliceSyntax.Program)
    (w : OWNER) (es : List E) (stack : List Config) : Entry E :=
  let c := PV_THR2_IntrinsicFrameEnter.pending s a parents loops rest fn [value] dest
  {activation := s.nextActivation,body := body,store := c.store,parent := c.frame,
   parents := parents,wait := PV_THR2_StaticReply.wait s fn [value] dest,dest := dest,
   args := [value],world := w,events := es,suspended := stack}

/-- Argument binding discharges entry validity at a fresh activation. The OWNER
fact is the previous callee's Post, not a new f6 Pre or a future-state read. -/
theorem one_valid {E : Type} (s : Store Data) (a : Nat) (parents : List Frame)
    (loops : List LoopFrame) (rest : List PV_STX2_SliceSyntax.Node)
    (fn value : Data) (dest : Nat) (body : PV_STX2_SliceSyntax.Program)
    (w : OWNER) (es : List E) (stack : List Config)
    (live : a < s.nextActivation) (owner : OwnerWellFormed w s.nextActivation) :
    EntryValid (one s a parents loops rest fn value dest body w es stack) := by
  refine ⟨rfl,live,rfl,rfl,⟨fn,rfl⟩,owner,?_⟩
  intro i v selected
  cases i with
  | zero =>
    have equal : value = v := by simpa only [one,List.getElem?_cons_zero,Option.some.injEq] using selected
    subst v
    simp [one,PV_THR2_IntrinsicFrameEnter.pending,PV_THR2_StaticCall.issued,
      PV_STX2_Native.arguments,write]
  | succ i => simp [one] at selected

/-- Exactly the original interpreter's one structured-call entry transition.
The actual resolver is an equation to the retained body, never switched to a
summary resolver. This theorem does not assume the body finishes. -/
theorem one_enter {E : Type} (M : Machine E) (s : Store Data) (a : Nat)
    (parents : List Frame) (loops : List LoopFrame) (rest : List PV_STX2_SliceSyntax.Node)
    (fn value : Data) (dest : Nat) (body : PV_STX2_SliceSyntax.Program)
    (w : OWNER) (es : List E) (stack : List Config)
    (ordinary : PV_THR2_Catch316Segment.select
      (PV_THR2_IntrinsicFrameEnter.pending s a parents loops rest fn [value] dest) = none)
    (resolved : M.programs fn = some body) :
    PV_THR2_IntrinsicState.advance M.carrier M.control M.programs M.handler 1
      ⟨⟨.running (PV_THR2_IntrinsicFrameEnter.pending s a parents loops rest fn [value] dest),w,es⟩,stack⟩ =
      entry (one s a parents loops rest fn value dest body w es stack) := by
  exact PV_THR2_IntrinsicFrameEnter.run M.carrier M.control M.programs M.handler
    s a parents loops rest fn [value] dest body w es stack ordinary resolved

/-- The actual1916 input. The same source aggregate and three original native
constructor replies appear here; no f124 internal store or prefix is imported. -/
def arcInput {E : Type} (s : Store Data) (a : Nat) (parents : List Frame)
    (counter thread panicked : Data) (w : OWNER) (es : List E) (stack : List Config) : Entry E :=
  let t := PV_FN_THREAD_f6ConstructorRun.third
    (PV_FN_THREAD_f6ConstructorRun.second (PV_FN_THREAD_f6ConstructorRun.first s a counter) a thread) a panicked
  one (PV_THR2_ScopeArcCall.before (PV_THR2_ScopeData.prepared t a counter thread panicked) a)
    a parents [] (PV_THR2_F6.live.body.drop 26) PV_THR2_ScopeArcCall.fn
    (PV_THR2_ScopeData.value counter thread panicked) 3 PV_THR2_F124.live w es stack

/-- Parent and issued store agree with the proved f6 own segment's exact
frontier at1916. This is a definitional source-call identification. -/
theorem arc_site {E : Type} (s : Store Data) (a : Nat) (parents : List Frame)
    (counter thread panicked : Data) (w : OWNER) (es : List E) (stack : List Config) :
    let x := arcInput s a parents counter thread panicked w es stack
    let c := PV_FN_THREAD_f6ScopeData.pending s a parents counter thread panicked
    x.parent = c.frame ∧ x.parents = c.callers ∧ x.store = c.store ∧
      x.activation = s.nextActivation + 3 := ⟨rfl,rfl,rfl,rfl⟩

/-- The fresh activation and argument clauses are DERIVED at1916. Only the
preceding leaf world's invariant is required as an internal Post projection. -/
theorem arc_valid {E : Type} (s : Store Data) (a : Nat) (parents : List Frame)
    (counter thread panicked : Data) (w : OWNER) (es : List E) (stack : List Config)
    (live : a < s.nextActivation) (owner : OwnerWellFormed w (s.nextActivation+3)) :
    EntryValid (arcInput s a parents counter thread panicked w es stack) := by
  apply one_valid
  · change a < s.nextActivation + 3
    exact Nat.lt_of_lt_of_le live (Nat.le_add_right _ _)
  · exact owner

/-- The named full124 dependency is instantiated with ScopeData at its ACTUAL
source1916 arguments. The result is a prefix/return/frame contract on the
original interpreter, with arbitrary native answer branches retained. -/
theorem at1916 {E : Type} (M : Machine E) (thread_f124 : f124 M)
    (s : Store Data) (a : Nat) (parents : List Frame) (counter thread panicked : Data)
    (w : OWNER) (es : List E) (stack : List Config)
    (live : a < s.nextActivation) (owner : OwnerWellFormed w (s.nextActivation+3)) :
    let x := arcInput s a parents counter thread panicked w es stack
    FullPost M x (fun post _ arc => NewArcAt M.carrier post x.activation arc
      (PV_THR2_ScopeData.value counter thread panicked) ∧ ReadOnlyFrame x post) := by
  exact thread_f124 _ _ rfl rfl (arc_valid s a parents counter thread panicked w es stack live owner)

/-- Actual1989 saved caller and source capture wrapper, on an explicit124
Post store. Its entry facts must be obtained from at1916 and the own segment. -/
def catchInput {E : Type} (t : Store Data) (a : Nat) (parents : List Frame)
    (arc capture : Data) (w : OWNER) (es : List E) (stack : List Config) : Entry E :=
  one (write (PV_FN_THREAD_f6OwnContinuation.prepared t a arc capture) ⟨a,11,[]⟩ none)
    a parents [] (PV_THR2_F6.live.body.drop 46) PV_THR2_ScopeCatchCall.descriptor.2
    (PV_THR2_ScopeCaptureWrap.value a capture) 10 PV_THR2_F125.live w es stack

theorem catch_site {E : Type} (t : Store Data) (a : Nat) (parents : List Frame)
    (arc capture : Data) (w : OWNER) (es : List E) (stack : List Config) :
    let x := catchInput t a parents arc capture w es stack
    let c := PV_FN_THREAD_f6OwnContinuation.pending t a parents arc capture
    x.parent = c.frame ∧ x.parents = c.callers ∧ x.store = c.store := ⟨rfl,rfl,rfl⟩

/-- Named125 instantiation at1989. ScopeAt/ArcAt are internal preceding-Post
projections; they are NOT additional hypotheses of PV_FN_THREAD_f6.Pre. -/
theorem at1989 {E : Type} (M : Machine E) (thread_f125 : f125 M)
    (t : Store Data) (a : Nat) (parents : List Frame) (arc capture payload : Data)
    (w : OWNER) (es : List E) (stack : List Config)
    (valid : EntryValid (catchInput t a parents arc capture w es stack))
    (scopeAt : At M.carrier (catchInput t a parents arc capture w es stack).store ⟨a,2,[0]⟩ arc)
    (arcAt : ArcAt M.carrier (catchInput t a parents arc capture w es stack).store arc payload) :
    let x := catchInput t a parents arc capture w es stack
    FullPost M x (fun post _ result => At M.carrier post ⟨a,2,[0]⟩ arc ∧
      ArcAt M.carrier post arc payload ∧
      (M.control.variant result = some 0 ∨ M.control.variant result = some 1)) := by
  exact thread_f125 _ a capture arc payload rfl rfl valid scopeAt arcAt

#print axioms one_valid
#print axioms one_enter
#print axioms arc_site
#print axioms arc_valid
#print axioms at1916
#print axioms catch_site
#print axioms at1989
end PV_FN_THREAD_f6InterfaceSites
