import PV_FN_SLICE_f22_TypedDestructor
import PV_FN_SLICE_f7_HandlerSpec
import PV_FN_SLICE_f7_Joins
set_option autoImplicit false
noncomputable section
namespace PV_FN_SLICE_f7_TypedDrop
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
abbrev Input := PV_FN_THREAD_f315.Input PV_RJ4IDB.NativeEvent

def cut (x : Input) (capture : Data) : PV_FN_SLICE_f7_Drop.Cut :=
  ⟨x.C,x.s,x.a,x.parent :: x.parents,x.w,capture⟩
def projection (x : Input) : Address → Option Data :=
  PV_FN_SLICE_f22_TypedDestructor.sourceProjection x.s x.s.nextActivation

/-- The f22-derived source projection instantiates the unchanged CLOSED W5
contract at the actual f7 Drop. No per-call identity delta is assumed. -/
theorem provider (x : Input) (capture : Data)
    (spec : PV_FN_SLICE_f7_HandlerSpec.Spec x.H)
    (pre : PV_W1_OwnerWellFormed.OwnerWellFormed x.w x.s.nextActivation) :
    ∃ H : PV_W5_NativeFrame.Backend,
      PV_FN_SLICE_f7_Drop.Summary (cut x capture) H (projection x) ∧
      x.H (.drop PV_FN_SLICE_f7_Drop.source capture) x.w =
        PV_FN_SLICE_f7_Drop.reply (cut x capture) H ∧
      PV_FN_SLICE_f7_Drop.effects (cut x capture) (projection x) = x.s ∧
      PV_W1_OwnerWellFormed.OwnerWellFormed
        (x.H (.drop PV_FN_SLICE_f7_Drop.source capture) x.w).world x.s.nextActivation := by
  obtain ⟨H,summary,reply,owner⟩ := PV_FN_SLICE_f7_HandlerSpec.at_source178
    x.H spec (cut x capture) (projection x) pre
  have same := PV_FN_SLICE_f22_TypedDestructor.w5_projection_identity
    (cut x capture) x.s.nextActivation
  exact ⟨H,summary,reply,same,owner⟩

/-- The actual Drop and entire f7 suffix, retaining every native answer.
LOCAL0 is preserved because the typed destructor writes no caller cell. -/
theorem run (x : Input) (capture : Data)
    (spec : PV_FN_SLICE_f7_HandlerSpec.Spec x.H)
    (cell : x.s.cells ⟨x.a,1,[]⟩ = some capture)
    (value : x.s.cells ⟨x.a,0,[]⟩ = some x.ptr)
    (saved : x.parent.waiting = some x.wait)
    (action : x.wait.action = .child x.a (.local x.dest))
    (pre : PV_W1_OwnerWellFormed.OwnerWellFormed x.w x.s.nextActivation) :
    let r := x.H (.drop PV_FN_SLICE_f7_AfterDrop.source.1 capture) x.w
    PV_THR2_IntrinsicState.advance (PV_FN_SLICE_ValueCarrier.carrier x.C) x.K x.P x.H
      (1+1+PV_FN_SLICE_f7_AfterDrop.steps r)
      ⟨⟨.running ⟨{activation := x.a,remaining := PV_STX2_SliceF7.program.body.drop 4},
        x.parent :: x.parents,x.s⟩,x.w,x.es⟩,x.stack⟩ =
      PV_FN_SLICE_f7_AfterDrop.finish x capture r := by
  have owner := (provider x capture spec pre).choose_spec.2.2.2
  apply PV_FN_SLICE_f7_Joins.dropComposition x capture cell saved action
  cases h : (x.H (.drop PV_FN_SLICE_f7_AfterDrop.source.1 capture) x.w).answer with
  | returned result => cases result <;> simp only [h]; exact ⟨value,owner⟩
  | fault f => trivial
  | pending => trivial

/-- Frame through Drop and its suffix, independent of the conservative
argument-reachability relation. This starts at the post-f8 store. -/
theorem frame (x : Input) (capture : Data) (r : Reply OWNER PV_RJ4IDB.NativeEvent Data)
    (p : Address) (own : p.activation ≠ x.a)
    (dest : p ≠ ⟨x.parent.activation,x.dest,[]⟩) :
    (PV_FN_SLICE_f8.store (PV_FN_SLICE_f7_AfterDrop.finish x capture r)).cells p = x.s.cells p := by
  have different : p ≠ (⟨x.a,1,[]⟩ : Address) := fun h => own (congrArg Address.activation h)
  cases r with
  | mk answer w events =>
    cases answer with
    | pending => rfl
    | fault f => cases f <;> rfl
    | returned result =>
      cases result with
      | ok v =>
        exact (PV_FN_SLICE_f7_Suffix.frame
          (PV_FN_SLICE_f7_AfterDrop.suffix x ⟨.returned (.ok v),w,events⟩) p own dest).trans
          (if_neg different)
      | fail e =>
        cases hp : x.parents <;>
          simp [PV_FN_SLICE_f8.store,PV_FN_SLICE_f7_AfterDrop.finish,
          PV_THR2_ChildBoundary.delivered,PV_STX2_Pinned.reply,PV_STX2_Pinned.eraseReply,
          PV_STX2_Native.reply,native,adopt,PV_W1_LeafBoundary.statusStore,hp]
      | div =>
        cases hp : x.parents <;>
          simp [PV_FN_SLICE_f8.store,PV_FN_SLICE_f7_AfterDrop.finish,
          PV_THR2_ChildBoundary.delivered,PV_STX2_Pinned.reply,PV_STX2_Pinned.eraseReply,
          PV_STX2_Native.reply,native,adopt,PV_W1_LeafBoundary.statusStore,hp]
#print axioms provider
#print axioms run
#print axioms frame
end PV_FN_SLICE_f7_TypedDrop
