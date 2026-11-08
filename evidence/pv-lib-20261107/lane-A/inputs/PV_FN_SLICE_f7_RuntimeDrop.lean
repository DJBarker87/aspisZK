import PV_FN_SLICE_RuntimeBindings
import PV_FN_SLICE_f7_TypedDrop
import PV_FN_SLICE_f7_HandlerSpec
import PV_FN_SLICE_f7_Joins
set_option autoImplicit false
noncomputable section
namespace PV_FN_SLICE_f7_RuntimeDrop
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
abbrev Input := PV_FN_THREAD_f315.Input PV_RJ4IDB.NativeEvent

def cut (x : Input) (capture : Data) : PV_FN_SLICE_f7_Drop.Cut :=
  ⟨x.C,x.s,x.a,x.parent :: x.parents,x.w,capture⟩
def projection (x : Input) : Address → Option Data :=
  PV_FN_SLICE_f22_TypedDestructor.sourceProjection x.s x.s.nextActivation

/-- The f22-derived source projection instantiates the unchanged CLOSED W5
contract at the actual f7 Drop. No per-call identity delta is assumed. -/
theorem provider (x : Input) (capture : Data)
    (spec : PV_FN_SLICE_RuntimeBindings.DropSemantics x.H)
    (pre : PV_W1_OwnerWellFormed.OwnerWellFormed x.w x.s.nextActivation) :
    ∃ H : PV_W5_NativeFrame.Backend,
      PV_FN_SLICE_f7_Drop.Summary (cut x capture) H (projection x) ∧
      x.H (.drop PV_FN_SLICE_f7_Drop.source capture) x.w =
        PV_FN_SLICE_f7_Drop.reply (cut x capture) H ∧
      PV_FN_SLICE_f7_Drop.effects (cut x capture) (projection x) = x.s ∧
      PV_W1_OwnerWellFormed.OwnerWellFormed
        (x.H (.drop PV_FN_SLICE_f7_Drop.source capture) x.w).world x.s.nextActivation := by
  obtain ⟨H,agree⟩ := spec
  have summary := PV_FN_SLICE_f7_Drop.contract (cut x capture) H (projection x) pre
  have reply : x.H (.drop PV_FN_SLICE_f7_Drop.source capture) x.w =
      PV_FN_SLICE_f7_Drop.reply (cut x capture) H := agree _ _ _
  have owner : PV_W1_OwnerWellFormed.OwnerWellFormed
      (x.H (.drop PV_FN_SLICE_f7_Drop.source capture) x.w).world x.s.nextActivation := by
    rw [reply]
    exact summary.2.2.1
  have same := PV_FN_SLICE_f22_TypedDestructor.w5_projection_identity
    (cut x capture) x.s.nextActivation
  exact ⟨H,summary,reply,same,owner⟩

/-- The actual Drop and entire f7 suffix, retaining every native answer.
LOCAL0 is preserved because the typed destructor writes no caller cell. -/
theorem run (x : Input) (capture : Data)
    (spec : PV_FN_SLICE_RuntimeBindings.DropSemantics x.H)
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

#print axioms provider
#print axioms run
end PV_FN_SLICE_f7_RuntimeDrop
