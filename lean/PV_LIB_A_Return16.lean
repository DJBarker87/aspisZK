import PV_LIB_A_ContextSource16
import PV_THR2_SourceReturn
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_Return16
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Execution Issued Context)
open PV_LIB_SPEC_F1Arithmetic14 (stage)

def complete (s : Store Data) (a : Nat) (parent : Frame) (parents : List Frame)
    (site : Site) (value : Data) (w : OWNER) (es : List Event)
    (issued : List Issued) (consumed : List Context) : Execution :=
  ⟨⟨⟨.running ⟨{activation := a,remaining := [.leaf (.ret site (.local 0))],completed := some (.ok value)},parent::parents,s⟩,w,es⟩,[]⟩,issued,consumed⟩

theorem source (p : Parameters) (H : Handler) (s : Store Data) (a : Nat)
    (parent : Frame) (parents : List Frame) (site : Site) (value : Data)
    (w : OWNER) (es : List Event) (issued : List Issued) (consumed : List Context)
    (cell : s.cells ⟨a,0,[]⟩ = some value) :
    PV_LIB_SPEC_SourceTransport15.sourceStep p H
      (stage s a (parent::parents) [.leaf (.ret site (.local 0))] w es issued consumed) =
      complete s a parent parents site value w es issued consumed := by
  unfold PV_LIB_SPEC_SourceTransport15.sourceStep stage PV_THR2_IntrinsicState.step
  simp only [PV_THR2_Catch316Segment.select]
  rw [PV_THR2_SourceReturn.source _ _ _ _ _ _ _ _ _ _ cell]
  simp [complete,PV_LIB_SPEC_ControlRuntime.recordIssue,PV_LIB_SPEC_ControlRuntime.issuing]

def delivered (s : Store Data) (a dest : Nat) (parent : Frame) (parents : List Frame)
    (value : Data) (w : OWNER) (es : List Event)
    (issued : List Issued) (consumed : List Context) : Execution :=
  ⟨⟨⟨.running ⟨{parent with waiting := none},parents,
    write (write s ⟨a,0,[]⟩ (some value)) ⟨parent.activation,dest,[]⟩ (some value)⟩,w,es⟩,[]⟩,issued,consumed⟩

theorem parent (p : Parameters) (H : Handler) (s : Store Data) (a dest : Nat)
    (saved : Frame) (parents : List Frame) (site : Site) (wait : PV_STX2_Native.Waiting Data)
    (value : Data) (w : OWNER) (es : List Event) (issued : List Issued) (consumed : List Context)
    (waiting : saved.waiting = some wait) (action : wait.action = .child a (.local dest)) :
    PV_LIB_SPEC_SourceTransport15.sourceStep p H
      (complete s a saved parents site value w es issued consumed) =
      delivered s a dest saved parents value w es issued consumed := by
  unfold PV_LIB_SPEC_SourceTransport15.sourceStep complete PV_THR2_IntrinsicState.step
  simp only [PV_THR2_Catch316Segment.select]
  rw [PV_THR2_SourceReturn.parent _ _ _ _ _ _ _ _ _ _ _ _ _ waiting action]
  simp [delivered,PV_LIB_SPEC_ControlRuntime.recordIssue,PV_LIB_SPEC_ControlRuntime.issuing]

theorem run (cut : PV_LIB_SPEC_ReachedNative14.Cut) (p : Parameters) (H : Handler)
    (s : Store Data) (a dest : Nat) (saved : Frame) (parents : List Frame)
    (site : Site) (wait : PV_STX2_Native.Waiting Data) (value : Data)
    (w : OWNER) (es : List Event) (issued : List Issued) (consumed : List Context)
    (cell : s.cells ⟨a,0,[]⟩ = some value)
    (waiting : saved.waiting = some wait) (action : wait.action = .child a (.local dest)) :
    PV_LIB_SPEC_ReachedNative14.run cut p 2
      (stage s a (saved::parents) [.leaf (.ret site (.local 0))] w es issued consumed) =
      delivered s a dest saved parents value w es issued consumed := by
  let x := stage s a (saved::parents) [.leaf (.ret site (.local 0))] w es issued consumed
  have q1 : PV_LIB_SPEC_SourceTransport15.Quiet x.state := by
    refine ⟨?_,?_⟩
    · intro c hc; cases hc; rfl
    · intro c hc; cases hc; exact ⟨rfl,rfl,True.intro⟩
  have q2 : PV_LIB_SPEC_SourceTransport15.Quiet
      (complete s a saved parents site value w es issued consumed).state := by
    refine ⟨?_,?_⟩
    · intro c hc; cases hc; rfl
    · intro c hc; cases hc; exact ⟨rfl,rfl,True.intro⟩
  have trace : PV_LIB_SPEC_SourceTransport15.Trace cut p H 2 x := by
    refine ⟨rfl,q1,?_,?_⟩
    · intro c; exact PV_LIB_SPEC_SourceProjection15.no_wait _ _ _ (by intro frame eq; cases eq; rfl)
    · rw [show PV_LIB_SPEC_SourceTransport15.sourceStep p H x = _ from source p H s a saved parents site value w es issued consumed cell]
      refine ⟨rfl,q2,?_,True.intro⟩
      intro c; exact PV_LIB_SPEC_SourceProjection15.no_wait _ _ _ (by intro frame eq; cases eq; rfl)
  rw [PV_LIB_SPEC_SourceTransport15.run cut p H 2 x trace]
  simp only [PV_LIB_SPEC_SourceTransport15.advance]
  rw [source p H s a saved parents site value w es issued consumed cell,
    parent p H s a dest saved parents site wait value w es issued consumed waiting action]

#print axioms source
#print axioms parent
#print axioms run
end PV_LIB_A_Return16
