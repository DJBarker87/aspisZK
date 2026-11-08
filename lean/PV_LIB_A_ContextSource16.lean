import PV_LIB_SPEC_LaneAJoins18
import PV_LIB_A_C18_A_SourceSequence13
import PV_LIB_A_C18_A_V2Neutral14
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_ContextSource16
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Execution Issued Context)
open PV_LIB_SPEC_F1Arithmetic14 (stage)
open PV_LIB_A_SourceSequence13

theorem quiet (q : State) (h : PV_LIB_A_PrefixMachine11.Quiet PV_LIB_SPEC_Full.programs q) :
    PV_LIB_SPEC_SourceTransport15.Quiet q :=
  ⟨PV_LIB_A_V2Neutral14.neutral _ _ h.1,h.2⟩

theorem storage_source (p : Parameters) (H : Handler) (s : Store Data) (a : Nat)
    (parents : List Frame) (rest : List PV_STX2_SliceSyntax.Node) (site : Site)
    (live : Bool) (slot : Nat) (w : OWNER) (es : List Event)
    (issued : List Issued) (consumed : List Context) :
    PV_LIB_SPEC_SourceTransport15.sourceStep p H
      (stage s a parents (.leaf (.storage site live slot)::rest) w es issued consumed) =
    stage (write s ⟨a,slot,[]⟩ none) a parents rest w es issued consumed := by
  unfold PV_LIB_SPEC_SourceTransport15.sourceStep stage
  have first := PV_THR2_IntrinsicFrameSteps.storage (runtime p).carrier (runtime p).control
    PV_LIB_SPEC_Full.programs H s a parents [] rest site live slot w es []
  simp only [PV_THR2_IntrinsicState.advance] at first
  rw [first]
  rfl

theorem aggregate_source (p : Parameters) (H : Handler) (s : Store Data) (a : Nat)
    (parents : List Frame) (rest : List PV_STX2_SliceSyntax.Node) (site : Site)
    (dest : PV_STX2_Syntax.Place) (kind : Data) (args : List Operand) (w : OWNER) (es : List Event)
    (issued : List Issued) (consumed : List Context) :
    PV_LIB_SPEC_SourceTransport15.sourceStep p H
      (stage s a parents (.leaf (.aggregateMove site dest kind args)::rest) w es issued consumed) =
    match bound (runtime p).carrier s a dest (.aggregate kind args) w with
    | none => ⟨⟨⟨.undefined (some site) s,w,es⟩,[]⟩,issued,consumed⟩
    | some t => stage t a parents rest w es issued consumed := by
  unfold PV_LIB_SPEC_SourceTransport15.sourceStep stage
  have first := PV_THR2_IntrinsicFrameAggregate.run (runtime p).carrier (runtime p).control
    PV_LIB_SPEC_Full.programs H s a parents [] rest site dest kind args w es []
  simp only [PV_THR2_IntrinsicState.advance] at first
  rw [first]
  unfold PV_THR2_IntrinsicFrameAggregate.after bound PV_THR2_IntrinsicFrameChain.bound
  split <;> simp_all only [PV_LIB_SPEC_ControlRuntime.recordIssue,PV_LIB_SPEC_ControlRuntime.issuing] <;> rfl

theorem bind_source (p : Parameters) (H : Handler) (s : Store Data) (a : Nat)
    (parents : List Frame) (rest : List PV_STX2_SliceSyntax.Node) (site : Site)
    (dest : PV_STX2_Syntax.Place) (expr : Expr) (w : OWNER) (es : List Event)
    (issued : List Issued) (consumed : List Context) :
    PV_LIB_SPEC_SourceTransport15.sourceStep p H
      (stage s a parents (.leaf (.bind site dest expr)::rest) w es issued consumed) =
    match bound (runtime p).carrier s a dest expr w with
    | none => ⟨⟨⟨.undefined (some site) s,w,es⟩,[]⟩,issued,consumed⟩
    | some t => stage t a parents rest w es issued consumed := by
  unfold PV_LIB_SPEC_SourceTransport15.sourceStep stage
  have first := PV_THR2_IntrinsicFrameBind.run (runtime p).carrier (runtime p).control
    PV_LIB_SPEC_Full.programs H s a parents [] rest site dest expr w es []
  simp only [PV_THR2_IntrinsicState.advance] at first
  rw [first]
  unfold PV_THR2_IntrinsicFrameBind.after bound PV_THR2_IntrinsicFrameChain.bound
  split <;> simp_all only [PV_LIB_SPEC_ControlRuntime.recordIssue,PV_LIB_SPEC_ControlRuntime.issuing] <;> rfl

theorem trace (cut : PV_LIB_SPEC_ReachedNative14.Cut) (p : Parameters) (H : Handler)
    (seq : Seq) (s : Store Data) (a : Nat) (parents : List Frame)
    (rest : List PV_STX2_SliceSyntax.Node) (w : OWNER) (es : List Event)
    (issued : List Issued) (consumed : List Context) (off : sites seq) :
    PV_LIB_SPEC_SourceTransport15.Trace cut p H (steps (runtime p).carrier a w seq s)
      (stage s a parents (nodes seq ++ rest) w es issued consumed) := by
  induction seq generalizing s with
  | done => trivial
  | bind site dest expr tail ih =>
    simp only [steps,nodes,List.cons_append]
    rw [Nat.add_comm 1]
    change _ ∧ _ ∧ _ ∧ _
    refine ⟨rfl,quiet _ (PV_LIB_A_ChainTrace11.bind_quiet _ s a parents [] _ site dest expr w es [] off.1),?_,?_⟩
    · intro c
      exact PV_LIB_SPEC_SourceProjection15.no_wait _ _ _ (by intro frame eq; cases eq; rfl)
    · rw [bind_source]
      cases hb : bound (runtime p).carrier s a dest expr w with
      | none => trivial
      | some t => exact ih t off.2
  | storage site live slot tail ih =>
    simp only [steps,nodes,List.cons_append]
    rw [Nat.add_comm 1]
    change _ ∧ _ ∧ _ ∧ _
    refine ⟨rfl,quiet _ (PV_LIB_A_ChainTrace11.storage_quiet _ s a parents [] _ site live slot w es [] off.1),?_,?_⟩
    · intro c
      exact PV_LIB_SPEC_SourceProjection15.no_wait _ _ _ (by intro frame eq; cases eq; rfl)
    · rw [storage_source]
      exact ih _ off.2
  | aggregate site dest kind args tail ih =>
    simp only [steps,nodes,List.cons_append]
    rw [Nat.add_comm 1]
    change _ ∧ _ ∧ _ ∧ _
    refine ⟨rfl,quiet _ (PV_LIB_A_SourceSequence13.aggregate_quiet _ s a parents [] _ site dest kind args w es []),?_,?_⟩
    · intro c
      exact PV_LIB_SPEC_SourceProjection15.no_wait _ _ _ (by intro frame eq; cases eq; rfl)
    · rw [aggregate_source]
      cases hb : bound (runtime p).carrier s a dest (.aggregate kind args) w with
      | none => trivial
      | some t =>
        exact ih t off.2

def finish (p : Parameters) (seq : Seq) (s : Store Data) (a : Nat)
    (parents : List Frame) (rest : List PV_STX2_SliceSyntax.Node) (w : OWNER)
    (es : List Event) (issued : List Issued) (consumed : List Context) : Execution :=
  ⟨⟨⟨result (runtime p).carrier a parents [] rest w seq s,w,es⟩,[]⟩,issued,consumed⟩

theorem source_result (p : Parameters) (H : Handler)
    (seq : Seq) (s : Store Data) (a : Nat) (parents : List Frame)
    (rest : List PV_STX2_SliceSyntax.Node) (w : OWNER) (es : List Event)
    (issued : List Issued) (consumed : List Context) :
    PV_LIB_SPEC_SourceTransport15.advance p H (steps (runtime p).carrier a w seq s)
      (stage s a parents (nodes seq ++ rest) w es issued consumed) =
      finish p seq s a parents rest w es issued consumed := by
  induction seq generalizing s with
  | done => rfl
  | storage site live slot tail ih =>
    simp only [steps,nodes,List.cons_append]
    rw [Nat.add_comm 1]
    change PV_LIB_SPEC_SourceTransport15.advance p H _
      (PV_LIB_SPEC_SourceTransport15.sourceStep p H _) = _
    rw [storage_source,ih]
    rfl
  | bind site dest expr tail ih =>
    simp only [steps,nodes,List.cons_append]
    rw [Nat.add_comm 1]
    change PV_LIB_SPEC_SourceTransport15.advance p H _
      (PV_LIB_SPEC_SourceTransport15.sourceStep p H _) = _
    rw [bind_source]
    cases hb : bound (runtime p).carrier s a dest expr w with
    | none => simp only [finish,result,hb]; rfl
    | some t => simp only [finish,result,hb]; exact ih t
  | aggregate site dest kind args tail ih =>
    simp only [steps,nodes,List.cons_append]
    rw [Nat.add_comm 1]
    change PV_LIB_SPEC_SourceTransport15.advance p H _
      (PV_LIB_SPEC_SourceTransport15.sourceStep p H _) = _
    rw [aggregate_source]
    cases hb : bound (runtime p).carrier s a dest (.aggregate kind args) w with
    | none => simp only [finish,result,hb]; rfl
    | some t => simp only [finish,result,hb]; exact ih t

#print axioms finish
#print axioms source_result
#print axioms bind_source
#print axioms trace
#print axioms quiet
#print axioms storage_source
#print axioms aggregate_source
end PV_LIB_A_ContextSource16
