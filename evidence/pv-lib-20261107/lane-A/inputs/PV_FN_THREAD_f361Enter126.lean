import PV_FN_THREAD_f361Callee126
import PV_THR2_PacketStructuredOneArg
import PV_THR2_IntrinsicFrameOrdinary
set_option autoImplicit false
noncomputable section
namespace PV_FN_THREAD_f361Enter126
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
open PV_FN_THREAD_f361Callee126

def source (c : Call) : Site × Data × Data := match node c with
  | .leaf (.call site (.object [("Regular",.object [("kind",kind),("generics",generics)])]) _ _ _) => (site,kind,generics)
  | _ => (⟨0,0,.null⟩,.null,.null)

def moved {E : Type} (x : Input E) (c : Call) : Input E :=
  {x with s := write x.s ⟨x.a,argumentLocal c,[]⟩ none}

def before {E : Type} (x : Input E) (c : Call) : PV_THR2_IntrinsicState.State OWNER E :=
  ⟨⟨.running ⟨{activation := x.a,remaining := node c :: rest c,loops := x.loops},
    x.parents,x.s⟩,x.w,x.es⟩,x.stack⟩

theorem source_shape (c : Call) :
    node c = .leaf (.call (source c).1
      (.object [("Regular",.object [("kind",(source c).2.1),("generics",(source c).2.2)])])
      [.move (.local (argumentLocal c))] (.local (destination c)) []) ∧
    fn c = .object [("Regular",.object [("kind",(source c).2.1),("generics",(source c).2.2)])] := by
  cases c <;> exact ⟨rfl,rfl⟩

/-- Issue only the actual source call, then use CLOSED126's call entry.
Both caller instructions are administrative; no instruction of126 is replayed. -/
theorem enter_call {E : Type} (x : Input E) (c : Call) (arc : Address)
    (cell : x.s.cells ⟨x.a,argumentLocal c,[]⟩ =
      some (PV_STX2_TypedReferences.reference arc .null)) :
    let y := child (moved x c) c arc
    PV_THR2_IntrinsicState.advance (PV_THR2_OwnInitExactReturnedCases.carrier x.C x.b)
      x.K (PV_FN_THREAD_f126_ReturnedStage.programs y)
      (PV_FN_THREAD_f126.installed y x.native arc).H 2 (before x c) =
      PV_FN_THREAD_f126_Arbitrary.entry y := by
  dsimp only
  let B := PV_THR2_OwnInitExactReturnedCases.carrier x.C x.b
  let y := child (moved x c) c arc
  let P := PV_FN_THREAD_f126_ReturnedStage.programs y
  let H := (PV_FN_THREAD_f126.installed y x.native arc).H
  have ordinary (t : Store Data) (vs : List Data) :
      PV_THR2_Catch316Segment.select (PV_THR2_IntrinsicFrameEnter.pending t x.a
        x.parents x.loops (rest c) (fn c) vs (destination c)) = none := by
    apply PV_THR2_IntrinsicFrameOrdinary.run
    intro h
    have ids := congrArg PV_THR2_OffPath.functionId h
    rw [(emitted c).1] at ids
    cases ids
  have resolved : P (fn c) = some PV_THR2_F126.live := by
    unfold P PV_FN_THREAD_f126_ReturnedStage.programs PV_THR2_PacketDataTable.resolve
    rw [(emitted c).1]
    rfl
  have run := PV_THR2_IntrinsicStructuredCall.run B x.K P H x.s x.a x.parents
    x.loops (rest c) (source c).1 (source c).2.1 (source c).2.2
    [.move (.local (argumentLocal c))] (destination c) PV_THR2_F126.live
    x.w x.es x.stack (by rfl) (by
      rw [← (source_shape c).2]
      exact ordinary) (by rw [← (source_shape c).2]; exact resolved)
  rw [← (source_shape c).1] at run
  have count : PV_THR2_IntrinsicStructuredCall.steps B x.s x.a
      [.move (.local (argumentLocal c))] x.w = 2 := by
    unfold PV_THR2_IntrinsicStructuredCall.steps
    rw [evaluated x c arc cell]
    rfl
  rw [count,← (source_shape c).2] at run
  have delivered := PV_THR2_PacketStructuredOneArg.after B x.s x.a (argumentLocal c)
    (destination c) x.parents x.loops (rest c) (source c).1 (fn c)
    (PV_STX2_TypedReferences.reference arc .null) PV_THR2_F126.live
    x.w x.es x.stack cell
  exact run.trans delivered

#print axioms source_shape
#print axioms enter_call
end PV_FN_THREAD_f361Enter126
