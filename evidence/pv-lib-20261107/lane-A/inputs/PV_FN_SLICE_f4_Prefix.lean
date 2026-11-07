import PV_STX2_SliceF4
import PV_FN_SLICE_f23
import PV_FN_SLICE_f8_Prefix
import PV_FN_W2_LifetimePrefix
import PV_STX2_LiveNumbering
import PV_FN_SLICE_f9_Prefix
set_option autoImplicit false
noncomputable section
namespace PV_FN_SLICE_f4_Prefix
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
abbrev Input := PV_FN_THREAD_f315.Input
/-- Own-entry prefix only. The complete f4 generator/buffer domain and f9
contract are not supplied by this preliminary source-entry predicate. -/
structure Pre {E : Type} (x : Input E) : Prop where
  generator : x.s.cells ⟨x.a,1,[]⟩ = some x.ptr
  saved : x.parent.waiting = some x.wait
  action : x.wait.action = .child x.a (.local x.dest)
  owner : PV_W1_OwnerWellFormed.OwnerWellFormed x.w x.s.nextActivation
  numbered : PV_STX2_LiveNumbering.Numbered
    ⟨{activation := x.a,remaining := PV_STX2_SliceF4.program.body},x.parent :: x.parents,x.s⟩
  suspended : ∀ c ∈ x.stack, PV_STX2_LiveNumbering.Numbered
    {c with store := {c.store with nextActivation := x.s.nextActivation}}

def source : Site × Data × List Instruction := match PV_STX2_SliceF4.node2 with
  | .leaf (.call site fn _ _ cleanup) => (site,fn,cleanup)
  | _ => (⟨0,0,.null⟩,.null,[])
def kindGenerics : Data × Data := match PV_STX2_SliceF4.node2 with
  | .leaf (.call _ (.object [("Regular",.object [("kind",k),("generics",g)])]) _ _ _) => (k,g)
  | _ => (.null,.null)
def storage {E : Type} (x : Input E) := write (write x.s ⟨x.a,10,[]⟩ none) ⟨x.a,11,[]⟩ none
def issued {E : Type} (x : Input E) := PV_THR2_StaticCall.issued (storage x) []
def waiting {E : Type} (x : Input E) : PV_STX2_Native.Waiting Data :=
  ⟨.child source.2.1 x.s.nextActivation [],.child x.s.nextActivation (.local 11),source.2.2⟩
def parent23 {E : Type} (x : Input E) : Frame :=
  {activation := x.a,remaining := PV_STX2_SliceF4.program.body.drop 3,waiting := some (waiting x)}
def out {E : Type} (x : Input E) : PV_THR2_IntrinsicState.State OWNER E :=
  ⟨⟨.running ⟨parent23 x,x.parent :: x.parents,issued x⟩,x.w,x.es⟩,x.stack⟩
def input23 {E : Type} (x : Input E) : PV_FN_SLICE_f23.Input E :=
  {x with
    a := x.s.nextActivation,s := issued x,parent := parent23 x,
    parents := x.parent :: x.parents,wait := waiting x,dest := 11}

theorem pre23 {E : Type} (x : Input E) (pre : Pre x) : PV_FN_SLICE_f23.Pre (input23 x) :=
  ⟨rfl,rfl,PV_W1_OwnerWellFormed.counter_mono _ _ _ pre.owner (Nat.le_succ _)⟩

theorem issue23 {E : Type} (x : Input E) :
    PV_THR2_IntrinsicState.advance (PV_FN_SLICE_ValueCarrier.carrier x.C) x.K x.P x.H 3
      ⟨⟨.running ⟨{activation := x.a,remaining := PV_STX2_SliceF4.program.body},
        x.parent :: x.parents,x.s⟩,x.w,x.es⟩,x.stack⟩ = out x := by
  let ops : List PV_FN_W2_LifetimePrefix.Operation :=
    [PV_STX2_SliceF4.node0,PV_STX2_SliceF4.node1].map PV_FN_SLICE_f9_Prefix.operation
  have front := PV_FN_W2_LifetimePrefix.run (PV_FN_SLICE_ValueCarrier.carrier x.C)
    x.K x.P x.H ops x.s x.a (x.parent :: x.parents) []
    (PV_STX2_SliceF4.program.body.drop 2) x.w x.es x.stack
  change PV_THR2_IntrinsicState.advance _ _ _ _ 2
    ⟨⟨.running ⟨{activation := x.a,remaining := PV_STX2_SliceF4.program.body},
      x.parent :: x.parents,x.s⟩,x.w,x.es⟩,x.stack⟩ = _ at front
  rw [show 3=2+1 by rfl,PV_THR2_IntrinsicComposition.advance_add,front]
  change PV_THR2_IntrinsicState.advance _ _ _ _ 1
    ⟨⟨.running ⟨{activation := x.a,remaining := PV_STX2_SliceF4.node2 ::
      PV_STX2_SliceF4.program.body.drop 3},x.parent :: x.parents,storage x⟩,x.w,x.es⟩,x.stack⟩ = _
  unfold PV_STX2_SliceF4.node2
  exact PV_FN_SLICE_f8_Prefix.issue _ x.K x.P x.H (storage x) (storage x) x.a
    (x.parent :: x.parents) (PV_STX2_SliceF4.program.body.drop 3) source.1 kindGenerics.1
    kindGenerics.2 [] [] 11 source.2.2 x.w x.es x.stack rfl

theorem enter23 {E : Type} (x : Input E)
    (resolve23 : x.P source.2.1 = some PV_STX2_SliceF23.program) :
    PV_THR2_IntrinsicState.advance (PV_FN_SLICE_ValueCarrier.carrier x.C) x.K x.P x.H 1 (out x) =
      ⟨⟨.running ⟨{activation := (input23 x).a,remaining := PV_STX2_SliceF23.program.body},
        (input23 x).parent :: (input23 x).parents,(input23 x).s⟩,(input23 x).w,(input23 x).es⟩,(input23 x).stack⟩ := by
  simp [PV_THR2_IntrinsicState.advance,PV_THR2_IntrinsicState.step,
    PV_THR2_Catch316Segment.select,PV_THR2_Execution.step,PV_THR2_Dynamic.active,
    PV_THR2_GapCompletion.step,PV_THR2_AggregateCompletion.complete,
    PV_STX2_SliceMachine.step,out,parent23,waiting,input23,resolve23]

/-- CLOSED f23 at its exact source51 call. The uninitialized union value is
DERIVED from that contract; no fixed native success or fabricated reply. -/
theorem through23 {E : Type} (x : Input E) (pre : Pre x)
    (resolve23 : x.P source.2.1 = some PV_STX2_SliceF23.program) :
    PV_FN_SLICE_f23.Post (input23 x) ∧
    PV_THR2_IntrinsicState.advance (PV_FN_SLICE_ValueCarrier.carrier x.C) x.K x.P x.H 8
      ⟨⟨.running ⟨{activation := x.a,remaining := PV_STX2_SliceF4.program.body},
        x.parent :: x.parents,x.s⟩,x.w,x.es⟩,x.stack⟩ =
      ⟨⟨.running ⟨{activation := x.a,remaining := PV_STX2_SliceF4.program.body.drop 3},
        x.parent :: x.parents,PV_FN_SLICE_f23.finalStore (input23 x)⟩,x.w,x.es⟩,x.stack⟩ := by
  have closed := PV_FN_SLICE_f23.contract (input23 x) (pre23 x pre)
  refine ⟨closed,?_⟩
  rw [show 8=3+(1+4) by rfl,PV_THR2_IntrinsicComposition.advance_add,issue23,
    PV_THR2_IntrinsicComposition.advance_add,enter23 x resolve23]
  exact closed.1
#print axioms pre23
#print axioms issue23
#print axioms enter23
#print axioms through23
end PV_FN_SLICE_f4_Prefix
