import PV_STX2_SliceF9
import PV_FN_SLICE_ValueCarrier
import PV_FN_W2_LifetimePrefix
import PV_THR2_IntrinsicFrameAggregate
import PV_STX2_LiveNumbering
set_option autoImplicit false
noncomputable section
namespace PV_FN_SLICE_f9_Prefix
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
abbrev Input := PV_FN_THREAD_f315.Input
/-- Preliminary own-entry source-prefix domain. The typed output-buffer and
generator domain needed for the entire row is not asserted by this module. -/
structure Pre {E : Type} (x : Input E) : Prop where
  buffer : x.s.cells ⟨x.a,1,[]⟩ = some x.allocator
  generator : x.s.cells ⟨x.a,2,[]⟩ = some x.ptr
  saved : x.parent.waiting = some x.wait
  action : x.wait.action = .child x.a (.local x.dest)
  owner : PV_W1_OwnerWellFormed.OwnerWellFormed x.w x.s.nextActivation
  numbered : PV_STX2_LiveNumbering.Numbered
    ⟨{activation := x.a,remaining := PV_STX2_SliceF9.program.body},x.parent :: x.parents,x.s⟩
  suspended : ∀ c ∈ x.stack, PV_STX2_LiveNumbering.Numbered c

def guardKind : Data := match PV_STX2_SliceF9.node8 with
  | .leaf (.aggregateMove _ _ kind _) => kind | _ => .null
def zero : Data := match PV_STX2_SliceF9.node8 with
  | .leaf (.aggregateMove _ _ _ [_,.constant c]) => c | _ => .null
def guard (buffer : Data) (n : Nat) := PV_STX2_Aggregates.pack guardKind [buffer,.number n]
def operation (n : PV_STX2_SliceSyntax.Node) : PV_FN_W2_LifetimePrefix.Operation :=
  match n with
  | .leaf (.storage site live slot) => (site,live,slot)
  | _ => (⟨0,0,.null⟩,false,0)
def operations := [PV_STX2_SliceF9.node0,PV_STX2_SliceF9.node1,PV_STX2_SliceF9.node2,
  PV_STX2_SliceF9.node3,PV_STX2_SliceF9.node4,PV_STX2_SliceF9.node5,
  PV_STX2_SliceF9.node6,PV_STX2_SliceF9.node7].map operation
def storage {E : Type} (x : Input E) : Store Data :=
  PV_FN_W2_LifetimePrefix.store x.s x.a operations
def prepared {E : Type} (x : Input E) := write (storage x) ⟨x.a,3,[]⟩ (some (guard x.allocator 0))
def out {E : Type} (x : Input E) : PV_THR2_IntrinsicState.State OWNER E :=
  ⟨⟨.running ⟨{activation := x.a,remaining := PV_STX2_SliceF9.program.body.drop 9},
    x.parent :: x.parents,prepared x⟩,x.w,x.es⟩,x.stack⟩

/-- The eight lifetime instructions touch only the current activation. -/
theorem frame {E : Type} (x : Input E) (p : Address) (own : p.activation ≠ x.a) :
    (prepared x).cells p = x.s.cells p := by
  have different (n : Nat) : p ≠ (⟨x.a,n,[]⟩ : Address) := by
    intro eq; exact own (congrArg Address.activation eq)
  simp only [prepared,storage,PV_FN_W2_LifetimePrefix.store,operations,List.map_cons,List.map_nil,
    operation,PV_STX2_SliceF9.node0,PV_STX2_SliceF9.node1,PV_STX2_SliceF9.node2,
    PV_STX2_SliceF9.node3,PV_STX2_SliceF9.node4,PV_STX2_SliceF9.node5,
    PV_STX2_SliceF9.node6,PV_STX2_SliceF9.node7,List.foldl_cons,List.foldl_nil,write,if_neg (different _)]

/-- Source guard initialization, from arbitrary row call entry, retains the
full lower stack, prior events and generator. No child is executed here. -/
theorem run {E : Type} (x : Input E) (pre : Pre x) :
    PV_THR2_IntrinsicState.advance (PV_FN_SLICE_ValueCarrier.carrier x.C) x.K x.P x.H 9
      ⟨⟨.running ⟨{activation := x.a,remaining := PV_STX2_SliceF9.program.body},
        x.parent :: x.parents,x.s⟩,x.w,x.es⟩,x.stack⟩ = out x := by
  let B := PV_FN_SLICE_ValueCarrier.carrier x.C
  have value : (storage x).cells ⟨x.a,1,[]⟩ = some x.allocator := by
    simpa [storage,PV_FN_W2_LifetimePrefix.store,operations,operation,
      PV_STX2_SliceF9.node0,PV_STX2_SliceF9.node1,PV_STX2_SliceF9.node2,
      PV_STX2_SliceF9.node3,PV_STX2_SliceF9.node4,PV_STX2_SliceF9.node5,
      PV_STX2_SliceF9.node6,PV_STX2_SliceF9.node7,write] using pre.buffer
  have constant : B.constant zero = some (.number 0) := rfl
  have aggregate : B.aggregate guardKind [x.allocator,.number 0] = some (guard x.allocator 0) := rfl
  have front :=  PV_FN_W2_LifetimePrefix.run B x.K x.P x.H operations x.s x.a
    (x.parent :: x.parents) [] (PV_STX2_SliceF9.program.body.drop 8) x.w x.es x.stack
  change PV_THR2_IntrinsicState.advance B x.K x.P x.H 8
    ⟨⟨.running ⟨{activation := x.a,remaining := PV_STX2_SliceF9.program.body},
      x.parent :: x.parents,x.s⟩,x.w,x.es⟩,x.stack⟩ = _ at front
  rw [show 9=8+1 by rfl,PV_THR2_IntrinsicComposition.advance_add,front]
  change PV_THR2_IntrinsicState.advance B x.K x.P x.H 1
    ⟨⟨.running ⟨{activation := x.a,remaining := PV_STX2_SliceF9.node8 ::
      PV_STX2_SliceF9.program.body.drop 9},x.parent :: x.parents,storage x⟩,x.w,x.es⟩,x.stack⟩ = _
  unfold PV_STX2_SliceF9.node8
  rw [PV_THR2_IntrinsicFrameAggregate.run]
  change PV_THR2_IntrinsicFrameAggregate.after B (storage x) x.a (x.parent :: x.parents) []
    (PV_STX2_SliceF9.program.body.drop 9) _ (.local 3) guardKind
    [.copy (.local 1),.constant zero] x.w x.es x.stack = out x
  simp [PV_THR2_IntrinsicFrameAggregate.after,PV_STX2_Store.bind,evaluate,operands,operand,
    PV_STX2_Store.read,readAddress,locate,writeAddress,value,constant,aggregate,prepared,out]

#print axioms frame
#print axioms run
end PV_FN_SLICE_f9_Prefix
