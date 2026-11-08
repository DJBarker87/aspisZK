import PV_STX2_SliceF7
import PV_FN_SLICE_f8
set_option autoImplicit false
noncomputable section
namespace PV_FN_SLICE_f7_Prefix
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
structure Input (E : Type) extends PV_FN_THREAD_f315.Input E where
  index : Nat
  tupleKind : Data
/-- Own-call-entry operands for FnOnce: capture is a VALUE in LOCAL1. f7
borrows that local itself; no address supplied by f9 or another caller is fixed. -/
structure Pre {E : Type} (x : Input E) : Prop where
  capture : x.s.cells ⟨x.a,1,[]⟩ = some x.ptr
  tuple : x.s.cells ⟨x.a,2,[]⟩ = some (PV_STX2_Aggregates.pack x.tupleKind [.number x.index])
  fresh : x.a < x.s.nextActivation
  owner : PV_W1_OwnerWellFormed.OwnerWellFormed x.w x.s.nextActivation

def self {E : Type} (x : Input E) := PV_STX2_TypedReferences.reference ⟨x.a,1,[]⟩ .null
def tuple {E : Type} (x : Input E) := PV_STX2_Aggregates.pack x.tupleKind [.number x.index]
def store1 {E : Type} (x : Input E) := write x.s ⟨x.a,0,[]⟩ none
def store2 {E : Type} (x : Input E) := write (store1 x) ⟨x.a,3,[]⟩ none
def store3 {E : Type} (x : Input E) := write (store2 x) ⟨x.a,3,[]⟩ (some (self x))
def moved {E : Type} (x : Input E) := write (write (store3 x) ⟨x.a,3,[]⟩ none) ⟨x.a,2,[]⟩ none
def issued {E : Type} (x : Input E) := PV_THR2_StaticCall.issued (moved x) [self x,tuple x]
def source : Site × Data × List Operand × Nat × List Instruction := match PV_STX2_SliceF7.node3 with
  | .leaf (.call site fn args (.local dest) cleanup) => (site,fn,args,dest,cleanup)
  | _ => (⟨0,0,.null⟩,.null,[],0,[])
def kindGenerics : Data × Data := match PV_STX2_SliceF7.node3 with
  | .leaf (.call _ (.object [("Regular",.object [("kind",k),("generics",g)])]) _ _ _) => (k,g)
  | _ => (.null,.null)
def metadata : Data := match PV_STX2_SliceF7.node2 with
  | .leaf (.bind _ _ (.reference _ (.constant c))) => c | _ => .null

def waiting {E : Type} (x : Input E) : PV_STX2_Native.Waiting Data :=
  ⟨.child source.2.1 x.s.nextActivation [self x,tuple x],
    .child x.s.nextActivation (.local 0),source.2.2.2.2⟩
def parent8 {E : Type} (x : Input E) : Frame :=
  {activation := x.a,remaining := PV_STX2_SliceF7.program.body.drop 4,waiting := some (waiting x)}
def out {E : Type} (x : Input E) : PV_THR2_IntrinsicState.State OWNER E :=
  ⟨⟨.running ⟨parent8 x,x.parent :: x.parents,issued x⟩,x.w,x.es⟩,x.stack⟩

theorem run {E : Type} (x : Input E) (pre : Pre x) :
    PV_THR2_IntrinsicState.advance (PV_FN_SLICE_ValueCarrier.carrier x.C) x.K x.P x.H 4
      ⟨⟨.running ⟨{activation := x.a,remaining := PV_STX2_SliceF7.program.body},
        x.parent :: x.parents,x.s⟩,x.w,x.es⟩,x.stack⟩ = out x := by
  let B := PV_FN_SLICE_ValueCarrier.carrier x.C
  let q (n : Nat) (t : Store Data) : PV_THR2_IntrinsicState.State OWNER E :=
    ⟨⟨.running ⟨{activation := x.a,remaining := PV_STX2_SliceF7.program.body.drop n},
      x.parent :: x.parents,t⟩,x.w,x.es⟩,x.stack⟩
  have h0 : PV_THR2_IntrinsicState.advance B x.K x.P x.H 1 (q 0 x.s) = q 1 (store1 x) := by
    change PV_THR2_IntrinsicState.advance B x.K x.P x.H 1
      ⟨⟨.running ⟨{activation := x.a,remaining := PV_STX2_SliceF7.node0 :: PV_STX2_SliceF7.program.body.drop 1},x.parent :: x.parents,x.s⟩,x.w,x.es⟩,x.stack⟩ = _
    unfold PV_STX2_SliceF7.node0
    exact PV_THR2_IntrinsicFrameSteps.storage B x.K x.P x.H _ _ _ _ _ _ _ _ _ _ _
  have h1 : PV_THR2_IntrinsicState.advance B x.K x.P x.H 1 (q 1 (store1 x)) = q 2 (store2 x) := by
    change PV_THR2_IntrinsicState.advance B x.K x.P x.H 1
      ⟨⟨.running ⟨{activation := x.a,remaining := PV_STX2_SliceF7.node1 :: PV_STX2_SliceF7.program.body.drop 2},x.parent :: x.parents,store1 x⟩,x.w,x.es⟩,x.stack⟩ = _
    unfold PV_STX2_SliceF7.node1
    exact PV_THR2_IntrinsicFrameSteps.storage B x.K x.P x.H _ _ _ _ _ _ _ _ _ _ _
  have h2 : PV_THR2_IntrinsicState.advance B x.K x.P x.H 1 (q 2 (store2 x)) = q 3 (store3 x) := by
    change PV_THR2_IntrinsicState.advance B x.K x.P x.H 1
      ⟨⟨.running ⟨{activation := x.a,remaining := PV_STX2_SliceF7.node2 :: PV_STX2_SliceF7.program.body.drop 3},x.parent :: x.parents,store2 x⟩,x.w,x.es⟩,x.stack⟩ = _
    unfold PV_STX2_SliceF7.node2
    rw [PV_THR2_IntrinsicFrameBind.run]
    have unit : B.constant metadata = some .null := rfl
    have reference (p : Address) : B.reference p .null = PV_STX2_TypedReferences.reference p .null := rfl
    change PV_THR2_IntrinsicFrameBind.after B (store2 x) x.a (x.parent :: x.parents) []
      (PV_STX2_SliceF7.program.body.drop 3) _ (.local 3)
      (.reference (.local 1) (.constant metadata)) x.w x.es x.stack = _
    simp [PV_THR2_IntrinsicFrameBind.after,PV_STX2_Store.bind,evaluate,operand,
      PV_STX2_Store.read,locate,writeAddress,write,unit,reference,store1,store2,store3,self,q]
  have h3 : PV_THR2_IntrinsicState.advance B x.K x.P x.H 1 (q 3 (store3 x)) = out x := by
    change PV_THR2_IntrinsicState.advance B x.K x.P x.H 1
      ⟨⟨.running ⟨{activation := x.a,remaining := PV_STX2_SliceF7.node3 :: PV_STX2_SliceF7.program.body.drop 4},x.parent :: x.parents,store3 x⟩,x.w,x.es⟩,x.stack⟩ = _
    unfold PV_STX2_SliceF7.node3
    have evaluated : operands B x.w x.a source.2.2.1 (store3 x) = some ([self x,tuple x],moved x) := by
      change operands B x.w x.a [.move (.local 3),.move (.local 2)] (store3 x) = _
      simp [operands,operand,PV_STX2_Store.read,locate,writeAddress,write,store3,store2,store1,moved,tuple,pre.tuple]
    exact PV_FN_SLICE_f8_Prefix.issue B x.K x.P x.H (store3 x) (moved x) x.a
      (x.parent :: x.parents) (PV_STX2_SliceF7.program.body.drop 4) source.1 kindGenerics.1 kindGenerics.2
      source.2.2.1 [self x,tuple x] 0 source.2.2.2.2 x.w x.es x.stack evaluated
  change PV_THR2_IntrinsicState.advance B x.K x.P x.H 4 (q 0 x.s) = _
  rw [show 4=1+3 by omega,PV_THR2_IntrinsicComposition.advance_add,h0,
    show 3=1+2 by omega,PV_THR2_IntrinsicComposition.advance_add,h1,
    show 2=1+1 by omega,PV_THR2_IntrinsicComposition.advance_add,h2]
  exact h3

def input8 {E : Type} (x : Input E) : PV_FN_SLICE_f8.Input E :=
  {x.toInput with a := x.s.nextActivation,s := issued x,parent := parent8 x,parents := x.parent :: x.parents,wait := waiting x,dest := 0,capture := ⟨x.a,1,[]⟩,index := x.index,tupleKind := x.tupleKind}

/-- Discharge f8's actual Pre at173: source minting supplies its operands and
OWNER freshness. No future generator read, child output or receiver is assumed. -/
theorem pre8 {E : Type} (x : Input E) (pre : Pre x)
    (resolve6 : x.P PV_FN_SLICE_f8_PrefixData.source.2.1 = some PV_STX2_SliceF6.program) :
    PV_FN_SLICE_f8.Pre (input8 x) := by
  refine {self := ?_,tuple := ?_,fresh := ?_,owner := ?_,saved := rfl,action := rfl,source6 := resolve6}
  · simp [input8,issued,PV_THR2_StaticCall.issued,PV_STX2_Native.arguments,write,self,moved,store3,store2,store1]
  · simp [input8,issued,PV_THR2_StaticCall.issued,PV_STX2_Native.arguments,write,tuple,moved,store3,store2,store1]
  · change x.s.nextActivation < x.s.nextActivation+1
    omega
  · change PV_W1_OwnerWellFormed.OwnerWellFormed x.w (x.s.nextActivation+1)
    exact PV_W1_OwnerWellFormed.counter_mono _ _ _ pre.owner (Nat.le_succ _)
#print axioms run
#print axioms pre8
set_option pp.fullNames true in
set_option pp.piBinderNames true in
set_option pp.proofs false in
#print pre8
end PV_FN_SLICE_f7_Prefix
