import PV_STX2_SliceF8
import PV_FN_SLICE_ValueCarrier
set_option autoImplicit false
noncomputable section
namespace PV_FN_SLICE_f8_PrefixData
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
structure Input (E : Type) extends PV_FN_THREAD_f315.Input E where
  capture : Address
  index : Nat
  tupleKind : Data
/-- Only call-entry operand shape, sufficient for the own-source prefix.
The whole-row generator ownership/entry linkage remains a separate task.
No future pointee/read/receiver, child result, or alias fact is assumed. -/
structure Pre {E : Type} (x : Input E) : Prop where
  self : x.s.cells ⟨x.a,1,[]⟩ = some (PV_STX2_TypedReferences.reference x.capture .null)
  tuple : x.s.cells ⟨x.a,2,[]⟩ = some (PV_STX2_Aggregates.pack x.tupleKind [.number x.index])
  fresh : x.a < x.s.nextActivation
  owner : PV_W1_OwnerWellFormed.OwnerWellFormed x.w x.s.nextActivation

def tupleKind : Data := match PV_STX2_SliceF8.node7 with
  | .leaf (.aggregateMove _ _ k _) => k | _ => .null
def tuple (n : Nat) := PV_STX2_Aggregates.pack tupleKind [.number n]
def emptied (k : Data) : Data := .object [("aggregate-kind",k),("aggregate-slots",.array [.array []])]
def generator {E : Type} (x : Input E) :=
  PV_STX2_TypedReferences.reference {x.capture with fields := x.capture.fields ++ [0]} .null

def store1 {E : Type} (x : Input E) := write x.s ⟨x.a,0,[]⟩ none
def store2 {E : Type} (x : Input E) := write (store1 x) ⟨x.a,3,[]⟩ none
def store3 {E : Type} (x : Input E) :=
  write (write (store2 x) ⟨x.a,2,[]⟩ (some (emptied x.tupleKind))) ⟨x.a,3,[]⟩ (some (.number x.index))
def store4 {E : Type} (x : Input E) := write (store3 x) ⟨x.a,4,[]⟩ none
def store5 {E : Type} (x : Input E) := write (store4 x) ⟨x.a,5,[]⟩ none
def store6 {E : Type} (x : Input E) := write (store5 x) ⟨x.a,5,[]⟩ (some (generator x))
def store7 {E : Type} (x : Input E) := write (store6 x) ⟨x.a,6,[]⟩ none
def store8 {E : Type} (x : Input E) := write (store7 x) ⟨x.a,6,[]⟩ (some (tuple x.index))
def moved {E : Type} (x : Input E) := write (write (store8 x) ⟨x.a,5,[]⟩ none) ⟨x.a,6,[]⟩ none

def source : Site × Data × List Operand × Nat × List Instruction := match PV_STX2_SliceF8.node8 with
  | .leaf (.call site fn args (.local dest) cleanup) => (site,fn,args,dest,cleanup)
  | _ => (⟨0,0,.null⟩,.null,[],0,[])
def entry6 {E : Type} (x : Input E) : PV_W1_LeafBoundary.Entry :=
  {store := moved x,caller := x.a,parents := x.parent :: x.parents,loops := [],
    rest := PV_STX2_SliceF8.program.body.drop 9,callee := source.2.1,
    arguments := [generator x,tuple x.index],destination := source.2.2.2.1,suspended := x.stack}
def issued {E : Type} (x : Input E) := PV_THR2_StaticCall.issued (moved x) [generator x,tuple x.index]
def out {E : Type} (x : Input E) : PV_THR2_IntrinsicState.State OWNER E :=
  let waiting : PV_STX2_Native.Waiting Data :=
    ⟨.child source.2.1 x.s.nextActivation [generator x,tuple x.index],
      .child x.s.nextActivation (.local 4),source.2.2.2.2⟩
  ⟨⟨.running ⟨{activation := x.a,remaining := PV_STX2_SliceF8.program.body.drop 9,waiting := some waiting},
    x.parent :: x.parents,issued x⟩,x.w,x.es⟩,x.stack⟩
/-- Source-minted child frame has no pre-existing OWNER registration (slice-9).
No native reply or child well-formedness hypothesis is used. -/
theorem child_fresh {E : Type} (x : Input E) (pre : Pre x) (fields : List Nat) :
    x.w.places ⟨x.s.nextActivation,fields⟩ = none :=
  PV_W1_OwnerWellFormed.fresh_callee _ _ pre.owner fields

theorem issued_owner {E : Type} (x : Input E) (pre : Pre x) :
    PV_W1_OwnerWellFormed.OwnerWellFormed x.w (issued x).nextActivation := by
  change PV_W1_OwnerWellFormed.OwnerWellFormed x.w (x.s.nextActivation+1)
  exact PV_W1_OwnerWellFormed.counter_mono _ _ _ pre.owner (Nat.le_succ _)

/-- Every pre-existing foreign cell is unchanged; only own locals and the
minted f6 argument cells are written, with the explicit issued store retained. -/
theorem frame {E : Type} (x : Input E) (p : Address)
    (own : p.activation ≠ x.a) (child : p.activation ≠ x.s.nextActivation) :
    (issued x).cells p = x.s.cells p := by
  have diff (n : Nat) : p ≠ (⟨x.a,n,[]⟩ : Address) := by
    intro h; exact own (congrArg Address.activation h)
  have freshDiff (n : Nat) : p ≠ (⟨x.s.nextActivation,n,[]⟩ : Address) := by
    intro h; exact child (congrArg Address.activation h)
  simp only [issued,PV_THR2_StaticCall.issued,PV_STX2_Native.arguments,moved,
    store8,store7,store6,store5,store4,store3,store2,store1,write,
    if_neg (diff 0),if_neg (diff 2),if_neg (diff 3),if_neg (diff 4),if_neg (diff 5),if_neg (diff 6),
    if_neg (freshDiff 1),if_neg (freshDiff 2)]
#print axioms child_fresh
#print axioms issued_owner
#print axioms frame
end PV_FN_SLICE_f8_PrefixData
