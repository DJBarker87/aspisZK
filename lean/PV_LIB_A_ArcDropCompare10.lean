import PV_LIB_A_FetchSubReply10
import PV_LIB_A_TypedBody486
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_ArcDropCompare10
open scoped Classical
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine

/-- Builtin numeric Ne, used by actual486 after581. Other operators retain
their exact old interpretation. This defines no native or allocation effect. -/
def numeric (C : Carrier OWNER Data) : Carrier OWNER Data :=
  {C with binary := fun op l r => match op,l,r with
    | "Ne",.number n,.number m => some (.boolean (decide (n ≠ m)))
    | _,_,_ => C.binary op l r}

def carrier (C : Carrier OWNER Data) (b : Bool) :=
  PV_LIB_A_DestructorValues10.carrier (numeric C) b

def call : Data × List Instruction :=
  match PV_LIB_A_TypedBody486.node13 [] with
  | .leaf (.call _ fn _ _ cleanup) => (fn,cleanup)
  | _ => (.null,[])

def wait (child : Nat) (args : List Data) : PV_STX2_Native.Waiting Data :=
  ⟨.child call.1 child args,.child child (.local 3),call.2⟩

def returnedStore (c : Config) (child old : Nat) : Store Data :=
  write (write c.store ⟨child,0,[]⟩ (some (.number old)))
    ⟨c.frame.activation,3,[]⟩ (some (.number old))

/-- The actual21732 call is exactly emitted581, not a guessed atomic leaf. -/
theorem function : PV_THR2_OffPath.functionId call.1 = some 581 := rfl

/-- Feed the OLD value from the documented581 model into486's ACTUAL result
local3. The original source return administration is used, with all events.
This is the returned arm of a full-reply model, not a row success assumption. -/
theorem delivery (C : Carrier OWNER Data) (c : Config) (child old : Nat)
    (args : List Data) (value : Data) (w : OWNER) (events : List PV_RJ4IDB.NativeEvent) :
    PV_THR2_ChildBoundary.delivered C c (wait child args)
      (PV_LIB_A_FetchSubReply10.PV_THR2_LibrarySemantics_FetchSubValue581 old
        ⟨.returned (.ok value),w,events⟩) =
      ⟨.running {c with store := returnedStore c child old, frame := {c.frame with waiting := none}},w,events⟩ := rfl

/-- Derive486's actual Ne expression from the returned source local. The move
of local3 is preserved; old=1 is precisely the last-strong control branch. -/
theorem compare (C : Carrier OWNER Data) (b : Bool) (c : Config) (w : OWNER)
    (child old : Nat) (types : List Data) :
    PV_STX2_Store.bind (carrier C b) (returnedStore c child old) w c.frame.activation
      (.local 2)
      (match PV_LIB_A_TypedBody486.node16 types with
       | .leaf (.bind _ _ expression) => expression
       | _ => .nullary .null) =
      some (write (write (returnedStore c child old) ⟨c.frame.activation,3,[]⟩ none)
        ⟨c.frame.activation,2,[]⟩ (some (.boolean (decide (old ≠ 1))))) := by
  simp [PV_LIB_A_TypedBody486.node16,PV_STX2_Store.bind,evaluate,operand,
    PV_STX2_Store.read,locate,writeAddress,write,returnedStore,
    carrier,numeric,PV_LIB_A_DestructorValues10.carrier,
    PV_THR2_AggregateCompletion.carrier,PV_THR2_OwnInitExactReturnedCases.carrier,
    PV_THR2_EntryDynamic.carrier,PV_THR2_Scalars.carrier,
    PV_STX2_TypedReferences.carrier,PV_STX2_LengthBranch.carrier,
    PV_STX2_Aggregates.carrier,PV_THR2_KeyInstall.carrier,
    PV_THR2_KeyValues.carrier,PV_THR2_FunctionValues.base,
    PV_THR2_ThreadFields.carrier,PV_THR2_ScopeLiterals.carrier,PV_THR2_RangeLiterals.carrier]

/-- Exact emitted branch alternatives: n≠1 skips slow destruction; n=1 enters
its fence/slow-drop block. No nonlast or success restriction is imposed. -/
theorem source_branch (types : List Data) :
    PV_LIB_A_TypedBody486.node81 types = .branch
      ⟨486,21826,.array [.atom "body",.atom "statements",.number 17]⟩
      (.move (.local 2)) [] (PV_LIB_A_TypedBody486.block80 types) := rfl

#print axioms numeric
#print axioms carrier
#print axioms call
#print axioms wait
#print axioms returnedStore
#print axioms function
#print axioms delivery
#print axioms compare
#print axioms source_branch
end PV_LIB_A_ArcDropCompare10
