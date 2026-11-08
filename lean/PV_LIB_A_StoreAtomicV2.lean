import PV_LIB_A_StorePrimitiveV2
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_StoreAtomicV2
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_LIB_A_StorePrimitiveV2
/-- Correct source representation of AtomicBool's UnsafeCell<u8>, not bool.
The earlier primitive draft's646 is superseded; core/sync/atomic.rs explicitly
casts val as u8. This is a model correction before any caller consumption. -/
def PV_THR2_LibrarySemantics_AtomicBoolStore646 {W : Type} (C : Carrier W Data)
    (args : List Data) (s : Store Data) (w : W) : Option (Store Data) :=
  match args with
  | [reference,.boolean value,_] => put C s w reference [0,0]
      (.number (if value then 1 else 0))
  | _ => none

/-- ONE named source meaning for emitted Cell::set504. Cell<T> has the
UnsafeCell<T> value field; this applies inside boxed state as well as locals.
ACTIVE's specialized scalar Cell::replace289 remains its existing meaning. -/
def PV_THR2_LibrarySemantics_CellSet504 {W : Type} (C : Carrier W Data)
    (args : List Data) (s : Store Data) (w : W) : Option (Store Data) :=
  match args with
  | [reference,value] => put C s w reference [0,0] value
  | _ => none

/-- The emitted Result ADT discriminant. Metadata remains in the source value;
no world-dependent marker or boolean oracle chooses CAS success. -/
def resultVariant : Data → Option Nat
  | .object [("thread-aggregate-kind",.object [("Adt",.array [_,.number n,_])]),
      ("thread-aggregate-slots",.array _)] => some n
  | _ => none

/-- CAS writes only on source Result::Ok. A weak CAS may spuriously return Err,
so comparing the old cell to expected is insufficient. Full nonreturned
replies are retained and no completion is manufactured. The returned value
law/atomic memory ordering remains a named native-semantics obligation. -/
def compareExchange {W E : Type} (C : Carrier W Data) (args : List Data)
    (s : Store Data) (w : W) (r : Reply W E Data) : Option (Store Data) :=
  match r.answer with
  | .returned (.ok result) => do
    match args with
    | [reference,_,replacement,_,_] =>
      let variant ← resultVariant result
      match variant with
      | 0 => put C s w reference [0,0] replacement
      | 1 => some s
      | _ => none
    | _ => none
  | _ => some s

/-- ONE named documented meaning per emitted function, despite shared code. -/
def PV_THR2_LibrarySemantics_CompareExchangeWeak530 {W E : Type}
    (C : Carrier W Data) (args : List Data) (s : Store Data) (w : W)
    (r : Reply W E Data) := compareExchange C args s w r

def PV_THR2_LibrarySemantics_CompareExchange555 {W E : Type}
    (C : Carrier W Data) (args : List Data) (s : Store Data) (w : W)
    (r : Reply W E Data) := compareExchange C args s w r

theorem bool_cast {W : Type} (C : Carrier W Data) (s : Store Data) (w : W)
    (reference ordering : Data) (b : Bool) :
    PV_THR2_LibrarySemantics_AtomicBoolStore646 C [reference,.boolean b,ordering] s w =
      put C s w reference [0,0] (.number (if b then 1 else 0)) := rfl

theorem cas_error {W E : Type} (C : Carrier W Data) (s : Store Data) (w : W)
    (reference expected replacement success failure ty payload : Data) :
    compareExchange C [reference,expected,replacement,success,failure] s w
      (⟨.returned (.ok (.object [("thread-aggregate-kind",.object [("Adt",.array [ty,.number 1,.null])]),
        ("thread-aggregate-slots",.array [payload])])),w,[]⟩ : Reply W E Data) = some s := rfl

#print axioms PV_THR2_LibrarySemantics_AtomicBoolStore646
#print axioms PV_THR2_LibrarySemantics_CellSet504
#print axioms PV_THR2_LibrarySemantics_CompareExchangeWeak530
#print axioms PV_THR2_LibrarySemantics_CompareExchange555
#print axioms bool_cast
#print axioms cas_error
end PV_LIB_A_StoreAtomicV2
