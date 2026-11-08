import PV_LIB_A_StoreActionMachine
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_ActionAdequacyGap
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_THR2_SourceStoreLibrary PV_LIB_StoreActionTable

/-- The emitted regular-function shape, retaining ALL generic metadata. -/
def token (n : Nat) (generics : Data) : Data :=
  .object [("Regular",.object [("kind",.object [("Fun",.object
    [("Regular",.number n)])]),("generics",generics)])]

/-- The installed504 selector ignores the emitted T/destructor specialization.
This includes the actual tuple437/629, Option477, SpawnHooks602 and generic762
sites as well as bool417. It therefore cannot establish arbitrary-T adequacy. -/
theorem set_selected (generics : Data) :
    v2 (token 504 generics) = some .cellBoolSet504 := rfl

/-- Every aggregate replacement fails the current supplied504 projection,
regardless of reference validity, old value or native answer. -/
theorem aggregate_set_unsupported (C : Carrier OWNER Data)
    (values : Values OWNER PV_RJ4IDB.NativeEvent) (s : Store Data) (w : OWNER)
    (generics reference : Data) (fields : List (String × Data))
    (r : Reply OWNER PV_RJ4IDB.NativeEvent Data) :
    interpret C values .cellBoolSet504 (token 504 generics)
      [reference,.object fields] s w r = none := rfl

/-- In contrast, the already documented transparent Cell replacement prefix
performs a DEFINED source write on that SAME aggregate. This is not a proof of
Drop(old T), and the theorem deliberately does not claim whole-call adequacy. -/
theorem aggregate_prefix_defined (C : Carrier OWNER Data) (s : Store Data)
    (w : OWNER) (reference : Data) (fields : List (String × Data)) (a i : Nat)
    (address : C.dereference w reference = some ⟨a,i,[]⟩) :
    PV_LIB_A_CellSourceV2.PV_THR2_LibrarySemantics_CellSetPrefix504
      C [reference,.object fields] s w =
      some (write s ⟨a,i,[]⟩ (some (.object fields))) :=
  PV_LIB_A_StorePrimitiveV2.put_root C s w reference (.object fields) a i address

/-- The incomplete projection replaces even pending/fault/failure answers by
undefined status. The preserved world/events theorem alone cannot assert
full-answer fidelity. No selected write-definedness premise conceals this arm. -/
theorem aggregate_delivery_undefined (C : Carrier OWNER Data)
    (values : Values OWNER PV_RJ4IDB.NativeEvent) (c : Config) (w : OWNER)
    (es : List PV_RJ4IDB.NativeEvent) (stack : List Config)
    (generics reference : Data) (fields : List (String × Data))
    (wait : PV_STX2_Native.Waiting Data) (r : Reply OWNER PV_RJ4IDB.NativeEvent Data) :
    (deliver C values c w es stack
      ⟨.cellBoolSet504,token 504 generics,wait,[reference,.object fields]⟩ r).current.status =
      .undefined none c.store := rfl

/-- Last-reference drop is rejected at the actual count1 branch; no higher
count or no-destructor premise is allowed to stand in for this missing case. -/
theorem last_drop_unsupported (C : Carrier OWNER Data) (args : List Data)
    (s : Store Data) (w : OWNER) (p : Address) (field : Nat)
    (inner : PV_LIB_A_ArcStoreV2.inner C args s w = some p)
    (count : PV_LIB_A_StorePrimitiveV2.numberAt C s
      {p with fields := p.fields ++ [field,0,0]} = some 1) :
    PV_LIB_A_DropStoreV2.nonlast C args s w field = none := by
  unfold PV_LIB_A_DropStoreV2.nonlast
  rw [inner]
  change (PV_LIB_A_StorePrimitiveV2.numberAt C s
    {p with fields := p.fields ++ [field,0,0]}).bind _ = _
  rw [count]
  rfl

/-- A primitive token table has no entry for the installed Thread::clone214,
join168, TLS122, park128, hooks454, collect4 or callback14 wrapper. This is a
checked coverage gap, never a certification that those functions are pure. -/
theorem installed_wrappers_missing (generics : Data) :
    v2 (token 214 generics) = none ∧ v2 (token 168 generics) = none ∧
    v2 (token 122 generics) = none ∧ v2 (token 128 generics) = none ∧
    v2 (token 454 generics) = none ∧ v2 (token 4 generics) = none ∧
    v2 (token 14 generics) = none := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

#print axioms set_selected
#print axioms aggregate_set_unsupported
#print axioms aggregate_prefix_defined
#print axioms aggregate_delivery_undefined
#print axioms last_drop_unsupported
#print axioms installed_wrappers_missing
end PV_LIB_A_ActionAdequacyGap
