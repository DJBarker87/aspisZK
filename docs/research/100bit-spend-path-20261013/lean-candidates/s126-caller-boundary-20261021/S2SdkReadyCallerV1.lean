import S2SdkReadyStateV1
import S126SdkAccountImageExportV1
import S2SdkKeyEqualityV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisS2OwnedStage1.SdkReference.ReadyCaller
open ReadyState

local instance {T : Type} [DecidableEq T] {n : Usize} : DecidableEq (Array T n) :=
  inferInstanceAs (DecidableEq { xs : List T // xs.length=n.val })

/-- Necessary accepted-native metadata class, on the SAME full record types.
Keys, owners of readonly inputs, rent and lamports slots are unchanged. -/
def readonlyMeta (account : OwnedAccount) (slot : Usize) : OwnedAccount :=
  {account with is_signer:=false,is_writable:=false,executable:=false,data_slot:=slot}

def checkpointMeta (program : Array U8 32#usize) (account : OwnedAccount) : OwnedAccount :=
  {account with owner:=program,is_signer:=false,is_writable:=true,executable:=false,data_slot:=2#usize}

def accounts3 (program : Array U8 32#usize) (p u c : OwnedAccount) : alloc.vec.Vec OwnedAccount :=
  triple (readonlyMeta p 0#usize) (readonlyMeta u 1#usize) (checkpointMeta program c)

def initialSdk (program : Array U8 32#usize) (p u c : OwnedAccount)
    (lamports : alloc.vec.Vec OwnedLamportsCell) (proof pubCell cpCell : OwnedDataCell) : OwnedSdk :=
  state (accounts3 program p u c) lamports proof pubCell {cpCell with borrowed:=0#isize}

def splitByte (ten : Bool) : U8 := if ten then 10#u8 else 11#u8

def splitIndex (ten : Bool) : Usize := if ten then 10#usize else 11#usize

def instruction (ten : Bool) : alloc.vec.Vec U8 :=
  ⟨[3#u8,splitByte ten],by scalar_tac⟩

theorem instruction_ten (ten : Bool) :
    Installation.stdSliceArrayEq core.cmp.PartialEqU8 (alloc.vec.Vec.deref (instruction ten))
      (Array.make 2#usize [3#u8,10#u8])=ok ten := by
  cases ten <;> rfl

theorem instruction_eleven (ten : Bool) :
    Installation.stdSliceArrayEq core.cmp.PartialEqU8 (alloc.vec.Vec.deref (instruction ten))
      (Array.make 2#usize [3#u8,11#u8])=ok (!ten) := by
  cases ten <;> rfl

theorem instruction_read (ten : Bool) :
    Slice.index_usize (alloc.vec.Vec.deref (instruction ten)) 1#usize=ok (splitByte ten) := by
  simp [instruction,alloc.vec.Vec.deref,Slice.index_usize]

theorem instruction_cast (ten : Bool) :
    (lift (UScalar.cast .Usize (splitByte ten)) : Result Usize)=ok (splitIndex ten) := by
  simp only [lift]
  congr 1
  apply UScalar.eq_of_val_eq
  rw [U8.cast_Usize_val_eq]
  cases ten <;> rfl


theorem key_eq_false (a b : Array U8 32#usize) (different : a≠b) :
    core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 a b=ok false := by
  rw [AspisS2SdkKeyEquality.array_eq_value core.cmp.PartialEqU8
    AspisS2SdkKeyEquality.u8_ne_spec]
  simp only [different,decide_false]

theorem owner_ne_self (a : Array U8 32#usize) :
    core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8 a a=ok false := by
  rw [AspisS2SdkKeyEquality.array_ne_value core.cmp.PartialEqU8
    AspisS2SdkKeyEquality.u8_ne_spec]
  simp only [ne_eq,not_true_eq_false,decide_false]

#print axioms instruction_ten
#print axioms instruction_eleven
#print axioms instruction_read
#print axioms instruction_cast
#print axioms key_eq_false
#print axioms owner_ne_self
end AspisS2OwnedStage1.SdkReference.ReadyCaller
