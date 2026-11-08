import PV_LIB_A_UnwindMatch
set_option autoImplicit false
namespace PV_LIB_A_UnwindReplies
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_LIB_A_UnwindMatch

theorem read_fields {W : Type} (C : Carrier W Data) (K : Control)
    (fields : List Nat) (value : Data) :
    readFields (carrier C K) fields value = readFields C fields value := by
  induction fields generalizing value with
  | nil => rfl
  | cons head tail ih => simp only [readFields,ih] <;> rfl

theorem replace_fields {W : Type} (C : Carrier W Data) (K : Control)
    (fields : List Nat) (value : Data) (replacement : Option Data) :
    replaceFields (carrier C K) fields replacement value = replaceFields C fields replacement value := by
  induction fields generalizing value with
  | nil => rfl
  | cons head tail ih =>
    cases tail with
    | nil => rfl
    | cons second rest => simp only [replaceFields,ih] <;> rfl

theorem read_address {W : Type} (C : Carrier W Data) (K : Control)
    (s : Store Data) (p : Address) :
    readAddress (carrier C K) s p = readAddress C s p := by
  simp only [readAddress,read_fields]

theorem write_address {W : Type} (C : Carrier W Data) (K : Control)
    (s : Store Data) (p : Address) (replacement : Option Data) :
    writeAddress (carrier C K) s p replacement = writeAddress C s p replacement := by
  cases fields : p.fields <;> simp only [writeAddress,fields,replace_fields]

theorem read_place {W : Type} (C : Carrier W Data) (K : Control)
    (s : Store Data) (w : W) (a : Nat) (p : Place) :
    read (carrier C K) s w a p = read C s w a p := by
  induction p with
  | «local» n => rfl
  | «global» n => rfl
  | project p projection ih =>
    cases projection <;> simp only [PV_STX2_Store.read,ih,read_address] <;> rfl

theorem locate_place {W : Type} (C : Carrier W Data) (K : Control)
    (s : Store Data) (w : W) (a : Nat) (p : Place) :
    locate (carrier C K) s w a p = locate C s w a p := by
  induction p with
  | «local» n => rfl
  | «global» n => rfl
  | project p projection ih =>
    cases projection <;> simp only [locate,ih,read_place] <;> rfl

theorem store_result {W : Type} (C : Carrier W Data) (K : Control)
    (c : PV_STX2_Native.Config Data) (w : W) (action : PV_STX2_Native.ReturnAction) (value : Data) :
    PV_STX2_Native.storeResult (carrier C K) c w action value =
      PV_STX2_Native.storeResult C c w action value := by
  cases action <;> simp only [PV_STX2_Native.storeResult,locate_place,write_address]

/-- EVERY full native answer is unchanged by the cleanup carrier extension,
including its exact store update, failure/divergence, pending and panic policy.
No caller frame law, event restriction or success hypothesis is introduced. -/
theorem full_reply {W E : Type} (C : Carrier W Data) (K : Control)
    (c : PV_STX2_Native.Config Data) (wait : PV_STX2_Native.Waiting Data) (r : Reply W E Data) :
    PV_STX2_Pinned.reply (carrier C K) c wait r = PV_STX2_Pinned.reply C c wait r := by
  unfold PV_STX2_Pinned.reply PV_STX2_Native.reply
  simp only [store_result]

#print axioms read_fields
#print axioms replace_fields
#print axioms read_address
#print axioms write_address
#print axioms read_place
#print axioms locate_place
#print axioms store_result
#print axioms full_reply
end PV_LIB_A_UnwindReplies
