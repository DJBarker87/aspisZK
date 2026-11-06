import NJQ_Library
import NJQ_Read
set_option autoImplicit false
noncomputable section
namespace NJQ_Reserved
open Aeneas Aeneas.Std Result
open NJI_Extracted.aspis_statement.pool_v1.pair_forest_accounts
attribute [local instance] Classical.propDecidable
abbrev CP := decode_pool_v1_pair_forest_checkpoint_v1.closure.Insts.CoreOpsFunctionFnMutTupleSharedU8Bool
abbrev MP := decode_pool_v1_pair_forest_master_v1.closure.Insts.CoreOpsFunctionFnMutTupleSharedU8Bool

theorem checkpoint_callback (c : decode_pool_v1_pair_forest_checkpoint_v1.closure) (x : U8) :
 CP.call_mut c x=ok (x != 0#u8,c) := rfl

theorem master_callback (c : decode_pool_v1_pair_forest_master_v1.closure) (x : U8) :
 MP.call_mut c x=ok (x != 0#u8,c) := rfl

theorem any_zero (xs : List U8) :
 xs.any (fun x=>x != 0#u8)=false ↔ xs=List.replicate xs.length 0#u8 := by
 rw [←NHY_AllZeroBridge.list_zero]
 constructor
 · intro h x member
   have hx := List.any_eq_false.mp h x member
   by_contra ne
   have hit : (x != 0#u8)=true := by simpa using ne
   rw [hit] at hx
   contradiction
 · intro h
   apply List.any_eq_false.mpr
   intro x member
   rw [h x member]
   simp

theorem complement (xs : List U8) :
 xs.any (fun x=>x != 0#u8) = !(decide (xs=List.replicate xs.length 0#u8)) := by
 cases h : xs.any (fun x=>x != 0#u8) with
 | false =>
   have zero := (any_zero xs).mp h
   simp only [h,decide_eq_true zero,Bool.not_true]
 | true =>
   have nonzero : xs≠List.replicate xs.length 0#u8 := by
    intro zero
    have no := (any_zero xs).mpr zero
    rw [h] at no
    contradiction
   simp only [h,decide_eq_false nonzero,Bool.not_false]

def checkpoint (b : Slice U8) : Result Bool := do
 let (answer,_) ← NJQ_Library.any CP {slice:=b,i:=0} ()
 ok answer

def master (b : Slice U8) : Result Bool := do
 let (answer,_) ← NJQ_Library.any MP {slice:=b,i:=0} ()
 ok answer

theorem checkpoint_value (b : Slice U8) :
 checkpoint b=ok (!(decide (b.val=List.replicate b.val.length 0#u8))) := by
 rw [checkpoint,NJQ_Library.pure_value CP (fun x=>x != 0#u8) checkpoint_callback]
 simp only [List.drop_zero,complement]

theorem master_value (b : Slice U8) :
 master b=ok (!(decide (b.val=List.replicate b.val.length 0#u8))) := by
 rw [master,NJQ_Library.pure_value MP (fun x=>x != 0#u8) master_callback]
 simp only [List.drop_zero,complement]

#print axioms checkpoint_callback
#print axioms master_callback
#print axioms any_zero
#print axioms complement
#print axioms checkpoint_value
#print axioms master_value
end NJQ_Reserved
