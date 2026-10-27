import FJf_ArraySlots
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJf_FactorArray
open Aeneas Aeneas.Std Result
open FJc_WeightQMBridge (SQ)
open FJf_PointBody (Factors)
abbrev Row := Array (Array SQ 4#usize) 5#usize
abbrev K := OraclePortCheckpointAbiC5.K

def rowCanon (r : Row) : Prop := ∀ a∈r.val,FJc_WeightArray.canonical a
def canon (f : Factors) : Prop := ∀ r∈f.val,rowCanon r

def rowValue (r : Row) (d s : Nat) : K :=
  match r.val[d]? with
  | some a => FJc_WeightArray.value a s
  | none => 0

def value (f : Factors) (k d s : Nat) : K :=
  match f.val[k]? with
  | some r => rowValue r d s
  | none => 0

theorem row_read (f : Factors) (k : Usize) (r : Row)
    (run : Array.index_usize f k=ok r) (d s : Nat) :
    value f k.val d s=rowValue r d s := by
  simp only [value,FJc_ReadSlot.slot _ _ _ run]

theorem row_update (a b : Row) (i : Usize) (x : Array SQ 4#usize)
    (run : Array.update a i x=ok b) (d s : Nat) :
    rowValue b d s=if i.val=d then FJc_WeightArray.value x s else rowValue a d s := by
  unfold rowValue
  rw [FJf_ArraySlots.update_slot a b i x run d]
  split <;> rfl

theorem outer_set (f : Factors) (i : Usize) (old x : Row)
    (run : Array.index_usize f i=ok old) (k d s : Nat) :
    value (f.set i x) k d s=if i.val=k then rowValue x d s else value f k d s := by
  have hi : i.val<f.val.length := (List.getElem_of_getElem? (FJc_ReadSlot.slot _ _ _ run)).choose
  unfold value
  rw [FJf_ArraySlots.set_slot f i x hi k]
  split <;> rfl

theorem row_update_canon (a b : Row) (i : Usize) (x : Array SQ 4#usize)
    (ha : rowCanon a) (hx : FJc_WeightArray.canonical x)
    (run : Array.update a i x=ok b) : rowCanon b := by
  unfold rowCanon
  rw [FJf_ArrayOps.update_val a b i x run]
  exact FIo_ArrayCanon.list_set FJc_WeightArray.canonical _ _ x ha hx

theorem outer_set_canon (f : Factors) (i : Usize) (x : Row)
    (hf : canon f) (hx : rowCanon x) : canon (f.set i x) := by
  unfold canon
  rw [FJf_ArrayOps.set_val]
  exact FIo_ArrayCanon.list_set rowCanon _ _ x hf hx

#print axioms row_read
#print axioms row_update
#print axioms outer_set
#print axioms row_update_canon
#print axioms outer_set_canon
end AspisR1.FJf_FactorArray
end
