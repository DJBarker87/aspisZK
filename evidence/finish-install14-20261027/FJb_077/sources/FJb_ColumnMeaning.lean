import FJb_ColumnWords
import FJb_MatrixModel
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJb_ColumnMeaning
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeValue (K decode)
open FJb_MatrixGroupStep (State)
open FJb_MatrixModel (Values sample)
open FJb_ColumnTable (Table callback)
open FJb_TailCell (cell)
open FJb_WordAt (q)
def sum (v : Values) (c : Nat) : K :=
  sample v c+sample v (4+c)+sample v (8+c)+sample v (12+c)

theorem q_value (s : State) (c r : Fin (4#usize).val) :
    decode (q s c r)=sample (FIw_ArrayValue.decoded s) (4*r.val+c.val) := by
  have hb : 4*r.val+c.val < (16#usize).val := by
    have hc : c.val < 4 := c.isLt
    have hr : r.val < 4 := r.isLt
    change 4*r.val+c.val < 16
    omega
  have hv := FJb_MatrixModel.at_value s (4*r.val+c.val)
  unfold FIv_NativeArray.value at hv
  rw [List.getElem?_eq_getElem (by simpa only [s.property] using hb)] at hv
  exact hv

/-- Wordwise sums are transported into the EXACT field on the same native table. -/
theorem value (s : State) (sums : Table)
    (run : array_from_fn_copy 4#usize (Array.Insts.CoreMarkerCopy 4#usize core.marker.CopyU64)
      callback (Array.repeat 4#usize 0#u64) s=ok sums) (c : Fin (4#usize).val) :
    RawPoseidonRowField.decodeWords (fun j=>(cell (cell sums c) j).val)=
      decode (q s c ⟨0,by decide⟩)+decode (q s c ⟨1,by decide⟩)+decode (q s c ⟨2,by decide⟩)+decode (q s c ⟨3,by decide⟩) := by
  let f0 : Fin 4 → Nat := FJb_ColumnWords.words s c ⟨0,by decide⟩
  let f1 : Fin 4 → Nat := FJb_ColumnWords.words s c ⟨1,by decide⟩
  let f2 : Fin 4 → Nat := FJb_ColumnWords.words s c ⟨2,by decide⟩
  let f3 : Fin 4 → Nat := FJb_ColumnWords.words s c ⟨3,by decide⟩
  have hd : RawPoseidonRowField.decodeWords (fun j=>(cell (cell sums c) j).val)=
      RawPoseidonRowField.decodeWords (fun j=>f0 j+f1 j+f2 j+f3 j) :=
    congrArg RawPoseidonRowField.decodeWords (FJb_ColumnWords.value s sums run c)
  rw [RawPoseidonRowField.decodeWords_add,RawPoseidonRowField.decodeWords_add,
    RawPoseidonRowField.decodeWords_add] at hd
  exact hd

theorem meaning (s : State) (sums : Table)
    (run : array_from_fn_copy 4#usize (Array.Insts.CoreMarkerCopy 4#usize core.marker.CopyU64)
      callback (Array.repeat 4#usize 0#u64) s=ok sums) (n : Nat) :
    FJb_TailStep.columns sums n=sum (FIw_ArrayValue.decoded s) (n%4) := by
  have hv := value s sums run ⟨n%4,Nat.mod_lt _ (by decide)⟩
  rw [q_value,q_value,q_value,q_value] at hv
  exact hv
#print axioms q_value
#print axioms value
#print axioms meaning
end AspisR1.FJb_ColumnMeaning
end
