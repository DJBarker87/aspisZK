import RPv_FJb_ColumnBound
import RPv_FIw_ArrayReadValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJb_TailStep
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeValue (K)
open FIw_ArrayValue (canonical decoded)
open FJb_MatrixGroupStep (State)
open FJb_ColumnTable (Table)
def columns (sums : Table) (n : Nat) : K :=
  RawPoseidonRowField.decodeWords (fun j=>
    (FJb_TailCell.cell (FJb_TailCell.cell sums ⟨n%4,Nat.mod_lt _ (by decide)⟩) j).val)
theorem column_eq (sums : Table) (i : Usize) : FJb_TailRow.column sums i=columns sums i.val := by
  have he : (⟨(i &&& 3#usize).val,FJb_MaskColumn.bound i⟩ : Fin (4#usize).val)=
      ⟨i.val%4,Nat.mod_lt _ (by decide)⟩ := Fin.ext (FJb_MaskColumn.value i)
  exact congrArg (fun c : Fin (4#usize).val=>RawPoseidonRowField.decodeWords
    (fun j=>(FJb_TailCell.cell (FJb_TailCell.cell sums c) j).val)) he

def step (s : State) (sums : Table) (i : Usize) : Result State := do
  let q ← Array.index_usize s i
  let out ← FJb_TailRow.step q sums i
  Array.update s i out

theorem value (s out : State) (sums : Table) (i : Usize)
    (hi : i.val < (16#usize).val) (hs : canonical s) (hb : FJb_TailCell.Bounded sums)
    (run : step s sums i=ok out) :
    canonical out ∧ decoded out=Function.update (decoded s) ⟨i.val,hi⟩
      (decoded s ⟨i.val,hi⟩+columns sums i.val) := by
  unfold step at run
  obtain ⟨q,hq,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨r,hr,run⟩ := FIv_Map.bind_success _ _ _ run
  have vr := FJb_TailRow.value q r sums i hb hr
  have vu := FIw_ArrayValue.update s out i r hi hs vr.1 run
  refine ⟨vu.1,?_⟩
  rw [vu.2,vr.2,FIw_ArrayReadValue.read s i hi q hq,column_eq]

theorem unfold_loop (s : State) (sums : Table) (i : Usize) :
    state_only_poseidon.external_linear_lazy_loop1 s sums i=
      (if i < poseidon2.POSEIDON2_WIDTH then do
        let next ← step s sums i
        let i1 ← i+1#usize
        state_only_poseidon.external_linear_lazy_loop1 next sums i1
      else ok s) := by
  rw [state_only_poseidon.external_linear_lazy_loop1.eq_def]
  simp only [step,FJb_TailRow.step,bind_assoc_eq]
#print axioms column_eq
#print axioms value
#print axioms unfold_loop
end AspisR1.FJb_TailStep
end
