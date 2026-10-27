import FJb_TailCell
import FJb_RawValue
import FJb_BuilderSelected
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJb_TailRow
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K Canon decode)
open FJb_ColumnTable (Table)
open FJb_TailCell (cell Bounded)
abbrev callback := state_only_poseidon.external_linear_lazy.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU64
def column (sums : Table) (index : Usize) : K :=
  RawPoseidonRowField.decodeWords (fun j=>
    (cell (cell sums ⟨(index &&& 3#usize).val,FJb_MaskColumn.bound index⟩) j).val)
def step (q : NQ) (sums : Table) (index : Usize) : Result NQ := do
  let limbs ← state_only_poseidon.extension_limbs q
  let raw ← array_from_fn_copy 4#usize core.marker.CopyU64 callback 0#u64 (limbs,sums,index)
  state_only_poseidon.extension_from_raw_limbs raw
/-- Exact field addition in the native final external row. -/
theorem value (q out : NQ) (sums : Table) (index : Usize) (hs : Bounded sums)
    (run : step q sums index=ok out) :
    Canon out ∧ decode out=decode q+column sums index := by
  unfold step at run
  obtain ⟨limbs,hl,run⟩ := FIv_Map.bind_success _ _ _ run
  have hl' : FJb_LimbMap.words q=limbs := Result.ok.inj hl
  subst limbs
  obtain ⟨raw,hr,run⟩ := FIv_Map.bind_success _ _ _ run
  have vraw := FJb_RawValue.value raw out run
  have selected := FJb_BuilderSelected.value 4#usize core.marker.CopyU64 callback 0#u64
    (FJb_LimbMap.words q,sums,index) (by
      intro i hi
      obtain ⟨x,hx,_,_⟩ := FJb_TailCell.value (FJb_LimbMap.words q) sums index i hi hs
      exact ⟨x,hx⟩) raw hr
  have hwords : (fun j : Fin (4#usize).val=>(cell raw j).val)=
      (fun j : Fin (4#usize).val=>(cell (FJb_LimbMap.words q) j).val+
        (cell (cell sums ⟨(index &&& 3#usize).val,FJb_MaskColumn.bound index⟩) j).val) := by
    funext j
    let i : Usize := Usize.ofNatCore j.val (lt_trans j.isLt (4#usize).hBounds)
    have vi : i.val=j.val := by simp [i]
    have hi : i.val < (4#usize).val := by rw [vi];exact j.isLt
    have called := selected i hi
    change FJb_TailCell.call (FJb_LimbMap.words q,sums,index) i=
      ok (cell raw ⟨i.val,hi⟩,(FJb_LimbMap.words q,sums,index)) at called
    rw [vi] at called
    obtain ⟨x,hx,hv,_⟩ := FJb_TailCell.value (FJb_LimbMap.words q) sums index i hi hs
    have he : x=cell raw j := (Prod.mk.inj (Result.ok.inj (hx.symm.trans called))).1
    rw [he,vi] at hv
    exact hv
  have hv := vraw.2
  change decode out=RawPoseidonRowField.decodeWords (fun j=>(cell raw j).val) at hv
  rw [hwords,RawPoseidonRowField.decodeWords_add] at hv
  have hq : RawPoseidonRowField.decodeWords (fun j=>(cell (FJb_LimbMap.words q) j).val)=decode q := by rfl
  rw [hq] at hv
  exact ⟨vraw.1,hv⟩
#print axioms value
end AspisR1.FJb_TailRow
end
