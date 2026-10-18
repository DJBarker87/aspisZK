import PoseidonExternalColumnCallV21
import PoseidonRaw4Constructor
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
namespace AspisR1.PoseidonExternalColumnArrayCall
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.PoseidonExternalColumnCall
abbrev State := Array field.QM31 16#usize
abbrev ColumnClosure := state_only_poseidon.external_linear_lazy.closure
abbrev InnerClosure := state_only_poseidon.external_linear_lazy.closure.closure
abbrev U32 := Std.U32
abbrev U64 := Std.U64

def columnTotal (state : State) (column : Usize) (hcolumn : column.val < 4) (j : Fin 4) (v : U64) : Prop :=
  let limb : Usize := UScalar.ofNatCore j.val (by scalar_tac)
  v.val = sumFour
    (limbAt (state.val[column.val]'(by have := hcolumn; scalar_tac)) limb j.isLt)
    (limbAt (state.val[4+column.val]'(by have := hcolumn; scalar_tac)) limb j.isLt)
    (limbAt (state.val[8+column.val]'(by have := hcolumn; scalar_tac)) limb j.isLt)
    (limbAt (state.val[12+column.val]'(by have := hcolumn; scalar_tac)) limb j.isLt)

theorem external_column_array_call (state : State) (column : Usize)
    (hcolumn : column.val < 4) :
    ∃ out : Array U64 4#usize,
      state_only_poseidon.external_linear_lazy.closure.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU644.call_mut
        state column = .ok (out,state) ∧
      ∀ j : Fin 4, columnTotal state column hcolumn j (AspisR1.PoseidonFullRoundCellStep.cell out j) := by
  let inst := state_only_poseidon.external_linear_lazy.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64
  let c : InnerClosure := (state,column)
  have hcall : ∀ (i : Usize) (hi : i.val < 4), ∃ v : U64,
      inst.call_mut c i = .ok (v,c) ∧ columnTotal state column hcolumn ⟨i.val,hi⟩ v := by
    intro i hi
    obtain ⟨v,hv,hm⟩ := external_column_limb_call state column i hcolumn hi
    let j : Fin 4 := ⟨i.val,hi⟩
    have hidx : (UScalar.ofNatCore j.val (by scalar_tac) : Usize) = i := by
      apply UScalar.eq_of_val_eq
      simp [j]
    refine ⟨v,hv,?_⟩
    change v.val = sumFour
      (limbAt (state.val[column.val]'(by have := hcolumn; scalar_tac))
        (UScalar.ofNatCore j.val (by scalar_tac)) j.isLt)
      (limbAt (state.val[4+column.val]'(by have := hcolumn; scalar_tac))
        (UScalar.ofNatCore j.val (by scalar_tac)) j.isLt)
      (limbAt (state.val[8+column.val]'(by have := hcolumn; scalar_tac))
        (UScalar.ofNatCore j.val (by scalar_tac)) j.isLt)
      (limbAt (state.val[12+column.val]'(by have := hcolumn; scalar_tac))
        (UScalar.ofNatCore j.val (by scalar_tac)) j.isLt)
    cases hidx
    exact hm
  obtain ⟨out,hcopy,hcells⟩ := AspisR1.PoseidonRaw4Constructor.source_success inst c
      (columnTotal state column hcolumn) hcall
  refine ⟨out, ?_, hcells⟩
  have houter :
      state_only_poseidon.external_linear_lazy.closure.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU644.call_mut
        state column = (do
          let a ← array_from_fn_copy 4#usize core.marker.CopyU64 inst 0#u64 c
          ok (a,state)) := by
    unfold state_only_poseidon.external_linear_lazy.closure.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU644.call_mut
    rfl
  rw [houter,hcopy]
  rfl

#print axioms external_column_array_call
end AspisR1.PoseidonExternalColumnArrayCall
