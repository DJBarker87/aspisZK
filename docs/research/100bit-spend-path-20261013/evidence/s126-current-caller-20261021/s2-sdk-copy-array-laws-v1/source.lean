import S2SdkCopyStepTotalV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisS2OwnedStage1.SdkReference.CopyLoop

theorem replace_length (sdk : OwnedSdk) (slot : Usize) (cell : OwnedDataCell)
    (bytes : alloc.vec.Vec U8) :
    (replaceBytes sdk slot cell bytes).data_cells.val.length=sdk.data_cells.val.length := by
  simp [replaceBytes,alloc.vec.Vec.set]

theorem replace_cell (sdk : OwnedSdk) (slot : Usize) (cell : OwnedDataCell)
    (bytes : alloc.vec.Vec U8) (valid : slot.val<sdk.data_cells.val.length) :
    (replaceBytes sdk slot cell bytes).data_cells.val[slot.val]'(by
      simpa only [replace_length] using valid)={cell with bytes:=bytes} := by
  simp [replaceBytes,alloc.vec.Vec.set]

theorem replace_same (sdk : OwnedSdk) (slot : Usize) (cell : OwnedDataCell)
    (valid : slot.val<sdk.data_cells.val.length)
    (actual : cell=sdk.data_cells.val[slot.val]) :
    replaceBytes sdk slot cell cell.bytes=sdk := by
  have row : {cell with bytes:=cell.bytes}=cell := by cases cell; rfl
  have set : alloc.vec.Vec.set sdk.data_cells slot cell=sdk.data_cells := by
    apply Subtype.ext
    simpa only [alloc.vec.Vec.set,actual] using List.set_getElem_self valid
  simp only [replaceBytes,row,set]

theorem replace_twice (sdk : OwnedSdk) (slot : Usize) (cell : OwnedDataCell)
    (before after : alloc.vec.Vec U8) :
    replaceBytes (replaceBytes sdk slot cell before) slot {cell with bytes:=before} after=
      replaceBytes sdk slot cell after := by
  simp [replaceBytes,alloc.vec.Vec.set]

def PrefixEq (bytes source : alloc.vec.Vec U8) (copied : Nat) : Prop :=
  ∀ j, j<copied → bytes.val[j]?=source.val[j]?

theorem prefix_step (bytes source : alloc.vec.Vec U8) (offset : Usize)
    (sameLength : bytes.val.length=source.val.length)
    (range : offset.val<source.val.length) (prefix : PrefixEq bytes source offset.val)
    (byte : U8) (which : byte=source.val[offset.val]) :
    PrefixEq (alloc.vec.Vec.set bytes offset byte) source (offset.val+1) := by
  intro j hj
  by_cases equal : j=offset.val
  · subst j
    have target : offset.val<bytes.val.length := by omega
    simp only [alloc.vec.Vec.set,List.getElem?_set_self target,
      List.getElem?_eq_getElem range,which]
  · have before : j<offset.val := by omega
    have different : offset.val≠j := Ne.symm equal
    simpa only [alloc.vec.Vec.set,List.getElem?_set_ne different] using prefix j before

theorem prefix_complete (bytes source : alloc.vec.Vec U8)
    (sameLength : bytes.val.length=source.val.length)
    (prefix : PrefixEq bytes source source.val.length) : bytes=source := by
  apply Subtype.ext
  apply List.ext_getElem sameLength
  intro j hb hs
  have selected := prefix j hs
  rw [List.getElem?_eq_getElem hb,List.getElem?_eq_getElem hs] at selected
  exact Option.some.inj selected

theorem increment_total (offset : Usize) (source : Slice U8)
    (range : offset.val<source.val.length) :
    ∃ next : Usize, (offset+1#usize : Result Usize)=ok next ∧ next.val=offset.val+1 := by
  apply spec_imp_exists
  apply UScalar.add_spec
  rw [UScalar.max_USize_eq]
  have bound := source.property
  omega

#print axioms replace_cell
#print axioms replace_same
#print axioms replace_twice
#print axioms prefix_step
#print axioms prefix_complete
#print axioms increment_total
end AspisS2OwnedStage1.SdkReference.CopyLoop
