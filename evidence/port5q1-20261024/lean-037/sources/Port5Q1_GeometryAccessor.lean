import Port5Q1_GeometryReads
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port5Q1_GeometryAccessor
open Aeneas Aeneas.Std Result AspisR1Stage2
open Port5Q1_GeometryBinding
attribute [local irreducible] Port5Q1_Domain.words Port5Q1_Domain.lineZ

theorem offset (i start : Usize) (order : start.val≤i.val) :
    (Usize.wrapping_sub i start).val=i.val-start.val := by
  have ib : i.val<UScalar.size .Usize := by rw [UScalar.size_def]; exact i.bv.isLt
  have sb : start.val<UScalar.size .Usize := by rw [UScalar.size_def]; exact start.bv.isLt
  rw [Usize.wrapping_sub_val_eq,
    show i.val+(UScalar.size .Usize-start.val)=UScalar.size .Usize+(i.val-start.val) by omega,
    Nat.add_mod,Nat.mod_self,Nat.zero_add,Nat.mod_mod,Nat.mod_eq_of_lt (by omega)]

/-- Both actual native reads select the SAME query in the SAME returned
geometry. No fresh inverse array or independently successful read is chosen. -/
theorem reads (queries : Array U32 22#usize) (start end1 : Usize)
    (geometry : verifier.QueryGeometry) (binding : Binding queries start end1 geometry)
    (i : Usize) (lo : start.val≤i.val) (hi : i.val<end1.val)
    (inverse : Array U32 5#usize) (z : U32)
    (inverseRead : forQuery geometry i=ok inverse)
    (zRead : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice U32)
      geometry.line_z (Usize.wrapping_sub i geometry.start)=ok z) :
    S7JoinBasisMachine.decode z=Port5Q1_Domain.lineZ (queryAt queries i.val).val ∧
    (∀ j : Fin 5, S7JoinBasisMachine.decode (lane inverse j)=
      ((Port5Q1_Domain.words (queryAt queries i.val).val)[j.val]?.getD 0)⁻¹) := by
  have ov : (Usize.wrapping_sub i geometry.start).val=i.val-start.val := by
    rw [binding.start_eq,offset i start lo]
  have localBound : i.val-start.val<end1.val-start.val := by omega
  obtain ⟨actual,run,contents⟩ := WP.spec_imp_exists
    (alloc.vec.Vec.index_usize_spec geometry.line_z (Usize.wrapping_sub i geometry.start)
      (by change (Usize.wrapping_sub i geometry.start).val<geometry.line_z.val.length; rw [ov,binding.line_size]; exact localBound))
  have same : actual=z := Result.ok.inj (run.symm.trans zRead)
  subst actual
  have zCell : geometry.line_z.val[i.val-start.val]?.getD 0#u32=z := by
    rw [List.getElem?_eq_getElem (by rw [binding.line_size]; exact localBound),Option.getD_some]
    simpa only [ov] using contents.symm
  obtain ⟨actual,run,contents⟩ := WP.spec_imp_exists
    (alloc.vec.Vec.index_usize_spec geometry.inverses (Usize.wrapping_sub i geometry.start)
      (by change (Usize.wrapping_sub i geometry.start).val<geometry.inverses.val.length; rw [ov,binding.inverse_size]; exact localBound))
  have same : actual=inverse := Result.ok.inj (run.symm.trans inverseRead)
  subst actual
  have iCell : geometry.inverses.val[i.val-start.val]?.getD
      (Array.make 5#usize [0#u32,0#u32,0#u32,0#u32,0#u32])=inverse := by
    rw [List.getElem?_eq_getElem (by rw [binding.inverse_size]; exact localBound),Option.getD_some]
    simpa only [ov] using contents.symm
  have indexEq : start.val+(i.val-start.val)=i.val := by omega
  constructor
  · have hz := binding.line (i.val-start.val) localBound
    rw [zCell,indexEq] at hz
    exact hz
  · intro j
    have hx := binding.inverses (i.val-start.val) localBound j
    rw [iCell,indexEq] at hx
    exact hx

#print axioms offset
#print axioms reads
end AspisR1.Port5Q1_GeometryAccessor
end
