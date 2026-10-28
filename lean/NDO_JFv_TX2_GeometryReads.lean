import NDO_JFv_TX2_Geometry
import NDO_JFv_TX2_GatherCells
import Port5Q1_GeometryAccessor
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFv_TX2_GeometryReads
open Aeneas Aeneas.Std Result AspisR1Stage2
open Port3_NativeGeometryBody

def cursor (i : Fin 12) : Usize := Usize.ofNat (10+i.val) (by have:=i.isLt;scalar_tac)

theorem source {C : Type} (err : C) (seed : Ops C) (i : Fin 12) :
    ∃ inverse : Array U32 5#usize,
      Port5Q1_GeometryBinding.forQuery (JFv_TX2_Geometry.value err seed) (cursor i)=ok inverse ∧
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice U32)
        (JFv_TX2_Geometry.value err seed).line_z
        (Usize.wrapping_sub (cursor i) (JFv_TX2_Geometry.value err seed).start)=ok (JFv_TX2_Rows.value i).lineZ ∧
      ∀ j : Fin 5, S7JoinBasisMachine.decode (Port5Q1_GeometryBinding.lane inverse j)=
        (S7JoinBasisMachine.decode ((JFv_TX2_Rows.value i).words[j.val]?.getD 0#u32))⁻¹ := by
  let g := JFv_TX2_Geometry.value err seed
  obtain ⟨start,line,inv,len,values,groups⟩ := JFv_TX2_Geometry.meaning err seed
  have offset : (Usize.wrapping_sub (cursor i) g.start).val=i.val := by
    rw [start,Port5Q1_GeometryAccessor.offset _ _ (by change 10≤10+i.val;omega)]
    change 10+i.val-10=i.val
    omega
  have ilen : g.inverses.val.length=12 := by rw [groups,List.length_map,List.length_range]
  have zlen : g.line_z.val.length=12 := by rw [line];exact (JFv_TX2_GatherShape.lengths 12).1
  obtain ⟨inverse,ir,iv⟩ := WP.spec_imp_exists
    (alloc.vec.Vec.index_usize_spec g.inverses (Usize.wrapping_sub (cursor i) g.start)
      (by change _<g.inverses.val.length;rw [offset,ilen];exact i.isLt))
  obtain ⟨z,zr,zv⟩ := WP.spec_imp_exists
    (alloc.vec.Vec.index_usize_spec g.line_z (Usize.wrapping_sub (cursor i) g.start)
      (by change _<g.line_z.val.length;rw [offset,zlen];exact i.isLt))
  have isame : inverse=Port4C_CollectLoop.record inv i.val := by
    have iv1 : inverse=g.inverses.val[i.val]'(by rw [ilen];exact i.isLt) := by
      simpa only [offset] using iv
    have hc : g.inverses.val[i.val]?=some inverse := by
      rw [List.getElem?_eq_getElem (by rw [ilen];exact i.isLt)]
      exact congrArg some iv1.symm
    rw [groups,List.getElem?_map,List.getElem?_range i.isLt] at hc
    exact Option.some.inj hc.symm
  have zsame : z=(JFv_TX2_Rows.value i).lineZ := by
    have cell : g.line_z.val[i.val]?.getD 0#u32=z := by
      rw [List.getElem?_eq_getElem (by rw [zlen];exact i.isLt),Option.getD_some]
      simpa only [offset] using zv.symm
    rw [line,JFv_TX2_GatherCells.node] at cell
    exact cell.symm
  refine ⟨inverse,ir,zsame ▸ zr,?_⟩
  intro j
  rw [isame,Port5Q1_GeometryBinding.lane,Port5Q1_ListCells.record_cell,
    values (5*i.val+j.val) (by have:=i.isLt;have:=j.isLt;omega),JFv_TX2_GatherCells.flat]
#print axioms source
end AspisR1.JFv_TX2_GeometryReads
end
