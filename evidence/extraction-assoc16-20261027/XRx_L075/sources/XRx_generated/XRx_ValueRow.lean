import XRx_ValueScalar
import XRu_RowShape
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace XRx_ValueRow
/-- Array mapping is sequenced over precisely the four cells of THIS row. -/
theorem map (a b c d : U64) (w x y z : U32)
 (ha : aspis_core.field.M31.reduce_u64 a=ok w)
 (hb : aspis_core.field.M31.reduce_u64 b=ok x)
 (hc : aspis_core.field.M31.reduce_u64 c=ok y)
 (hd : aspis_core.field.M31.reduce_u64 d=ok z) :
 core.array.Array.map (BuiltinFnMut U64 aspis_core.field.M31)
  (Array.make 4#usize [a,b,c,d]) aspis_core.field.M31.reduce_u64 =
 ok (Array.make 4#usize [w,x,y,z]) := by
 simp +zeta +zetaDelta +zetaHave +iota only [core.array.Array.map,
  Array.make,core.array.mapListFnMut,BuiltinFnMut,ha,hb,hc,hd,bind_tc_ok]
 rfl

/-- Exact successful value equation: the actual Vec read and reductions,
with no independently supplied successful value. -/
theorem source (bw : verifier.BatchedWeights) (i : Usize)
 (bound : i.val<bw.raw.length) :
 ∃ a b c d : U64, ∃ w x y z : U32,
 bw.raw.val[i.val]=Array.make 4#usize [a,b,c,d] ∧
 verifier.BatchedWeights.value bw i=ok (⟨⟨w,x⟩,⟨y,z⟩⟩ : aspis_core.field.QM31) ∧
 w.val=a.val%2147483647 ∧ x.val=b.val%2147483647 ∧
 y.val=c.val%2147483647 ∧ z.val=d.val%2147483647 := by
 obtain ⟨row,hread,hval⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec bw.raw i bound)
 have hr : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice XRu_RowShape.Row) bw.raw i=ok row := hread
 obtain ⟨a,b,c,d,shape⟩ := XRu_RowShape.cells row
 obtain ⟨w,hw,hwm,_⟩ := XRx_ValueScalar.source a
 obtain ⟨x,hx,hxm,_⟩ := XRx_ValueScalar.source b
 obtain ⟨y,hy,hym,_⟩ := XRx_ValueScalar.source c
 obtain ⟨z,hz,hzm,_⟩ := XRx_ValueScalar.source d
 refine ⟨a,b,c,d,w,x,y,z,?_,?_,hwm,hxm,hym,hzm⟩
 · rw [←hval];exact shape
 · unfold verifier.BatchedWeights.value
   rw [hr,bind_tc_ok,shape,map a b c d w x y z hw hx hy hz,bind_tc_ok]
   rfl
#print axioms map
#print axioms source
end XRx_ValueRow
