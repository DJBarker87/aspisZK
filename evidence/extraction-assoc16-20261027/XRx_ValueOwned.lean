import XRx_ValueRow
import S8OwnedP6Finish
import XRo_Join_Carriers
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
namespace XRx_ValueOwned
def oldQ (q : aspis_core.field.QM31) : S8OwnedP6ValueModel.Q :=
 ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩
/-- Reuse the checked owned reducer, rather than assuming an arithmetic leaf. -/
theorem scalar (x : U64) :
 aspis_core.field.M31.reduce_u64 x=S8OwnedP6.aspis_core.field.M31.reduce_u64 x := by
 obtain ⟨a,ha,hav,_⟩ := XRx_ValueScalar.source x
 obtain ⟨b,hb,hbv,_⟩ := S8OwnedP6ValueModel.reducer_total x
 have eq : a=b := UScalar.eq_of_val_eq (hav.trans hbv.symm)
 rw [ha,hb,eq]

/-- Bounded actual Vec read and all four reducers commute with the owned
value computation on the SAME row. No output-success premise is added. -/
theorem source (b : verifier.BatchedWeights) (i : Usize) (bound : i.val<b.raw.length) :
 XRo_Join_Carriers.mapR oldQ (verifier.BatchedWeights.value b i)=
 S8OwnedP6.value_owned b.raw.val[i.val] := by
 obtain ⟨row,hread,hval⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec b.raw i bound)
 have hr : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice XRu_RowShape.Row) b.raw i=ok row := hread
 obtain ⟨a,c,d,e,shape⟩ := XRu_RowShape.cells row
 obtain ⟨w,hw,_,_⟩ := XRx_ValueScalar.source a
 obtain ⟨x,hx,_,_⟩ := XRx_ValueScalar.source c
 obtain ⟨y,hy,_,_⟩ := XRx_ValueScalar.source d
 obtain ⟨z,hz,_,_⟩ := XRx_ValueScalar.source e
 have hw' := (scalar a).symm.trans hw
 have hx' := (scalar c).symm.trans hx
 have hy' := (scalar d).symm.trans hy
 have hz' := (scalar e).symm.trans hz
 rw [←hval,shape]
 unfold verifier.BatchedWeights.value
 rw [hr,bind_tc_ok,shape,XRx_ValueRow.map a c d e w x y z hw hx hy hz,bind_tc_ok]
 change ok (⟨⟨w,x⟩,⟨y,z⟩⟩ : S8OwnedP6ValueModel.Q) = (do
  let m0 ← S8OwnedP6.aspis_core.field.M31.reduce_u64 a
  let m1 ← S8OwnedP6.aspis_core.field.M31.reduce_u64 c
  let m2 ← S8OwnedP6.aspis_core.field.M31.reduce_u64 d
  let m3 ← S8OwnedP6.aspis_core.field.M31.reduce_u64 e
  ok (⟨⟨m0,m1⟩,⟨m2,m3⟩⟩ : S8OwnedP6ValueModel.Q))
 rw [hw',bind_tc_ok,hx',bind_tc_ok,hy',bind_tc_ok,hz']
 rfl

#print axioms scalar
#print axioms source
end XRx_ValueOwned
