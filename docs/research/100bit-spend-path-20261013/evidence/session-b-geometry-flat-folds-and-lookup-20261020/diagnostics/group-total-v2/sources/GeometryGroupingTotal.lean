import GeometryGroupingIndex
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1GeometryGrouping.Proof
open alloc.vec

def groupedWord (flat : Vec M31) (i j : Usize) : M31 :=
  flat.val.getD (5*i.val+j.val) 0#u32

theorem grouping_callback_total (flat : Vec M31) (i j : Usize)
    (hb : 5*i.val+j.val < flat.val.length) :
    geometry_groups.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeM31.call_mut
      (flat,i) j = .ok (groupedWord flat i j,(flat,i)) := by
  have hmBound : 5*i.val ≤ Usize.max := by have hf := flat.property; omega
  have hm : (5#usize*i : Result Usize) ⦃p => p.val=5*i.val⦄ := by
    apply UScalar.mul_spec
    simpa only [UScalar.max_USize_eq,UScalar.ofNatCore_val_eq] using hmBound
  obtain ⟨product,hmul,hprod⟩ := WP.spec_imp_exists hm
  have haBound : product.val+j.val ≤ Usize.max := by have hf := flat.property; omega
  have ha : (product+j : Result Usize) ⦃p => p.val=product.val+j.val⦄ := by
    apply UScalar.add_spec
    simpa only [UScalar.max_USize_eq] using haBound
  obtain ⟨index,hadd,hindex⟩ := WP.spec_imp_exists ha
  have hi : index.val=5*i.val+j.val := by omega
  have hidxBound : index.val<flat.val.length := by omega
  obtain ⟨value,hread,hvalue⟩ := WP.spec_imp_exists (Vec.index_usize_spec flat index hidxBound)
  have hv : value=groupedWord flat i j := by
    rw [groupedWord,List.getD_eq_getElem flat.val 0#u32 hb]
    simpa only [hi] using hvalue
  unfold geometry_groups.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeM31.call_mut
  dsimp only
  simp only [hmul,bind_tc_ok,hadd,Vec.index_slice_index,hread,hv]

#print axioms grouping_callback_total
end AspisR1GeometryGrouping.Proof
