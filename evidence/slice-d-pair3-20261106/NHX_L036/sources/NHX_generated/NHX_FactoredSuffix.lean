import NHX_FactoredCut
set_option autoImplicit false
namespace NHX_FactoredSuffix
open Aeneas Aeneas.Std Result ControlFlow AspisR1 LPi_FieldValues
open NHM_FactoredPrefix NHX_FactoredCut

theorem total (ap1 : Cells) (side : Usize) (iter : Iter) (weights : Cells)
 (q4 q16 : NQ) (a b c d : NE)
 (ha : canonE a) (hb : canonE b) (hc : canonE c) (hd : canonE d)
 (hw : ∀ x∈weights.val,canonE x) (h4 : canonQ q4) (h16 : canonQ q16) :
 ∃ out,suffix ap1 side iter weights q4 q16 (a,b,c,d)=ok (.cont (iter,out)) ∧
 (∀ x∈out.val,canonE x) := by
 obtain ⟨m0,hm0,cm0,_⟩:=LPi_TowerValues.wide_mul a d ha hd
 by_cases hside:side=0#usize
 · obtain ⟨m1,hm1,cm1,_⟩:=LPi_TowerValues.wide_mul a c ha hc
   obtain ⟨v1,hv1,cv1,_⟩:=NHE_ScalarProductLaw.product m1 q16 cm1 h16
   let w0:=NHI_ArrayCells.put weights 0#usize m0
   let w1:=NHI_ArrayCells.put w0 1#usize v1
   have u0:=NHI_ArrayCells.update weights 0#usize m0 (by decide)
   have u1:=NHI_ArrayCells.update (NHI_ArrayCells.put weights 0#usize m0) 1#usize v1 (by decide)
   refine ⟨w1,?_,NHM_ArrayPreserve.canonical canonE w0 w1 1#usize v1
    (NHM_ArrayPreserve.canonical canonE weights w0 0#usize m0 hw cm0 u0) cv1 u1⟩
   dsimp only [suffix]
   simp only [hside,ite_true,hm0,hm1,hv1,u0,u1,bind_tc_ok]
   rfl
 · let old:=NHI_ScalarDomain.pick weights 1 (by decide)
   have cold:=NHI_ScalarDomain.canon_pick canonE weights hw 1 (by decide)
   have iold:=NHI_ScalarDomain.index weights 1#usize (by decide)
   let last:=NHI_ScalarDomain.pick ap1 1 (by decide)
   obtain ⟨quarter,hquarter,cquarter,_⟩:=NGM_RoundScale.total last
   have hquarter1 : FIo_Native.aspis_core.field.wide_exact.WideExact.mul_m31 last FIo_Native.weights.QUARTER=ok quarter:=by
    simpa only [FIo_Native.weights.QUARTER] using hquarter
   obtain ⟨p,hp,cp,_⟩:=LPi_TowerValues.wide_mul a quarter ha cquarter
   obtain ⟨v1,hv1,cv1⟩:=NGW_PolynomialAdd.total old p cold cp
   obtain ⟨v2,hv2,cv2,_⟩:=NHE_ScalarProductLaw.product m0 q4 cm0 h4
   obtain ⟨m3,hm3,cm3,_⟩:=LPi_TowerValues.wide_mul a b ha hb
   obtain ⟨q,hq,cq,_⟩:=LPi_TowerValues.qm_mul q16 q4 h16 h4
   obtain ⟨v3,hv3,cv3,_⟩:=NHE_ScalarProductLaw.product m3 q cm3 cq
   let w0:=NHI_ArrayCells.put weights 1#usize v1
   let w1:=NHI_ArrayCells.put w0 2#usize v2
   let w2:=NHI_ArrayCells.put w1 3#usize v3
   have u0:=NHI_ArrayCells.update weights 1#usize v1 (by decide)
   have u1:=NHI_ArrayCells.update (NHI_ArrayCells.put weights 1#usize v1) 2#usize v2 (by decide)
   have u2:=NHI_ArrayCells.update (NHI_ArrayCells.put (NHI_ArrayCells.put weights 1#usize v1) 2#usize v2) 3#usize v3 (by decide)
   have c0:=NHM_ArrayPreserve.canonical canonE weights w0 1#usize v1 hw cv1 u0
   have c1:=NHM_ArrayPreserve.canonical canonE w0 w1 2#usize v2 c0 cv2 u1
   dsimp only [last,old] at hquarter1 hv1
   refine ⟨w2,?_,NHM_ArrayPreserve.canonical canonE w1 w2 3#usize v3 c1 cv3 u2⟩
   dsimp only [suffix]
   simp only [hside,ite_false,iold,bind_tc_ok,hquarter1,hp,hv1,u0,hm0,hv2,u1,hm3,hq,hv3,u2]
   rfl

#print axioms total
end NHX_FactoredSuffix
