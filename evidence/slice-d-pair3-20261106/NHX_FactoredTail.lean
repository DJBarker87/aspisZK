import NHX_FieldResults
import NHM_FactoredFrames
set_option autoImplicit false
namespace NHX_FactoredTail
open Aeneas Aeneas.Std Result ControlFlow AspisR1 LPi_FieldValues
open NHM_FactoredPrefix

theorem total (ap0 ap1 : Cells) (side : Usize) (iter : Iter) (weights : Cells)
 (low_powers high_powers : Array NQ 4#usize) (q4 q16 : NQ)
 (ha : ∀ x∈ap0.val,canonE x) (hb : ∀ x∈ap1.val,canonE x)
 (hw : ∀ x∈weights.val,canonE x)
 (hl : ∀ x∈low_powers.val,canonQ x) (hh : ∀ x∈high_powers.val,canonQ x)
 (hc4 : canonQ q4) (hc16 : canonQ q16) (side_zero : side=0#usize) :
 ∃ out,tail ap0 ap1 side iter weights low_powers high_powers q4 q16=ok (.cont (iter,out)) ∧
 (∀ x∈out.val,canonE x) := by
 obtain ⟨sum,low,hfold,cs,hs,cl,hval⟩:=NHI_Scalar.total low_powers ap0 ha hl
 let a0:=NHI_ScalarDomain.pick ap1 0 (by decide)
 let q0:=NHI_ScalarDomain.pick high_powers 0 (by decide)
 have ca0:canonE a0:=NHI_ScalarDomain.canon_pick canonE ap1 hb 0 (by decide)
 have cq0:canonQ q0:=NHI_ScalarDomain.canon_pick canonQ high_powers hh 0 (by decide)
 have ia0:Array.index_usize ap1 0#usize=ok a0:=NHI_ScalarDomain.index ap1 0#usize (by decide)
 have iq0:Array.index_usize high_powers 0#usize=ok q0:=NHI_ScalarDomain.index high_powers 0#usize (by decide)
 obtain ⟨p0,hp0,cp0,_⟩:=NHE_ScalarProductLaw.product a0 q0 ca0 cq0
 obtain ⟨t0,ht0,ct0,_⟩:=NGM_RoundScale.total p0
 change FIo_Native.aspis_core.field.wide_exact.WideExact.mul_m31 p0 FIo_Native.weights.QUARTER=ok t0 at ht0
 let a1:=NHI_ScalarDomain.pick ap1 3 (by decide)
 let q1:=NHI_ScalarDomain.pick high_powers 1 (by decide)
 have ca1:canonE a1:=NHI_ScalarDomain.canon_pick canonE ap1 hb 3 (by decide)
 have cq1:canonQ q1:=NHI_ScalarDomain.canon_pick canonQ high_powers hh 1 (by decide)
 have ia1:Array.index_usize ap1 3#usize=ok a1:=NHI_ScalarDomain.index ap1 3#usize (by decide)
 have iq1:Array.index_usize high_powers 1#usize=ok q1:=NHI_ScalarDomain.index high_powers 1#usize (by decide)
 obtain ⟨p1,hp1,cp1,_⟩:=NHE_ScalarProductLaw.product a1 q1 ca1 cq1
 obtain ⟨t1,ht1,ct1,_⟩:=NGM_RoundScale.total p1
 change FIo_Native.aspis_core.field.wide_exact.WideExact.mul_m31 p1 FIo_Native.weights.QUARTER=ok t1 at ht1
 let a2:=NHI_ScalarDomain.pick ap1 2 (by decide)
 let q2:=NHI_ScalarDomain.pick high_powers 2 (by decide)
 have ca2:canonE a2:=NHI_ScalarDomain.canon_pick canonE ap1 hb 2 (by decide)
 have cq2:canonQ q2:=NHI_ScalarDomain.canon_pick canonQ high_powers hh 2 (by decide)
 have ia2:Array.index_usize ap1 2#usize=ok a2:=NHI_ScalarDomain.index ap1 2#usize (by decide)
 have iq2:Array.index_usize high_powers 2#usize=ok q2:=NHI_ScalarDomain.index high_powers 2#usize (by decide)
 obtain ⟨p2,hp2,cp2,_⟩:=NHE_ScalarProductLaw.product a2 q2 ca2 cq2
 obtain ⟨t2,ht2,ct2,_⟩:=NGM_RoundScale.total p2
 change FIo_Native.aspis_core.field.wide_exact.WideExact.mul_m31 p2 FIo_Native.weights.QUARTER=ok t2 at ht2
 let a3:=NHI_ScalarDomain.pick ap1 1 (by decide)
 let q3:=NHI_ScalarDomain.pick high_powers 3 (by decide)
 have ca3:canonE a3:=NHI_ScalarDomain.canon_pick canonE ap1 hb 1 (by decide)
 have cq3:canonQ q3:=NHI_ScalarDomain.canon_pick canonQ high_powers hh 3 (by decide)
 have ia3:Array.index_usize ap1 1#usize=ok a3:=NHI_ScalarDomain.index ap1 1#usize (by decide)
 have iq3:Array.index_usize high_powers 3#usize=ok q3:=NHI_ScalarDomain.index high_powers 3#usize (by decide)
 obtain ⟨p3,hp3,cp3,_⟩:=NHE_ScalarProductLaw.product a3 q3 ca3 cq3
 obtain ⟨t3,ht3,ct3,_⟩:=NGM_RoundScale.total p3
 change FIo_Native.aspis_core.field.wide_exact.WideExact.mul_m31 p3 FIo_Native.weights.QUARTER=ok t3 at ht3
 obtain ⟨first2,first3,all,hr,c2,c3,call⟩:=NHM_FactoredSums.total t0 t1 t2 t3 ct0 ct1 ct2 ct3
 obtain ⟨m0,hm0,cm0,_⟩:=LPi_TowerValues.wide_mul low all cl call
 obtain ⟨m1,hm1,cm1,_⟩:=LPi_TowerValues.wide_mul low first3 cl c3
 obtain ⟨v1,hv1,cv1,_⟩:=NHE_ScalarProductLaw.product m1 q16 cm1 hc16
 have joins : ∃ (h2 h3 : Unit),FIo_Native.aspis_core.field.wide_exact.WideExact.add t0 t1=ok first2 ∧
  FIo_Native.aspis_core.field.wide_exact.WideExact.add first2 t2=ok first3 ∧
  FIo_Native.aspis_core.field.wide_exact.WideExact.add first3 t3=ok all := by
  unfold NHM_FactoredSums.run at hr
  obtain ⟨x,hx,hr⟩:=Port3_PushFrame.bind_success _ _ _ hr
  obtain ⟨y,hy,hr⟩:=Port3_PushFrame.bind_success _ _ _ hr
  obtain ⟨z,hz,hr⟩:=Port3_PushFrame.bind_success _ _ _ hr
  cases Result.ok.inj hr
  exact ⟨(),(),hx,hy,hz⟩
 obtain ⟨_,_,h2,h3,hall⟩:=joins
 have side0:side=0#usize:=side_zero
 let w0:=NHI_ArrayCells.put weights 0#usize m0
 let w1:=NHI_ArrayCells.put w0 1#usize v1
 have u0:=NHI_ArrayCells.update weights 0#usize m0 (by decide)
 have u1:=NHI_ArrayCells.update w0 1#usize v1 (by decide)
 refine ⟨w1,?_,NHM_ArrayPreserve.canonical canonE w0 w1 1#usize v1
  (NHM_ArrayPreserve.canonical canonE weights w0 0#usize m0 hw cm0 u0) cv1 u1⟩
 simp only [tail,hs,bind_tc_ok,side0,ite_true]
 simp only [FIo_Native.weights.PERM,Array.index_usize,Array.make,Array.getElem?_Usize_eq] at *
 simp_all only [bind_tc_ok]

#print axioms total
end NHX_FactoredTail
