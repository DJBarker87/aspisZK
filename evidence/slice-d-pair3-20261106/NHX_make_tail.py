from pathlib import Path
E=Path(__file__).resolve().parent
s='''import NHX_FieldResults
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
 (hc4 : canonQ q4) (hc16 : canonQ q16) :
 ∃ out,tail ap0 ap1 side iter weights low_powers high_powers q4 q16=ok (.cont (iter,out)) ∧
 (∀ x∈out.val,canonE x) := by
 obtain ⟨sum,low,hfold,cs,hs,cl,hval⟩:=NHI_Scalar.total low_powers ap0 ha hl
'''
for i,perm in enumerate([0,3,2,1]):
 s+=f''' let a{i}:=NHI_ScalarDomain.pick ap1 {perm} (by decide)
 let q{i}:=NHI_ScalarDomain.pick high_powers {i} (by decide)
 have ca{i}:canonE a{i}:=NHI_ScalarDomain.canon_pick canonE ap1 hb {perm} (by decide)
 have cq{i}:canonQ q{i}:=NHI_ScalarDomain.canon_pick canonQ high_powers hh {i} (by decide)
 have ia{i}:Array.index_usize ap1 {perm}#usize=ok a{i}:=NHI_ScalarDomain.index ap1 {perm}#usize (by decide)
 have iq{i}:Array.index_usize high_powers {i}#usize=ok q{i}:=NHI_ScalarDomain.index high_powers {i}#usize (by decide)
 obtain ⟨p{i},hp{i},cp{i},_⟩:=NHE_ScalarProductLaw.product a{i} q{i} ca{i} cq{i}
 obtain ⟨t{i},ht{i},ct{i},_⟩:=NGM_RoundScale.total p{i}
 change FIo_Native.aspis_core.field.wide_exact.WideExact.mul_m31 p{i} FIo_Native.weights.QUARTER=ok t{i} at ht{i}
'''
s+=''' obtain ⟨first2,first3,all,hr,c2,c3,call⟩:=NHM_FactoredSums.total t0 t1 t2 t3 ct0 ct1 ct2 ct3
 obtain ⟨m0,hm0,cm0,_⟩:=LPi_TowerValues.wide_mul low all cl call
 obtain ⟨m1,hm1,cm1,_⟩:=LPi_TowerValues.wide_mul low first3 cl c3
 obtain ⟨v1,hv1,cv1,_⟩:=NHE_ScalarProductLaw.product m1 q16 cm1 hc16
 have joins : ∃ h2 h3,FIo_Native.aspis_core.field.wide_exact.WideExact.add t0 t1=ok first2 ∧
  FIo_Native.aspis_core.field.wide_exact.WideExact.add first2 t2=ok first3 ∧
  FIo_Native.aspis_core.field.wide_exact.WideExact.add first3 t3=ok all := by
  unfold NHM_FactoredSums.run at hr
  obtain ⟨x,hx,hr⟩:=Port3_PushFrame.bind_success _ _ _ hr
  obtain ⟨y,hy,hr⟩:=Port3_PushFrame.bind_success _ _ _ hr
  obtain ⟨z,hz,hr⟩:=Port3_PushFrame.bind_success _ _ _ hr
  cases Result.ok.inj hr
  exact ⟨(),(),hx,hy,hz⟩
 obtain ⟨_,_,h2,h3,hall⟩:=joins
 by_cases side0:side=0#usize
 · let w0:=NHI_ArrayCells.put weights 0#usize m0
   let w1:=NHI_ArrayCells.put w0 1#usize v1
   have u0:=NHI_ArrayCells.update weights 0#usize m0 (by decide)
   have u1:=NHI_ArrayCells.update w0 1#usize v1 (by decide)
   refine ⟨w1,?_,NHM_ArrayPreserve.canonical canonE w0 w1 1#usize v1
    (NHM_ArrayPreserve.canonical canonE weights w0 0#usize m0 hw cm0 u0) cv1 u1⟩
   simp only [tail,hs,bind_tc_ok,side0,ite_true]
   simp only [FIo_Native.weights.PERM,Array.index_usize,Array.make,Array.getElem?_Usize_eq] at *
'''
# Initial proposal intentionally only proves side0 below; replace theorem to be side0-only for focused qualification.
s=s[:s.index(' by_cases side0:')]+s[s.index(' by_cases side0:'):].replace(' by_cases side0:side=0#usize\n ·',' have side0:side=0#usize:=side_zero\n ')
s=s.replace(' (hc4 : canonQ q4) (hc16 : canonQ q16) :',' (hc4 : canonQ q4) (hc16 : canonQ q16) (side_zero : side=0#usize) :')
s=s.replace('∃ h2 h3,','∃ (h2 h3 : Unit),')
s+='''   simp_all only [bind_tc_ok]

#print axioms total
end NHX_FactoredTail
'''
(E/'NHX_FactoredTail.lean').write_text(s)
