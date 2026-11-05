import NHM_FactoredTerm
set_option autoImplicit false
namespace NHM_FactoredSums
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues

def run (a b c d : NE) : Result (NE × NE × NE) := do
 let first2 ← FIo_Native.aspis_core.field.wide_exact.WideExact.add a b
 let first3 ← FIo_Native.aspis_core.field.wide_exact.WideExact.add first2 c
 let all ← FIo_Native.aspis_core.field.wide_exact.WideExact.add first3 d
 ok (first2,first3,all)

theorem total (a b c d : NE) (ha : canonE a) (hb : canonE b) (hc : canonE c) (hd : canonE d) :
 ∃ first2 first3 all,run a b c d=ok (first2,first3,all) ∧
 canonE first2 ∧ canonE first3 ∧ canonE all := by
 obtain ⟨x,hx,cx⟩:=NGW_PolynomialAdd.total a b ha hb
 obtain ⟨y,hy,cy⟩:=NGW_PolynomialAdd.total x c cx hc
 obtain ⟨z,hz,cz⟩:=NGW_PolynomialAdd.total y d cy hd
 exact ⟨x,y,z,by simp only [run,hx,hy,hz,bind_tc_ok],cx,cy,cz⟩

#print axioms total
end NHM_FactoredSums
