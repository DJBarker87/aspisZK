import XRy_ClaimArithmetic
open Aeneas Aeneas.Std Result
open XRo_Join_Carriers XRo_Join_ResultTransport XRn_Join_FieldExternal XRp_PowersQAdd
set_option autoImplicit false
namespace XRy_ClaimAdd
open AspisR1ClaimPreparedBridge XRy_ClaimArithmetic

def minimalAdd (a b : W) : Result W := do
 let lo ← AspisR1CurrentWideMul.field.QM31.add a.c0 b.c0
 let hi ← AspisR1CurrentWideMul.field.QM31.add a.c1 b.c1
 ok ⟨lo,hi⟩

theorem full_graph (a b : AspisR1CurrentWide.Proof.E) :
 mapR AspisR1CurrentWide.Proof.toMinimalWide
   (AspisR1CurrentWide.field.wide_exact.WideExact.add a b) =
 minimalAdd (AspisR1CurrentWide.Proof.toMinimalWide a)
   (AspisR1CurrentWide.Proof.toMinimalWide b) := by
 simp only [AspisR1CurrentWide.field.wide_exact.WideExact.add,minimalAdd,
   AspisR1CurrentWide.Proof.toMinimalWide,AspisR1CurrentWideMul.field.QM31.add,
   ←AspisR1CurrentWide.Proof.qm_add_same,mapR,bind_assoc_eq,bind_tc_ok]

theorem graph (a b : C.E) :
 mapR toMinimal (AspisR1CurrentPreparedClaim.aspis_core.field.WideExact.add (toClaimE a) (toClaimE b)) =
 minimalAdd (XRy_WideMultiply.toWide a) (XRy_WideMultiply.toWide b) := by
 unfold AspisR1CurrentPreparedClaim.aspis_core.field.WideExact.add
 simp only [mapR,bind_assoc_eq,bind_tc_ok]
 exact full_graph _ _

theorem add (a b : C.E) (ha : XRy_WideMultiply.Canonical a) (hb : XRy_WideMultiply.Canonical b) :
 ∃ z, aspis_core.field.wide_exact.WideExact.add a b = ok z ∧ XRy_WideMultiply.Canonical z ∧
 AspisR1CurrentPreparedClaim.aspis_core.field.WideExact.add (toClaimE a) (toClaimE b) = ok (toClaimE z) := by
 obtain ⟨lo,el,hl,tl⟩ := XRy_QmLinear.add (newQ a.c0) (newQ b.c0) ha.1 hb.1
 obtain ⟨hi,eh,hh,th⟩ := XRy_QmLinear.add (newQ a.c1) (newQ b.c1) ha.2 hb.2
 let z : C.E := ⟨oldQ lo,oldQ hi⟩
 have ht : minimalAdd (XRy_WideMultiply.toWide a) (XRy_WideMultiply.toWide b) = ok (toMinimal (toClaimE z)) := by
   simp only [minimalAdd,XRy_WideMultiply.toWide,tl,th,bind_tc_ok]
   rfl
 refine ⟨z,?_,⟨hl,hh⟩,?_⟩
 · simp only [aspis_core.field.wide_exact.WideExact.add,el,eh,bind_tc_ok,z]
 · apply map_injective toMinimal injective
   exact (graph a b).trans ht

#print axioms full_graph
#print axioms graph
#print axioms add
end XRy_ClaimAdd
