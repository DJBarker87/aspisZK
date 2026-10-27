import XRy_QmLinear
open Aeneas Aeneas.Std Result
open XRo_Join_Carriers XRp_PowersQAdd XRn_Join_FieldExternal
set_option autoImplicit false
namespace XRy_WideMultiply
abbrev W := AspisR1CurrentWideMul.field.wide_exact.WideExact

def toWide (x : C.E) : W := ⟨toQ (newQ x.c0),toQ (newQ x.c1)⟩
def Canonical (x : C.E) : Prop := CanonicalQ (newQ x.c0) ∧ CanonicalQ (newQ x.c1)

theorem total (a b : C.E) (ha : Canonical a) (hb : Canonical b) :
 ∃ z, aspis_core.field.wide_exact.WideExact.mul a b = ok z ∧ Canonical z ∧
 AspisR1CurrentWideMul.field.wide_exact.WideExact.mul (toWide a) (toWide b) = ok (toWide z) := by
 obtain ⟨ac,eac,hac,tac⟩ := XRy_QmMultiply.total (newQ a.c0) (newQ b.c0) ha.1 hb.1
 obtain ⟨bd,ebd,hbd,tbd⟩ := XRy_QmMultiply.total (newQ a.c1) (newQ b.c1) ha.2 hb.2
 obtain ⟨aa,eaa,haa,taa⟩ := XRy_QmLinear.add (newQ a.c0) (newQ a.c1) ha.1 ha.2
 obtain ⟨bb,ebb,hbb,tbb⟩ := XRy_QmLinear.add (newQ b.c0) (newQ b.c1) hb.1 hb.2
 obtain ⟨cross,ecross,hcross,tcross⟩ := XRy_QmMultiply.total aa bb haa hbb
 obtain ⟨u,eu,hu,tu⟩ := XRy_QmLinear.mul_u_total bd hbd
 obtain ⟨lo,elo,hlo,tlo⟩ := XRy_QmLinear.add ac u hac hu
 obtain ⟨d,ed,hd,td⟩ := XRy_QmLinear.sub cross ac hcross hac
 obtain ⟨hi,ehi,hhi,thi⟩ := XRy_QmLinear.sub d bd hd hbd
 refine ⟨⟨oldQ lo,oldQ hi⟩,?_,⟨hlo,hhi⟩,?_⟩
 · simp only [aspis_core.field.wide_exact.WideExact.mul,eac,ebd,eaa,ebb,ecross,eu,elo,ed,ehi,bind_tc_ok]
 · simp only [AspisR1CurrentWideMul.field.wide_exact.WideExact.mul,toWide,
     tac,tbd,taa,tbb,tcross,tu,tlo,td,thi,bind_tc_ok]
   rfl

theorem multiply (a b : C.E) (ha : Canonical a) (hb : Canonical b) :
 mapR toWide (aspis_core.field.wide_exact.WideExact.mul a b) =
 AspisR1CurrentWideMul.field.wide_exact.WideExact.mul (toWide a) (toWide b) := by
 obtain ⟨z,hz,hc,ht⟩ := total a b ha hb
 rw [hz]
 exact ht.symm

#print axioms total
#print axioms multiply
end XRy_WideMultiply
