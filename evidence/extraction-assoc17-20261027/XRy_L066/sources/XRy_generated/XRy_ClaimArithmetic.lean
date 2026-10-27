import XRy_PreparePowers
open Aeneas Aeneas.Std Result
open XRo_Join_Carriers XRo_Join_ResultTransport
set_option autoImplicit false
namespace XRy_ClaimArithmetic
open AspisR1ClaimPreparedBridge
abbrev CE := AspisR1CurrentPreparedClaim.Concrete.E
abbrev W := XRy_WideMultiply.W

def toMinimal (x : CE) : W :=
 AspisR1CurrentWide.Proof.toMinimalWide (AspisR1CurrentPreparedClaim.Concrete.toFull x)
def fromMinimal (x : W) : CE :=
 ⟨⟨⟨x.c0.c0.a,x.c0.c0.b⟩,⟨x.c0.c1.a,x.c0.c1.b⟩⟩,
  ⟨⟨x.c1.c0.a,x.c1.c0.b⟩,⟨x.c1.c1.a,x.c1.c1.b⟩⟩⟩

theorem roundtrip (x : CE) : fromMinimal (toMinimal x)=x := rfl

theorem injective : Function.Injective toMinimal := by
 intro a b h
 exact (roundtrip a).symm.trans ((congrArg fromMinimal h).trans (roundtrip b))

theorem mul_graph (a b : C.E) :
 mapR toMinimal (AspisR1CurrentPreparedClaim.aspis_core.field.WideExact.mul (toClaimE a) (toClaimE b)) =
 AspisR1CurrentWideMul.field.wide_exact.WideExact.mul (XRy_WideMultiply.toWide a) (XRy_WideMultiply.toWide b) := by
 unfold AspisR1CurrentPreparedClaim.aspis_core.field.WideExact.mul
 simp only [mapR,bind_assoc_eq,bind_tc_ok]
 exact AspisR1CurrentWide.Proof.wide_mul_same_minimal _ _

theorem multiply (a b : C.E) (ha : XRy_WideMultiply.Canonical a) (hb : XRy_WideMultiply.Canonical b) :
 ∃ z, aspis_core.field.wide_exact.WideExact.mul a b = ok z ∧ XRy_WideMultiply.Canonical z ∧
 AspisR1CurrentPreparedClaim.aspis_core.field.WideExact.mul (toClaimE a) (toClaimE b) = ok (toClaimE z) := by
 obtain ⟨z,hz,hc,ht⟩ := XRy_WideMultiply.total a b ha hb
 refine ⟨z,hz,hc,?_⟩
 apply map_injective toMinimal injective
 exact (mul_graph a b).trans ht

#print axioms roundtrip
#print axioms injective
#print axioms mul_graph
#print axioms multiply
end XRy_ClaimArithmetic
