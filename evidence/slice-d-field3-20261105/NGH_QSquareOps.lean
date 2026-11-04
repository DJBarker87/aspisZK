import NGH_QSquareRef
set_option autoImplicit false
noncomputable section
namespace NGH_QSquareOps
open Aeneas Aeneas.Std Result AspisR1.FIo_FieldBridge
open AspisR1CurrentWide.Proof
abbrev Canon := AspisR1.FIo_CMValues.Canon
abbrev decode (x : NC) := decodeC (cm x)

theorem square (x : NC) (hx : Canon x) :
 ∃ out, FIo_Native.aspis_core.field.CM31.square x=ok out ∧ Canon out ∧
 decode out=decode x*decode x := by
 obtain ⟨out,ho⟩ := NGA_NativeOps.cm_square_total x
 exact ⟨out,ho,AspisR1.FJm_CMSquare.value x out hx ho⟩

theorem product (x y : NC) (hx : Canon x) (hy : Canon y) :
 ∃ out, FIo_Native.aspis_core.field.CM31.mul x y=ok out ∧ Canon out ∧
 decode out=decode x*decode y := by
 obtain ⟨out,ho⟩ := AspisR1.NFN_LPi_Total.cm_mul x y
 exact ⟨out,ho,AspisR1.FIo_CMMulValues.mul x y out hx hy ho⟩

def finish (a b ab : NC) : Result NQ := do
 let r ← FIo_Native.aspis_core.field.mul_by_r b
 let lo ← FIo_Native.aspis_core.field.CM31.add a r
 let hi ← FIo_Native.aspis_core.field.CM31.add ab ab
 ok ⟨lo,hi⟩

-- Native call-log association, on precisely the same receiver and replies.
theorem associate (x : NQ) (a b ab : NC)
 (ha : FIo_Native.aspis_core.field.CM31.square x.c0=ok a)
 (hb : FIo_Native.aspis_core.field.CM31.square x.c1=ok b)
 (hab : FIo_Native.aspis_core.field.CM31.mul x.c0 x.c1=ok ab) :
 NGH_QSquareRef.run x=finish a b ab := by
 simp only [NGH_QSquareRef.run,finish,ha,hb,hab,bind_tc_ok]

-- Canonical domains required by native opaque sites are derived, not assumed
-- on independent replies. finish retains the real by-r, add and double calls.
theorem source (x : NQ) (hx : NGA_NativeOps.Canon x) :
 ∃ a b ab out,
 FIo_Native.aspis_core.field.CM31.square x.c0=ok a ∧ Canon a ∧
 FIo_Native.aspis_core.field.CM31.square x.c1=ok b ∧ Canon b ∧
 FIo_Native.aspis_core.field.CM31.mul x.c0 x.c1=ok ab ∧ Canon ab ∧
 finish a b ab=ok out ∧ NGA_NativeOps.Canon out ∧
 NGH_QSquareRef.run x=ok out ∧
 NGA_NativeOps.decode out=NGA_NativeOps.decode x*NGA_NativeOps.decode x := by
 obtain ⟨a,ha,ca,_⟩ := square x.c0 hx.1
 obtain ⟨b,hb,cb,_⟩ := square x.c1 hx.2
 obtain ⟨ab,hab,cab,_⟩ := product x.c0 x.c1 hx.1 hx.2
 obtain ⟨out,ho,co,vo⟩ := NGH_QSquareRef.cohort x hx
 exact ⟨a,b,ab,out,ha,ca,hb,cb,hab,cab,(associate x a b ab ha hb hab).symm.trans ho,co,ho,vo⟩
#print axioms square
#print axioms product
#print axioms associate
#print axioms source
end NGH_QSquareOps
end
