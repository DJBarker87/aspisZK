import NJX_AppendTargets
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKI_TweakScalar
open Aeneas Aeneas.Std Result
theorem source (x : U32) (hx : x.val<2147483647) :
 ∃ t, FIq_Native.field.M31.add x NJX_AppendTargets.tweak=ok t ∧
 t.val=(x.val+1095962629)%2147483647 ∧ t.val<2147483647 := by
 obtain ⟨t,ct,vt,ht⟩ := NJB_TagReduce.add x NJX_AppendTargets.tweak hx (by decide)
 exact ⟨t,ct,vt,ht⟩
#print axioms source
end AspisR1.NKI_TweakScalar
end
