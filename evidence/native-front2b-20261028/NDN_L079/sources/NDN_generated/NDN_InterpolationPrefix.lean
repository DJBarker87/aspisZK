import NDN_InterpolationPrestate
import NDN_InterpolationBridge
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NDN_InterpolationPrefix

def arithmetic_prefix (a0 a1 a2 b0 b1 b2 : U32) : Result U64 := do
 let p0 ← core.convert.num.FromU64U32.from a0 * core.convert.num.FromU64U32.from b0
 let p1 ← core.convert.num.FromU64U32.from a1 * core.convert.num.FromU64U32.from b1
 let s ← p0+p1
 let p2 ← core.convert.num.FromU64U32.from a2 * core.convert.num.FromU64U32.from b2
 s+p2

theorem source_factor (a0 a1 a2 b0 b1 b2 : U32) :
 FIq_Native.state_only_poseidon.interpolate_three_constant_limb a0 a1 a2 b0 b1 b2 =
 (do let raw ← arithmetic_prefix a0 a1 a2 b0 b1 b2;FIq_Native.field.M31.reduce_u64 raw) := by
 simp only [FIq_Native.state_only_poseidon.interpolate_three_constant_limb,arithmetic_prefix,
  lift,bind_tc_ok,bind_assoc_eq]

theorem value (a0 a1 a2 b0 b1 b2 : U32)
 (ha0:a0.val<2147483647) (ha1:a1.val<2147483647) (ha2:a2.val<2147483647)
 (hb0:b0.val<2147483647) (hb1:b1.val<2147483647) (hb2:b2.val<2147483647) :
 ∃ raw,arithmetic_prefix a0 a1 a2 b0 b1 b2=ok raw ∧
 raw.val=a0.val*b0.val+a1.val*b1.val+a2.val*b2.val := by
 obtain ⟨p0,p1,p2,h0,h1,h2,v0,v1,v2,b0',b1',b2',bound⟩:=
  NDN_InterpolationPrestate.raw_domain a0 a1 a2 b0 b1 b2 ha0 ha1 ha2 hb0 hb1 hb2
 have h01:p0.val+p1.val<2^64 := by omega
 obtain ⟨s,hs,vs⟩:=WP.spec_imp_exists (UScalar.add_spec (x:=p0) (y:=p1) (by scalar_tac))
 obtain ⟨z,hz,vz⟩:=WP.spec_imp_exists (UScalar.add_spec (x:=s) (y:=p2) (by scalar_tac))
 refine ⟨z,?_,?_⟩
 · simp only [arithmetic_prefix,h0,h1,bind_tc_ok,hs,h2,hz]
 · simp only [vz,vs,v0,v1,v2]

#print axioms source_factor
#print axioms value
end NDN_InterpolationPrefix
