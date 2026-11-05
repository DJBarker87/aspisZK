import NGM_LPi_FieldValues
set_option autoImplicit false
namespace AspisR1.NGM_RoundScale
open Aeneas Aeneas.Std Result LPi_FieldValues
abbrev E := LPi_Total.NE

def limbs (x : E) : List Nat :=
 [x.c0.c0.a.val,x.c0.c0.b.val,x.c0.c1.a.val,x.c0.c1.b.val,
  x.c1.c0.a.val,x.c1.c0.b.val,x.c1.c1.a.val,x.c1.c1.b.val]

/-- Exact emitted scalar product law paired with the round's opaque call.
No product/result observation or successful enclosing round is assumed. -/
theorem total (x : E) : ∃ out : E,
 FIo_Native.aspis_core.field.wide_exact.WideExact.mul_m31 x 536870912#u32=ok out ∧
 canonE out ∧ limbs out=(limbs x).map (fun word=>(word*536870912)%2147483647) := by
 have quarter : (536870912#u32 % 2147483647#u32)=ok 536870912#u32 := by rfl
 obtain ⟨a,ha,va,ca⟩ := LPf_BaseMultiply.source x.c0.c0.a 536870912#u32
 obtain ⟨b,hb,vb,cb⟩ := LPf_BaseMultiply.source x.c0.c0.b 536870912#u32
 obtain ⟨c,hc,vc,cc⟩ := LPf_BaseMultiply.source x.c0.c1.a 536870912#u32
 obtain ⟨d,hd,vd,cd⟩ := LPf_BaseMultiply.source x.c0.c1.b 536870912#u32
 obtain ⟨e,he,ve,ce⟩ := LPf_BaseMultiply.source x.c1.c0.a 536870912#u32
 obtain ⟨f,hf,vf,cf⟩ := LPf_BaseMultiply.source x.c1.c0.b 536870912#u32
 obtain ⟨g,hg,vg,cg⟩ := LPf_BaseMultiply.source x.c1.c1.a 536870912#u32
 obtain ⟨h,hh,vh,ch⟩ := LPf_BaseMultiply.source x.c1.c1.b 536870912#u32
 refine ⟨⟨⟨⟨a,b⟩,⟨c,d⟩⟩,⟨⟨e,f⟩,⟨g,h⟩⟩⟩,?_,?_,?_⟩
 · simp only [FIo_Native.aspis_core.field.wide_exact.WideExact.mul_m31,
    FIo_Native.aspis_core.field.QM31.mul_m31,FIo_Native.aspis_core.field.CM31.mul_m31,
    FIo_Native.aspis_core.field.P,quarter,ha,hb,hc,hd,he,hf,hg,hh,bind_tc_ok]
 · exact ⟨⟨⟨ca,cb⟩,⟨cc,cd⟩⟩,⟨⟨ce,cf⟩,⟨cg,ch⟩⟩⟩
 · simp [limbs,va,vb,vc,vd,ve,vf,vg,vh]
#print axioms total
end AspisR1.NGM_RoundScale
