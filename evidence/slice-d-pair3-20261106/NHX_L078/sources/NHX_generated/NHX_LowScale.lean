import NGM_LPi_FieldValues
set_option autoImplicit false
namespace NHX_LowScale
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues
abbrev E := LPi_Total.NE

def limbs (x : E) : List Nat :=
 [x.c0.c0.a.val,x.c0.c0.b.val,x.c0.c1.a.val,x.c0.c1.b.val,
  x.c1.c0.a.val,x.c1.c0.b.val,x.c1.c1.a.val,x.c1.c1.b.val]

/-- Missing squared-quarter scalar law for pair_loop15, reusing LPf base-product
laws. This is a different constant domain from NGM_RoundScale, not a rerun. -/
theorem square : FIo_Native.aspis_core.field.M31.mul FIo_Native.weights.QUARTER FIo_Native.weights.QUARTER=ok 134217728#u32 := by
 obtain ⟨z,run,val,canonical⟩:=LPf_BaseMultiply.source FIo_Native.weights.QUARTER FIo_Native.weights.QUARTER
 have same:z=134217728#u32:=UScalar.eq_of_val_eq (by
  change z.val=134217728
  change z.val=(536870912*536870912)%2147483647 at val
  norm_num at val
  exact val)
 rwa [same] at run

theorem total (x : E) : ∃ out : E,
 FIo_Native.aspis_core.field.wide_exact.WideExact.mul_m31 x 134217728#u32=ok out ∧
 canonE out ∧ limbs out=(limbs x).map (fun word=>(word*134217728)%2147483647) := by
 have quarter : (134217728#u32 % 2147483647#u32)=ok 134217728#u32 := by rfl
 obtain ⟨a,ha,va,ca⟩ := LPf_BaseMultiply.source x.c0.c0.a 134217728#u32
 obtain ⟨b,hb,vb,cb⟩ := LPf_BaseMultiply.source x.c0.c0.b 134217728#u32
 obtain ⟨c,hc,vc,cc⟩ := LPf_BaseMultiply.source x.c0.c1.a 134217728#u32
 obtain ⟨d,hd,vd,cd⟩ := LPf_BaseMultiply.source x.c0.c1.b 134217728#u32
 obtain ⟨e,he,ve,ce⟩ := LPf_BaseMultiply.source x.c1.c0.a 134217728#u32
 obtain ⟨f,hf,vf,cf⟩ := LPf_BaseMultiply.source x.c1.c0.b 134217728#u32
 obtain ⟨g,hg,vg,cg⟩ := LPf_BaseMultiply.source x.c1.c1.a 134217728#u32
 obtain ⟨h,hh,vh,ch⟩ := LPf_BaseMultiply.source x.c1.c1.b 134217728#u32
 refine ⟨⟨⟨⟨a,b⟩,⟨c,d⟩⟩,⟨⟨e,f⟩,⟨g,h⟩⟩⟩,?_,?_,?_⟩
 · simp only [FIo_Native.aspis_core.field.wide_exact.WideExact.mul_m31,
    FIo_Native.aspis_core.field.QM31.mul_m31,FIo_Native.aspis_core.field.CM31.mul_m31,
    FIo_Native.aspis_core.field.P,quarter,ha,hb,hc,hd,he,hf,hg,hh,bind_tc_ok]
 · exact ⟨⟨⟨ca,cb⟩,⟨cc,cd⟩⟩,⟨⟨ce,cf⟩,⟨cg,ch⟩⟩⟩
 · simp [limbs,va,vb,vc,vd,ve,vf,vg,vh]
#print axioms square
#print axioms total
end NHX_LowScale
