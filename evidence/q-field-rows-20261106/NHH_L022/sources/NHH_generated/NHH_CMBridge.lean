import NHH_CMTrace
set_option autoImplicit false
noncomputable section
namespace NHH_CMBridge
open Aeneas Aeneas.Std Result
open AspisV8R15.ExactTowerBase
open AspisV8R19
open NHH_CMInverse (C Canon decode encode toSampler)
def Live (x : C) : Prop := ¬(x.a=0#u32 ∧ x.b=0#u32)

theorem decode_live (x : C) (hx : Canon x) (hl : Live x) : decode x≠0 := by
 intro zero
 have a := congrArg QuadraticAlgebra.re zero
 have b := congrArg QuadraticAlgebra.im zero
 change (x.a.val : M31Exact)=0 at a
 change (x.b.val : M31Exact)=0 at b
 have av : x.a.val=0 := by
  simpa only [ZMod.val_natCast_of_lt hx.1,ZMod.val_zero] using congrArg ZMod.val a
 have bv : x.b.val=0 := by
  simpa only [ZMod.val_natCast_of_lt hx.2,ZMod.val_zero] using congrArg ZMod.val b
 exact hl ⟨UScalar.eq_of_val_eq av,UScalar.eq_of_val_eq bv⟩

theorem encoded_canonical (x : CM31Exact) : Canon (encode x) := by
 constructor <;> simp only [encode,ComplexBaseExecution.encodeBase_val]
 · exact ZMod.val_lt x.re
 · exact ZMod.val_lt x.im

/-- Complete fixed-source packet on the caller-established canonical live
receiver. The output and every reply are derived from this execution. -/
theorem packet (x : C) (hx : Canon x) (hl : Live x) :
 ∃ out,
 NHH_CMTrace.run x=ok (out,NHH_CMTrace.log (decode x)) ∧ Canon out ∧
 NFG_InverseRef.field.CM31.inv x=ok out ∧
 AspisR72Sampler.field.CM31.inv (toSampler x)=ok (toSampler out) := by
 have live := decode_live x hx hl
 have trace := NHH_CMTrace.encoded (decode x) live
 rw [NHH_CMInverse.roundtrip x hx] at trace
 let out := encode (decode x)⁻¹
 have src : NFG_InverseRef.field.CM31.inv x=ok out := by
  rw [←NHH_CMTrace.source,trace];rfl
 have assoc := NHH_CMInverse.canonical_association x hx live
 rw [src,bind_tc_ok] at assoc
 exact ⟨out,trace,encoded_canonical _,src,assoc.symm⟩

/-- The frozen sole inventory caller selects this direct backend. This is
specialization, not generic function-pointer equality or a generic Kani pass. -/
theorem selected_backend (x : C) :
 NFG_InverseRef.field.CM31.inv x=
 NFG_InverseRef.field.CM31.inv_with x NFG_InverseRef.field.M31.inv := rfl

theorem specialized_packet (x : C) (hx : Canon x) (hl : Live x) :
 ∃ out,
 NFG_InverseRef.field.CM31.inv_with x NFG_InverseRef.field.M31.inv=ok out ∧ Canon out ∧
 AspisR72Sampler.field.CM31.inv (toSampler x)=ok (toSampler out) := by
 obtain ⟨out,_,hc,hs,hm⟩ := packet x hx hl
 exact ⟨out,hs,hc,hm⟩

#print axioms decode_live
#print axioms encoded_canonical
#print axioms packet
#print axioms selected_backend
#print axioms specialized_packet
end NHH_CMBridge
end
