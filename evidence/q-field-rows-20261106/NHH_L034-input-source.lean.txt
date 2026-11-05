import NHH_QAll
import NHH_QTrace
set_option autoImplicit false
noncomputable section
namespace NHH_QBridge
open Aeneas Aeneas.Std Result
open AspisV8R15.ExactTowerBase
open NHH_QInverse (Q Canon encode decode toSampler)
def Live (x : Q) : Prop := ¬(x.c0.a=0#u32 ∧ x.c0.b=0#u32 ∧ x.c1.a=0#u32 ∧ x.c1.b=0#u32)

theorem decode_live (x : Q) (hx : Canon x) (hl : Live x) : decode x≠0 := by
 intro hz
 have z : x=encode 0 := (NHH_QInverse.roundtrip x hx).symm.trans (congrArg encode hz)
 apply hl
 rw [z]
 exact ⟨rfl,rfl,rfl,rfl⟩

theorem try_packet (x : Q) (hx : Canon x) :
 ∃ out events,
 NHH_QTrace.run x=ok (out,events) ∧
 NFG_InverseRef.field.QM31.try_inv x=ok out ∧
 (∀ value, out=some value → Canon value) ∧
 AspisR72Sampler.field.QM31.try_inv (toSampler x)=ok (out.map toSampler) ∧
 (out=none → events=[]) := by
 have assoc := NHH_QAll.try_association x
 by_cases hz : decode x=0
 · have z : x=encode 0 := (NHH_QInverse.roundtrip x hx).symm.trans (congrArg encode hz)
   have tr : NHH_QTrace.run x=ok (none,[]) := by rw [z];exact NHH_QTrace.zero
   have src : NFG_InverseRef.field.QM31.try_inv x=ok none := by
    rw [←NHH_QTrace.source,tr];rfl
   rw [src,bind_tc_ok] at assoc
   exact ⟨none,[],tr,src,by intro v h;cases h,assoc.symm,by intro _;rfl⟩
 · have tr := NHH_QTrace.encoded (decode x) hz
   rw [NHH_QInverse.roundtrip x hx] at tr
   let out := encode (decode x)⁻¹
   have src : NFG_InverseRef.field.QM31.try_inv x=ok (some out) := by
    rw [←NHH_QTrace.source,tr];rfl
   rw [src,bind_tc_ok] at assoc
   refine ⟨some out,NHH_QTrace.log (decode x),tr,src,?_,assoc.symm,?_⟩
   · intro v h
     have hv : out=v := Option.some.inj h
     exact hv ▸ NHH_QInverse.canonical _
   · intro h;cases h

theorem inverse_packet (x : Q) (hx : Canon x) (hl : Live x) :
 ∃ out,
 NFG_InverseRef.field.QM31.try_inv x=ok (some out) ∧ Canon out ∧
 NFG_InverseRef.field.QM31.inv x=ok out ∧
 (do let o ← AspisR72Sampler.field.QM31.try_inv (toSampler x)
     core.option.Option.expect o NFG_PanicMessage.value)=ok (toSampler out) := by
 have live := decode_live x hx hl
 let out := encode (decode x)⁻¹
 have child : NFG_InverseRef.field.QM31.try_inv x=ok (some out) := by
  rw [←NHH_QInverse.roundtrip x hx]
  exact NHH_QInverse.try_nonzero _ live
 have returned : NFG_InverseRef.field.QM31.inv x=ok out := by
  rw [NFG_InverseRef.field.QM31.inv,child];rfl
 have assoc := NHH_QAll.inverse_association x
 rw [returned,bind_tc_ok] at assoc
 exact ⟨out,child,NHH_QInverse.canonical _,returned,assoc.symm⟩

#print axioms decode_live
#print axioms try_packet
#print axioms inverse_packet
end NHH_QBridge
end
