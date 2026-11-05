import NHH_CMInverse
set_option autoImplicit false
noncomputable section
namespace NHH_CMTrace
open Aeneas Aeneas.Std Result
open AspisV8R19 AspisV8R15.ExactTowerBase
open ComplexBaseExecution (encodeBase)
inductive Event where
 | product : U32 → U32 → U32 → Event
 | backend : U32 → U32 → Event

def run (x : NHH_CMInverse.C) : Result (NHH_CMInverse.C × List Event) := do
 let aa ← NFG_InverseRef.field.M31.mul x.a x.a
 let bb ← NFG_InverseRef.field.M31.mul x.b x.b
 let n ← NFG_InverseRef.field.M31.add aa bb
 let inv ← NFG_InverseRef.field.M31.inv n
 let re ← NFG_InverseRef.field.M31.mul x.a inv
 let neg ← NFG_InverseRef.field.M31.neg x.b
 let im ← NFG_InverseRef.field.M31.mul neg inv
 ok (⟨re,im⟩,[.product x.a x.a aa,.product x.b x.b bb,.backend n inv,
  .product x.a inv re,.product neg inv im])

def log (x : CM31Exact) : List Event :=
 let a := encodeBase x.re
 let b := encodeBase x.im
 let n := NormInverse.complexNorm x
 let inv := encodeBase n⁻¹
 [.product a a (encodeBase (x.re*x.re)),.product b b (encodeBase (x.im*x.im)),
 .backend (encodeBase n) inv,.product a inv (encodeBase (x.re*n⁻¹)),
 .product (encodeBase (-x.im)) inv (encodeBase ((-x.im)*n⁻¹))]

theorem source (x : NHH_CMInverse.C) :
 (do let out ← run x;ok out.1)=NFG_InverseRef.field.CM31.inv x := by
 simp only [run,NFG_InverseRef.field.CM31.inv,NFG_InverseRef.field.CM31.inv_with,
 bind_assoc_eq,bind_tc_ok]

theorem encoded (x : CM31Exact) (hx : x≠0) :
 run (NHH_CMInverse.encode x)=ok (NHH_CMInverse.encode x⁻¹,log x) := by
 have hn := NormInverse.complex_norm_nonzero x hx
 have hi := NHH_EncodedScalar.inverse (NormInverse.complexNorm x) hn
 have he : (⟨x.re*(NormInverse.complexNorm x)⁻¹,
  (-x.im)*(NormInverse.complexNorm x)⁻¹⟩ : CM31Exact)=x⁻¹ := by
  rw [←NormInverse.complex_inverse_correct x hx]
  simp only [NormInverse.complexInverse,NormInverse.base_inverse_correct _ hn]
 simp only [NormInverse.complexNorm] at hi
 simp only [run,NHH_CMInverse.encode,NHH_EncodedScalar.multiply,NHH_EncodedScalar.addition,
  hi,NHH_EncodedScalar.negation,bind_tc_ok,log,NormInverse.complexNorm]
 exact congrArg (fun v => ok (NHH_CMInverse.encode v,log x)) he

/-- Backend domain is derived from the actual norm, before installing its law. -/
theorem backend_domain (x : CM31Exact) (hx : x≠0) :
 (encodeBase (NormInverse.complexNorm x)).val<2147483647 ∧
 encodeBase (NormInverse.complexNorm x)≠0#u32 := by
 constructor
 · simpa only [ComplexBaseExecution.encodeBase_val] using ZMod.val_lt (NormInverse.complexNorm x)
 · intro h
   have hv : (NormInverse.complexNorm x).val=0 := congrArg UScalar.val h
   exact NormInverse.complex_norm_nonzero x hx ((ZMod.val_eq_zero _).mp hv)

#print axioms source
#print axioms encoded
#print axioms backend_domain
end NHH_CMTrace
end
