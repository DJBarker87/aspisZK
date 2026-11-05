import NHH_QInverse
set_option autoImplicit false
noncomputable section
namespace NHH_QTrace
open Aeneas Aeneas.Std Result
open AspisV8R19 AspisV8R15.ExactTowerBase
open NHH_QInverse (Q encode)
abbrev C := NHH_CMInverse.C
inductive Event where
 | square : C → C → Event
 | inverse : C → C → Event
 | product : C → C → C → Event

def run (x : Q) : Result (Option Q × List Event) := do
 let zero ← NFG_InverseRef.field.QM31.is_zero x
 if zero then ok (none,[]) else
 let aa ← NFG_InverseRef.field.CM31.square x.c0
 let bb ← NFG_InverseRef.field.CM31.square x.c1
 let rotated ← NFG_InverseRef.field.mul_by_r bb
 let norm ← NFG_InverseRef.field.CM31.sub aa rotated
 let inv ← NFG_InverseRef.field.CM31.inv norm
 let re ← NFG_InverseRef.field.CM31.mul x.c0 inv
 let negative ← NFG_InverseRef.field.CM31.neg x.c1
 let im ← NFG_InverseRef.field.CM31.mul negative inv
 ok (some ⟨re,im⟩,[.square x.c0 aa,.square x.c1 bb,.inverse norm inv,
 .product x.c0 inv re,.product negative inv im])

def log (x : QM31Exact) : List Event :=
 let a := NHH_CMInverse.encode x.re
 let b := NHH_CMInverse.encode x.im
 let n := NormInverse.quarticNorm x
 let inv := NHH_CMInverse.encode n⁻¹
 [.square a (NHH_CMInverse.encode (x.re*x.re)),.square b (NHH_CMInverse.encode (x.im*x.im)),
 .inverse (NHH_CMInverse.encode n) inv,.product a inv (NHH_CMInverse.encode (x.re*n⁻¹)),
 .product (NHH_CMInverse.encode (-x.im)) inv (NHH_CMInverse.encode ((-x.im)*n⁻¹))]

theorem source (x : Q) :
 (do let out ← run x;ok out.1)=NFG_InverseRef.field.QM31.try_inv x := by
 simp only [run,NFG_InverseRef.field.QM31.try_inv,bind_assoc_eq]
 congr 1
 funext b
 cases b <;> simp only [Bool.false_eq_true,if_false,if_pos rfl,bind_assoc_eq,bind_tc_ok]

theorem encoded (x : QM31Exact) (hx : x≠0) :
 run (encode x)=ok (some (encode x⁻¹),log x) := by
 have hn := NormInverse.quartic_norm_nonzero x hx
 have hi := NHH_CMInverse.fixed (NormInverse.quarticNorm x) hn
 have he : (⟨x.re*(NormInverse.quarticNorm x)⁻¹,
  (-x.im)*(NormInverse.quarticNorm x)⁻¹⟩ : QM31Exact)=x⁻¹ := by
  rw [←NormInverse.quartic_inverse_correct x hx]
  simp only [NormInverse.quarticInverse,NormInverse.complex_inverse_correct _ hn]
 simp only [NormInverse.quarticNorm] at hi
 simp only [run,NHH_QInverse.zero_test,hx,decide_false,bind_tc_ok,Bool.false_eq_true,if_false]
 simp only [encode,NHH_CMAlgebra.square,NHH_CMAlgebra.rotate,NHH_CMAlgebra.subtraction,
 hi,NHH_CMAlgebra.multiply,NHH_CMAlgebra.negation,bind_tc_ok,log,NormInverse.quarticNorm]
 exact congrArg (fun v => ok (some (encode v),log x)) he

theorem zero : run (encode 0)=ok (none,[]) := by
 rw [run,NHH_QInverse.zero_test];rfl

theorem inverse_domain (x : QM31Exact) (hx : x≠0) :
 NHH_CMInverse.Canon (NHH_CMInverse.encode (NormInverse.quarticNorm x)) ∧
 NHH_CMInverse.decode (NHH_CMInverse.encode (NormInverse.quarticNorm x))≠0 := by
 refine ⟨NHH_CMBridge.encoded_canonical _,?_⟩
 have dec (c : CM31Exact) : NHH_CMInverse.decode (NHH_CMInverse.encode c)=c := by
  apply QuadraticAlgebra.ext <;> simp only [NHH_CMInverse.decode,NHH_CMInverse.encode,
   ComplexBaseExecution.encodeBase_val,ZMod.natCast_zmod_val]
 rw [dec]
 exact NormInverse.quartic_norm_nonzero x hx

#print axioms source
#print axioms encoded
#print axioms zero
#print axioms inverse_domain
end NHH_QTrace
end
