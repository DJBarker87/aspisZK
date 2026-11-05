import NHH_CMSampler
set_option autoImplicit false
noncomputable section
namespace NHH_CMAlgebra
open Aeneas Aeneas.Std Result
open AspisV8R19 AspisV8R15.ExactTowerBase
open NHH_CMInverse (C encode toSampler)

theorem injective : Function.Injective toSampler := by
 intro x y h
 cases x;cases y;cases h;rfl

theorem unmap (r : Result C) (out : C)
 (h : (do let z ← r;ok (toSampler z))=ok (toSampler out)) : r=ok out := by
 cases r with
 | ok v => exact congrArg Result.ok (injective (Result.ok.inj h))
 | fail e => cases h
 | div => cases h

theorem addition (x y : CM31Exact) :
 NFG_InverseRef.field.CM31.add (encode x) (encode y)=ok (encode (x+y)) := by
 apply unmap
 rw [NHH_CMSampler.add_association]
 exact SamplerClosureCircleFieldExecution.cm_add x y

theorem subtraction (x y : CM31Exact) :
 NFG_InverseRef.field.CM31.sub (encode x) (encode y)=ok (encode (x-y)) := by
 apply unmap
 rw [NHH_CMSampler.sub_association]
 exact SamplerClosureCircleFieldExecution.cm_sub x y

theorem negation (x : CM31Exact) :
 NFG_InverseRef.field.CM31.neg (encode x)=ok (encode (-x)) := by
 apply unmap
 rw [NHH_CMSampler.neg_association]
 exact SamplerClosureCircleFieldExecution.cm_neg x

theorem multiply (x y : CM31Exact) :
 NFG_InverseRef.field.CM31.mul (encode x) (encode y)=ok (encode (x*y)) := by
 apply unmap
 rw [NHH_CMSampler.mul_association]
 exact SamplerClosureCircleFieldExecution.cm_mul x y

theorem square (x : CM31Exact) :
 NFG_InverseRef.field.CM31.square (encode x)=ok (encode (x*x)) := by
 apply unmap
 rw [NHH_CMSampler.square_association]
 exact SamplerClosureCircleFieldExecution.cm_square x

theorem rotate (x : CM31Exact) :
 NFG_InverseRef.field.mul_by_r (encode x)=ok (encode (qm31R*x)) := by
 apply unmap
 rw [NHH_CMSampler.rotate_association]
 exact SamplerClosureCircleFieldExecution.cm_mul_r x

#print axioms injective
#print axioms unmap
#print axioms addition
#print axioms subtraction
#print axioms negation
#print axioms multiply
#print axioms square
#print axioms rotate
end NHH_CMAlgebra
end
