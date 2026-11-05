import NHH_CMInverse
set_option autoImplicit false
noncomputable section
namespace NHH_CMSampler
open Aeneas Aeneas.Std Result
open AspisV8R19 AspisV8R15.ExactTowerBase
open ComplexBaseExecution (encodeBase)
open NHH_CMInverse (C encode toSampler)

theorem narrow_roundtrip (x : U64) (hx : x.val≤4294967295) :
 UScalar.cast .U64 (UScalar.cast .U32 x)=x := by
 apply UScalar.eq_of_val_eq
 scalar_tac

theorem raw_product (x y : U64) :
 AspisR72Sampler.field.r23_product_u32_bounded x y=x*y := by
 unfold AspisR72Sampler.field.r23_product_u32_bounded
 simp only [lift,bind_tc_ok]
 split_ifs with hx hy
 · have hxx : x.val≤4294967295 := by scalar_tac
   have hyy : y.val≤4294967295 := by scalar_tac
   rw [narrow_roundtrip x hxx,narrow_roundtrip y hyy]
 · rfl
 · rfl

theorem scalar_add (x y : U32) : NFG_InverseRef.field.M31.add x y=AspisR72Sampler.field.M31.add x y := by
 simp only [NFG_InverseRef.field.M31.add,AspisR72Sampler.field.M31.add,NFG_InverseRef.field.P,AspisR72Sampler.field.P]
theorem scalar_sub (x y : U32) : NFG_InverseRef.field.M31.sub x y=AspisR72Sampler.field.M31.sub x y := by
 simp only [NFG_InverseRef.field.M31.sub,AspisR72Sampler.field.M31.sub,NFG_InverseRef.field.P,AspisR72Sampler.field.P]
theorem scalar_neg (x : U32) : NFG_InverseRef.field.M31.neg x=AspisR72Sampler.field.M31.neg x := by
 simp only [NFG_InverseRef.field.M31.neg,AspisR72Sampler.field.M31.neg,NFG_InverseRef.field.P,AspisR72Sampler.field.P]
theorem scalar_reduce (x : U64) : NFG_InverseRef.field.M31.reduce_u64 x=AspisR72Sampler.field.M31.reduce_u64 x := by
 simp only [NFG_InverseRef.field.M31.reduce_u64,AspisR72Sampler.field.M31.reduce_u64,
 NFG_InverseRef.field.reduce_u64,AspisR72Sampler.field.reduce_u64,NFG_InverseRef.field.P,AspisR72Sampler.field.P]
theorem scalar_double (x : U32) : NFG_InverseRef.field.M31.double x=AspisR72Sampler.field.M31.double x := by
 simp only [NFG_InverseRef.field.M31.double,AspisR72Sampler.field.M31.double,scalar_add]
theorem scalar_multiply (x y : M31Exact) :
 NFG_InverseRef.field.M31.mul (encodeBase x) (encodeBase y)=AspisR72Sampler.field.M31.mul (encodeBase x) (encodeBase y) :=
 (NHH_EncodedScalar.multiply x y).trans (SamplerClosureCircleScalarTransport.mul_encode x y).symm

theorem add_association (x y : C) :
 (do let z ← NFG_InverseRef.field.CM31.add x y;ok (toSampler z))=
 AspisR72Sampler.field.CM31.add (toSampler x) (toSampler y) := by
 simp only [NFG_InverseRef.field.CM31.add,AspisR72Sampler.field.CM31.add,
 scalar_add,toSampler,bind_assoc_eq,bind_tc_ok]
theorem sub_association (x y : C) :
 (do let z ← NFG_InverseRef.field.CM31.sub x y;ok (toSampler z))=
 AspisR72Sampler.field.CM31.sub (toSampler x) (toSampler y) := by
 simp only [NFG_InverseRef.field.CM31.sub,AspisR72Sampler.field.CM31.sub,
 scalar_sub,toSampler,bind_assoc_eq,bind_tc_ok]
theorem neg_association (x : C) :
 (do let z ← NFG_InverseRef.field.CM31.neg x;ok (toSampler z))=
 AspisR72Sampler.field.CM31.neg (toSampler x) := by
 simp only [NFG_InverseRef.field.CM31.neg,AspisR72Sampler.field.CM31.neg,
 scalar_neg,toSampler,bind_assoc_eq,bind_tc_ok]
theorem mul_association (x y : CM31Exact) :
 (do let z ← NFG_InverseRef.field.CM31.mul (encode x) (encode y);ok (toSampler z))=
 AspisR72Sampler.field.CM31.mul (SamplerClosureProductExecution.encodeCM x)
 (SamplerClosureProductExecution.encodeCM y) := by
 simp only [NFG_InverseRef.field.CM31.mul,AspisR72Sampler.field.CM31.mul,
  encode,SamplerClosureProductExecution.encodeCM,scalar_multiply,scalar_sub,scalar_reduce,
  raw_product,toSampler,bind_assoc_eq,bind_tc_ok]
theorem square_association (x : CM31Exact) :
 (do let z ← NFG_InverseRef.field.CM31.square (encode x);ok (toSampler z))=
 AspisR72Sampler.field.CM31.square (SamplerClosureProductExecution.encodeCM x) := by
 simp only [NFG_InverseRef.field.CM31.square,AspisR72Sampler.field.CM31.square,
  encode,SamplerClosureProductExecution.encodeCM,scalar_multiply,scalar_double,scalar_reduce,
  raw_product,NFG_InverseRef.field.P,AspisR72Sampler.field.P,toSampler,bind_assoc_eq,bind_tc_ok]
theorem rotate_association (x : C) :
 (do let z ← NFG_InverseRef.field.mul_by_r x;ok (toSampler z))=
 AspisR72Sampler.field.mul_by_r (toSampler x) := by
 simp only [NFG_InverseRef.field.mul_by_r,AspisR72Sampler.field.mul_by_r,
 scalar_add,scalar_sub,scalar_double,toSampler,bind_assoc_eq,bind_tc_ok]

#print axioms narrow_roundtrip
#print axioms raw_product
#print axioms scalar_add
#print axioms scalar_sub
#print axioms scalar_neg
#print axioms scalar_reduce
#print axioms scalar_double
#print axioms scalar_multiply
#print axioms add_association
#print axioms sub_association
#print axioms neg_association
#print axioms mul_association
#print axioms square_association
#print axioms rotate_association
end NHH_CMSampler
end
