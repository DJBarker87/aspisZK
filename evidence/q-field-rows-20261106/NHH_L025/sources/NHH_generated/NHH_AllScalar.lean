import NHH_CMSampler
set_option autoImplicit false
noncomputable section
namespace NHH_AllScalar
open Aeneas Aeneas.Std Result
open AspisV8R19 AspisV8R15.ExactTowerBase
open ComplexBaseExecution (encodeBase)

theorem multiply (x y : U32) :
 NFG_InverseRef.field.M31.mul x y=AspisR72Sampler.field.M31.mul x y := by
 by_cases hx : x<2147483647#u32
 · by_cases hy : y<2147483647#u32
   · have cx : x.val<2147483647 := by scalar_tac
     have cy : y.val<2147483647 := by scalar_tac
     have ex : encodeBase (x.val : M31Exact)=x := by
      apply UScalar.eq_of_val_eq
      simp only [ComplexBaseExecution.encodeBase_val,ZMod.val_natCast_of_lt cx]
     have ey : encodeBase (y.val : M31Exact)=y := by
      apply UScalar.eq_of_val_eq
      simp only [ComplexBaseExecution.encodeBase_val,ZMod.val_natCast_of_lt cy]
     rw [←ex,←ey]
     exact NHH_CMSampler.scalar_multiply _ _
   · simp only [NFG_InverseRef.field.M31.mul,AspisR72Sampler.field.M31.mul,
       NFG_InverseRef.field.P,AspisR72Sampler.field.P,hx,hy,if_pos,if_neg,if_false,if_true,
       NFG_InverseRef.field.reduce_u64,AspisR72Sampler.field.reduce_u64]
 · simp only [NFG_InverseRef.field.M31.mul,AspisR72Sampler.field.M31.mul,
       NFG_InverseRef.field.P,AspisR72Sampler.field.P,hx,if_neg,if_false,if_true,
       NFG_InverseRef.field.reduce_u64,AspisR72Sampler.field.reduce_u64]

theorem body (i : core.ops.range.Range Usize) (x : U32) :
 NFG_InverseRef.field.square_n_loop.body i x=AspisR72Sampler.field.square_n_loop.body i x := by
 simp only [NFG_InverseRef.field.square_n_loop.body,AspisR72Sampler.field.square_n_loop.body,multiply]
 rfl

theorem square (x : U32) (n : Usize) :
 NFG_InverseRef.field.square_n x n=AspisR72Sampler.field.square_n x n := by
 simp only [NFG_InverseRef.field.square_n,NFG_InverseRef.field.square_n_loop,
 AspisR72Sampler.field.square_n,AspisR72Sampler.field.square_n_loop,body]

theorem inverse (x : U32) :
 NFG_InverseRef.field.M31.inv x=AspisR72Sampler.field.M31.inv x := by
 simp only [NFG_InverseRef.field.M31.inv,AspisR72Sampler.field.M31.inv,multiply,square]

#print axioms multiply
#print axioms body
#print axioms square
#print axioms inverse
end NHH_AllScalar
end
