import NEO_TailReference
import NEB_PureFrame
set_option autoImplicit false
namespace NEO_InverseLog
open Aeneas Aeneas.Std Result AspisR1
inductive Call where
 | product (left right reply : U32)
 | square (input : U32) (count : Usize) (reply : U32)

def legal : Call → Prop
 | .product a b r => FIo_Native.aspis_core.field.M31.mul a b=ok r ∧ r.val<2147483647
 | .square a n r => AspisR1M31Inverse.field.square_n FIo_Native.aspis_core.field.M31.mul a n=ok r ∧ r.val<2147483647

def chain (x m t2 m1 t4 m2 t8 m3 t16 m4 t24 m5 t28 m6 t29 t30 m7 out : U32) : List Call :=
 [.product x x m,.product m x t2,.square t2 2#usize m1,.product m1 t2 t4,
  .square t4 4#usize m2,.product m2 t4 t8,.square t8 8#usize m3,.product m3 t8 t16,
  .square t16 8#usize m4,.product m4 t8 t24,.square t24 4#usize m5,.product m5 t4 t28,
  .product t28 t28 m6,.product m6 x t29,.product t29 t29 t30,
  .product t30 t30 m7,.product m7 x out]

theorem nonzero (x : U32) (nonzero : x != 0#u32) :
 ∃ m t2 m1 t4 m2 t8 m3 t16 m4 t24 m5 t28 m6 t29 t30 m7 out : U32,
 let calls := chain x m t2 m1 t4 m2 t8 m3 t16 m4 t24 m5 t28 m6 t29 t30 m7 out
 calls.length=17 ∧ (∀ call∈calls,legal call) ∧
 NEO_TailRef.inverse NEO_TailReference.inverseOps x=ok out ∧ out.val<2147483647 := by
 obtain ⟨m,t2,m1,t4,m2,t8,m3,t16,m4,t24,m5,t28,m6,t29,t30,m7,out,
 hm,cm,ht2,ct2,hm1,cm1,ht4,ct4,hm2,cm2,ht8,ct8,hm3,cm3,ht16,ct16,
 hm4,cm4,ht24,ct24,hm5,cm5,ht28,ct28,hm6,cm6,ht29,ct29,ht30,ct30,hm7,cm7,hout,cout,run⟩ :=
 NEB_InverseCalls.nonzero x nonzero
 refine ⟨m,t2,m1,t4,m2,t8,m3,t16,m4,t24,m5,t28,m6,t29,t30,m7,out,?_,?_,?_,cout⟩
 · rfl
 · intro call member
   simp only [chain,List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
   all_goals simp_all only [legal]
 · rw [NEO_TailReference.inverse]
   exact run

theorem zero : NEO_TailRef.inverse NEO_TailReference.inverseOps 0#u32=fail .assertionFailure := by
 simp [NEO_TailRef.inverse,massert]

#print axioms nonzero
#print axioms zero
end NEO_InverseLog
