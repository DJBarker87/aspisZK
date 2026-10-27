import R1Z.PV_Inv_NativeNormC
set_option autoImplicit false
namespace R1Z.PV_Inv_NativeScalar
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitM31Ops48

theorem decode_injective (x y : U32) (hx : canonical x) (hy : canonical y)
    (he : decode x=decode y) : x=y := by
  apply UScalar.eq_of_val_eq
  have hv := congrArg ZMod.val he
  change x.val % P = y.val % P at hv
  simpa only [Nat.mod_eq_of_lt hx,Nat.mod_eq_of_lt hy] using hv

theorem sub_nonzero (x y : U32) (hx : canonical x) (hy : canonical y) (hne : x ≠ y) :
    ∃ d : U32, field.M31.sub x y=ok d ∧ canonical d ∧ decode d ≠ 0 := by
  obtain ⟨d,hd,hc,hv⟩ := sub_exact x y hx hy
  refine ⟨d,hd,hc,?_⟩
  rw [hv]
  exact sub_ne_zero.mpr (fun he => hne (decode_injective x y hx hy he))

theorem mul_nonzero (x y : U32) (hx : decode x ≠ 0) (hy : decode y ≠ 0) :
    ∃ d : U32, field.M31.mul x y=ok d ∧ canonical d ∧ decode d ≠ 0 := by
  obtain ⟨d,hd,hc,hv⟩ := mul_exact x y
  exact ⟨d,hd,hc,by rw [hv]; exact mul_ne_zero hx hy⟩

#print axioms decode_injective
#print axioms sub_nonzero
#print axioms mul_nonzero
end R1Z.PV_Inv_NativeScalar
