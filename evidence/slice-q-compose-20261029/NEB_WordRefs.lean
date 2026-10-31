import NEB_AdditiveRef.Funs
import NEB_BaseCallBounds
set_option autoImplicit false
namespace NEB_WordRefs
open Aeneas Aeneas.Std Result AspisR1

theorem add (x y : U32) :
    NEB_AdditiveRef.add_word x y=FIo_Native.aspis_core.field.M31.add x y := by
  simp only [NEB_AdditiveRef.add_word,NEB_AdditiveRef.P,
    FIo_Native.aspis_core.field.M31.add,FIo_Native.aspis_core.field.P,
    core.num.U32.wrapping_add,core.num.U32.wrapping_sub,
    U32.wrapping_add,U32.wrapping_sub,lift,bind_tc_ok]

theorem sub (x y : U32) :
    NEB_AdditiveRef.sub_word x y=FIo_Native.aspis_core.field.M31.sub x y := by
  simp only [NEB_AdditiveRef.sub_word,NEB_AdditiveRef.P,
    FIo_Native.aspis_core.field.M31.sub,FIo_Native.aspis_core.field.P,
    core.num.U32.wrapping_add,core.num.U32.wrapping_sub,
    U32.wrapping_add,U32.wrapping_sub,lift,bind_tc_ok]

theorem double (x : U32) :
    NEB_AdditiveRef.add_word x x=FIo_Native.aspis_core.field.M31.double x := by
  rw [add]
  rfl

theorem normalize (x : U32) :
    NEB_AdditiveRef.normalize_word x=x%2147483647#u32 := by
  simp only [NEB_AdditiveRef.normalize_word,NEB_AdditiveRef.P]

theorem normalize_value (x : U32) : ∃ z,
    NEB_AdditiveRef.normalize_word x=ok z ∧
    z.val=x.val%2147483647 ∧ z.val<2147483647 := by
  obtain ⟨z,run,value⟩ := NBG_WideCarriers.remainder x
  exact ⟨z,(normalize x).trans run,value,by rw [value];exact Nat.mod_lt _ (by decide)⟩

#print axioms add
#print axioms sub
#print axioms double
#print axioms normalize
#print axioms normalize_value
end NEB_WordRefs
