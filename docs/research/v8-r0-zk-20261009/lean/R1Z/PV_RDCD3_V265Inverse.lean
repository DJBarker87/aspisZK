import R1Z.PV_AL_CircleNative
import R1Z.PV_RDCD3_UsizeLoop

namespace R1Z.PV_RDCD3_V265Inverse
set_option autoImplicit false
open Aeneas Aeneas.Std Result PV_AL_CircleOwned
abbrev M := aspis_core.field.M31

/-- No pointer or callback interface is introduced: the squaring operation is
statically the frozen M31 multiplication body at both sides. -/
def squareStep (v : M) (_ : Nat) : Result M := aspis_core.field.M31.mul v v

theorem square_loop (r : core.ops.range.Range Usize) (v : M) :
    aspis_core.field.square_n_loop r v = PV_RDCD3_UsizeLoop.source squareStep r v := rfl

theorem square_count (v : M) (n : Usize) :
    aspis_core.field.square_n v n =
      PV_RDCD3_RangeFold.ordered squareStep n.val 0 v := by
  rw [aspis_core.field.square_n,square_loop]
  exact PV_RDCD3_UsizeLoop.complete squareStep n.val _ v (by simp)

/-- Owned interpretation of the exact deployed addition chain, including the
unconditional assertion at zero. No inverse-totality premise is assumed. -/
def inverse (x : M) : Result M := do
  massert (x != 0#u32)
  let a ← aspis_core.field.M31.mul x x
  let t2 ← aspis_core.field.M31.mul a x
  let a ← PV_RDCD3_RangeFold.ordered squareStep 2 0 t2
  let t4 ← aspis_core.field.M31.mul a t2
  let a ← PV_RDCD3_RangeFold.ordered squareStep 4 0 t4
  let t8 ← aspis_core.field.M31.mul a t4
  let a ← PV_RDCD3_RangeFold.ordered squareStep 8 0 t8
  let t16 ← aspis_core.field.M31.mul a t8
  let a ← PV_RDCD3_RangeFold.ordered squareStep 8 0 t16
  let t24 ← aspis_core.field.M31.mul a t8
  let a ← PV_RDCD3_RangeFold.ordered squareStep 4 0 t24
  let t28 ← aspis_core.field.M31.mul a t4
  let a ← aspis_core.field.M31.mul t28 t28
  let t29 ← aspis_core.field.M31.mul a x
  let t30 ← aspis_core.field.M31.mul t29 t29
  let a ← aspis_core.field.M31.mul t30 t30
  aspis_core.field.M31.mul a x

theorem source (x : M) : aspis_core.field.M31.inv x = inverse x := by
  simp only [aspis_core.field.M31.inv,inverse,square_count]

#print axioms square_loop
#print axioms square_count
#print axioms source
end R1Z.PV_RDCD3_V265Inverse
