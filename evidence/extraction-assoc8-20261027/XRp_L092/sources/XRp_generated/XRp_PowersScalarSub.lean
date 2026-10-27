import XRp_PowersScalar
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace XRp_PowersScalarSub

def wrappingNormalize (x : U32) : Result U32 :=
  if x ≥ 2147483647#u32 then ok (U32.wrapping_sub x 2147483647#u32) else ok x
def checkedNormalize (x : U32) : Result U32 :=
  if x ≥ 2147483647#u32 then do let r ← x-2147483647#u32; ok r else ok x

theorem normalize (x : U32) : wrappingNormalize x = checkedNormalize x := by
  unfold wrappingNormalize checkedNormalize
  by_cases h : x ≥ 2147483647#u32
  · simp only [if_pos h]
    rw [XRp_CheckedWrapping.sub _ _ (by scalar_tac)]
    rfl
  · simp only [if_neg h]

def wrappingSub (x y : U32) := wrappingNormalize (U32.wrapping_sub x y)
def checkedSub (x y : U32) : Result U32 := do let s ← x-y; checkedNormalize s

theorem subtract (x y : U32) (hy : y.val ≤ x.val) : wrappingSub x y = checkedSub x y := by
  unfold checkedSub
  rw [XRp_CheckedWrapping.sub _ _ hy]
  change wrappingNormalize (U32.wrapping_sub x y) = checkedNormalize (U32.wrapping_sub x y)
  exact normalize _

theorem source (a b : U32) : XRn_Join_Field.field.M31.sub a b =
    wrappingSub (U32.wrapping_add a 2147483647#u32) b := by
  simp only [XRn_Join_Field.field.M31.sub,XRn_Join_Field.field.P,
    lift,bind_tc_ok,wrappingSub,wrappingNormalize]
  rfl

theorem target (a b : U32) : AspisR1Qm31ArithmeticProbe.field.M31.sub a b =
    (do let x ← a+2147483647#u32; checkedSub x b) := by
  unfold AspisR1Qm31ArithmeticProbe.field.M31.sub AspisR1Qm31ArithmeticProbe.field.P
  rfl

#print axioms normalize
#print axioms subtract
#print axioms source
#print axioms target
end XRp_PowersScalarSub
