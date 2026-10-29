import FIn_WeightsFuns
import FIo_NativeFuns
import LPi_TowerValues
set_option autoImplicit false
namespace NDL_TowerTransport
open Aeneas Aeneas.Std Result
abbrev FC := FIn_WeightsExtract.field.CM31
abbrev FQ := FIn_WeightsExtract.field.QM31
abbrev NC := FIo_Native.aspis_core.field.CM31
abbrev NQ := FIo_Native.aspis_core.field.QM31
def toC (x : FC) : NC := ⟨x.a,x.b⟩
def toQ (x : FQ) : NQ := ⟨toC x.c0,toC x.c1⟩

theorem base_add (x y : U32) : FIn_WeightsExtract.field.M31.add x y =
    FIo_Native.aspis_core.field.M31.add x y := by
  simp [FIn_WeightsExtract.field.M31.add,FIo_Native.aspis_core.field.M31.add,
    FIn_WeightsExtract.field.reduce_u64,FIo_Native.aspis_core.field.reduce_u64,
    FIn_WeightsExtract.field.P,FIo_Native.aspis_core.field.P]
theorem base_sub (x y : U32) : FIn_WeightsExtract.field.M31.sub x y =
    FIo_Native.aspis_core.field.M31.sub x y := by
  simp [FIn_WeightsExtract.field.M31.sub,FIo_Native.aspis_core.field.M31.sub,
    FIn_WeightsExtract.field.reduce_u64,FIo_Native.aspis_core.field.reduce_u64,
    FIn_WeightsExtract.field.P,FIo_Native.aspis_core.field.P]
theorem base_mul (x y : U32) : FIn_WeightsExtract.field.M31.mul x y =
    FIo_Native.aspis_core.field.M31.mul x y := by
  simp [FIn_WeightsExtract.field.M31.mul,FIo_Native.aspis_core.field.M31.mul,
    FIn_WeightsExtract.field.reduce_u64,FIo_Native.aspis_core.field.reduce_u64,
    FIn_WeightsExtract.field.P,FIo_Native.aspis_core.field.P]
theorem base_reduce (x : U64) : FIn_WeightsExtract.field.M31.reduce_u64 x =
    FIo_Native.aspis_core.field.M31.reduce_u64 x := by
  simp [FIn_WeightsExtract.field.M31.reduce_u64,FIo_Native.aspis_core.field.M31.reduce_u64,
    FIn_WeightsExtract.field.reduce_u64,FIo_Native.aspis_core.field.reduce_u64,
    FIn_WeightsExtract.field.P,FIo_Native.aspis_core.field.P]

theorem cm_add (x y : FC) :
    (do let z←FIn_WeightsExtract.field.CM31.add x y;ok (toC z)) =
    FIo_Native.aspis_core.field.CM31.add (toC x) (toC y) := by
  simp only [FIn_WeightsExtract.field.CM31.add,FIo_Native.aspis_core.field.CM31.add,
    toC,base_add,bind_assoc_eq,bind_tc_ok]
theorem cm_sub (x y : FC) :
    (do let z←FIn_WeightsExtract.field.CM31.sub x y;ok (toC z)) =
    FIo_Native.aspis_core.field.CM31.sub (toC x) (toC y) := by
  simp only [FIn_WeightsExtract.field.CM31.sub,FIo_Native.aspis_core.field.CM31.sub,
    toC,base_sub,bind_assoc_eq,bind_tc_ok]
theorem cm_mul (x y : FC) :
    (do let z←FIn_WeightsExtract.field.CM31.mul x y;ok (toC z)) =
    FIo_Native.aspis_core.field.CM31.mul (toC x) (toC y) := by
  simp only [FIn_WeightsExtract.field.CM31.mul,FIo_Native.aspis_core.field.CM31.mul,
    toC,base_mul,base_sub,base_reduce,bind_assoc_eq,bind_tc_ok]
theorem by_r (x : FC) :
    (do let z←FIn_WeightsExtract.field.mul_by_r x;ok (toC z)) =
    FIo_Native.aspis_core.field.mul_by_r (toC x) := by
  simp only [FIn_WeightsExtract.field.mul_by_r,FIo_Native.aspis_core.field.mul_by_r,
    toC,FIn_WeightsExtract.field.M31.double,FIo_Native.aspis_core.field.M31.double,base_add,base_sub,bind_assoc_eq,bind_tc_ok]
theorem qm_mul (x y : FQ) :
    (do let z←FIn_WeightsExtract.field.QM31.mul x y;ok (toQ z)) =
    FIo_Native.aspis_core.field.QM31.mul (toQ x) (toQ y) := by
  simp only [FIn_WeightsExtract.field.QM31.mul,FIo_Native.aspis_core.field.QM31.mul,toQ]
  simp only [← cm_mul,← cm_add,← cm_sub,← by_r,bind_assoc_eq,bind_tc_ok]

#print axioms qm_mul
#print axioms base_add
#print axioms base_sub
#print axioms base_mul
#print axioms base_reduce
#print axioms cm_add
#print axioms cm_sub
#print axioms cm_mul
#print axioms by_r
end NDL_TowerTransport
