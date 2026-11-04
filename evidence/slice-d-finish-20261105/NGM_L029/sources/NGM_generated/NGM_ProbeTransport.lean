import FIn_WeightsFuns
import AspisR1SelectedMaskProbe.Funs

set_option autoImplicit false
namespace NGM_ProbeTransport
open Aeneas Aeneas.Std Result
abbrev FC := FIn_WeightsExtract.field.CM31
abbrev FQ := FIn_WeightsExtract.field.QM31
abbrev NC := AspisR1SelectedMaskProbe.field.CM31
abbrev NQ := AspisR1SelectedMaskProbe.field.QM31
def toC (x : FC) : NC := ⟨x.a,x.b⟩
def toQ (x : FQ) : NQ := ⟨toC x.c0,toC x.c1⟩

theorem base_add (x y : U32) : FIn_WeightsExtract.field.M31.add x y =
    AspisR1SelectedMaskProbe.field.M31.add x y := by
  simp [FIn_WeightsExtract.field.M31.add,AspisR1SelectedMaskProbe.field.M31.add,
    FIn_WeightsExtract.field.reduce_u64,AspisR1SelectedMaskProbe.field.reduce_u64,
    FIn_WeightsExtract.field.P,AspisR1SelectedMaskProbe.field.P]
theorem base_sub (x y : U32) : FIn_WeightsExtract.field.M31.sub x y =
    AspisR1SelectedMaskProbe.field.M31.sub x y := by
  simp [FIn_WeightsExtract.field.M31.sub,AspisR1SelectedMaskProbe.field.M31.sub,
    FIn_WeightsExtract.field.reduce_u64,AspisR1SelectedMaskProbe.field.reduce_u64,
    FIn_WeightsExtract.field.P,AspisR1SelectedMaskProbe.field.P]
theorem base_mul (x y : U32) : FIn_WeightsExtract.field.M31.mul x y =
    AspisR1SelectedMaskProbe.field.M31.mul x y := by
  simp [FIn_WeightsExtract.field.M31.mul,AspisR1SelectedMaskProbe.field.M31.mul,
    FIn_WeightsExtract.field.reduce_u64,AspisR1SelectedMaskProbe.field.reduce_u64,
    FIn_WeightsExtract.field.P,AspisR1SelectedMaskProbe.field.P]
theorem base_reduce (x : U64) : FIn_WeightsExtract.field.M31.reduce_u64 x =
    AspisR1SelectedMaskProbe.field.M31.reduce_u64 x := by
  simp [FIn_WeightsExtract.field.M31.reduce_u64,AspisR1SelectedMaskProbe.field.M31.reduce_u64,
    FIn_WeightsExtract.field.reduce_u64,AspisR1SelectedMaskProbe.field.reduce_u64,
    FIn_WeightsExtract.field.P,AspisR1SelectedMaskProbe.field.P]

theorem cm_add (x y : FC) :
    (do let z←FIn_WeightsExtract.field.CM31.add x y;ok (toC z)) =
    AspisR1SelectedMaskProbe.field.CM31.add (toC x) (toC y) := by
  simp only [FIn_WeightsExtract.field.CM31.add,AspisR1SelectedMaskProbe.field.CM31.add,
    toC,base_add,bind_assoc_eq,bind_tc_ok]
theorem cm_sub (x y : FC) :
    (do let z←FIn_WeightsExtract.field.CM31.sub x y;ok (toC z)) =
    AspisR1SelectedMaskProbe.field.CM31.sub (toC x) (toC y) := by
  simp only [FIn_WeightsExtract.field.CM31.sub,AspisR1SelectedMaskProbe.field.CM31.sub,
    toC,base_sub,bind_assoc_eq,bind_tc_ok]
theorem cm_mul (x y : FC) :
    (do let z←FIn_WeightsExtract.field.CM31.mul x y;ok (toC z)) =
    AspisR1SelectedMaskProbe.field.CM31.mul (toC x) (toC y) := by
  simp only [FIn_WeightsExtract.field.CM31.mul,AspisR1SelectedMaskProbe.field.CM31.mul,
    toC,base_mul,base_sub,base_reduce,bind_assoc_eq,bind_tc_ok]
theorem by_r (x : FC) :
    (do let z←FIn_WeightsExtract.field.mul_by_r x;ok (toC z)) =
    AspisR1SelectedMaskProbe.field.mul_by_r (toC x) := by
  simp only [FIn_WeightsExtract.field.mul_by_r,AspisR1SelectedMaskProbe.field.mul_by_r,
    toC,FIn_WeightsExtract.field.M31.double,AspisR1SelectedMaskProbe.field.M31.double,base_add,base_sub,bind_assoc_eq,bind_tc_ok]
theorem qm_mul (x y : FQ) :
    (do let z←FIn_WeightsExtract.field.QM31.mul x y;ok (toQ z)) =
    AspisR1SelectedMaskProbe.field.QM31.mul (toQ x) (toQ y) := by
  simp only [FIn_WeightsExtract.field.QM31.mul,AspisR1SelectedMaskProbe.field.QM31.mul,toQ]
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
end NGM_ProbeTransport
