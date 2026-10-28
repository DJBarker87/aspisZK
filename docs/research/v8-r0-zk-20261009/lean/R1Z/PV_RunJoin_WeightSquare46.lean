import R1Z.PV_RunJoin_WeightQuartic46
import AspisR1ProducerRelease47.Kernels49
set_option autoImplicit false
namespace R1Z.PV_RunJoin_WeightSquare46
open Aeneas Aeneas.Std Result PV_RunJoin_WeightCarrier46
open PV_RunJoin_WeightComplex46 (C toC)
open PV_RunJoin_WeightMap46 (mapResult map_bind)

theorem complex (x : C) :
    AspisR1ProducerRelease47.field.CM31.square (toC x)=
      mapResult toC (PV_B2_251c1.aspis_core.field.CM31.square x) := by
  simp only [AspisR1ProducerRelease47.field.CM31.square,
    PV_B2_251c1.aspis_core.field.CM31.square,toC,
    PV_RunJoin_WeightScalar46.reduce_m31,PV_RunJoin_WeightScalar46.mul,
    PV_RunJoin_WeightScalar46.double,PV_B2_C_251FieldTotal.M31_reduce_u64,
    PV_B2_C_251FieldTotal.M31_mul,PV_B2_C_251FieldTotal.M31_double,
    AspisR1ProducerRelease47.field.P,PV_B2_251c1.aspis_core.field.P,
    lift,bind_tc_ok,mapResult,PV_B2_E_OrdinaryOriginal.mapResult]

theorem complex_add (x y : C) :
    AspisR1ProducerRelease47.field.CM31.add (toC x) (toC y)=
      mapResult toC (PV_B2_251c1.aspis_core.field.CM31.add x y) := by
  rw [PV_B2_C_251FieldTotal.CM31_add]
  exact PV_RunJoin_WeightComplex46.add x y

theorem complex_mul (x y : C) :
    AspisR1ProducerRelease47.field.CM31.mul (toC x) (toC y)=
      mapResult toC (PV_B2_251c1.aspis_core.field.CM31.mul x y) := by
  rw [PV_B2_C_251FieldTotal.CM31_mul]
  exact PV_RunJoin_WeightComplex46.mul x y

theorem complex_r (x : C) :
    AspisR1ProducerRelease47.field.mul_by_r (toC x)=
      mapResult toC (PV_B2_251c1.aspis_core.field.mul_by_r x) := by
  rw [PV_B2_C_251FieldTotal.mul_by_r]
  exact PV_RunJoin_WeightComplex46.r_mul x

theorem complete (x : Q) :
    AspisR1ProducerRelease47.field.QM31.square (toQ x)=
      mapResult toQ (PV_B2_251c1.aspis_core.field.QM31.square x) := by
  change AspisR1ProducerRelease47.field.QM31.square ⟨toC x.c0,toC x.c1⟩=_
  unfold AspisR1ProducerRelease47.field.QM31.square PV_B2_251c1.aspis_core.field.QM31.square
  symm
  rw [complex]
  apply map_bind toC toQ
  intro s0
  rw [complex]
  apply map_bind toC toQ
  intro s1
  rw [complex_r]
  apply map_bind toC toQ
  intro r
  rw [complex_add]
  apply map_bind toC toQ
  intro lo
  rw [complex_mul]
  apply map_bind toC toQ
  intro xy
  unfold AspisR1ProducerRelease47.field.CM31.double PV_B2_251c1.aspis_core.field.CM31.double
  rw [complex_add]
  apply map_bind toC toQ
  intro hi
  rfl
#print axioms complex
#print axioms complex_add
#print axioms complex_mul
#print axioms complex_r
#print axioms complete
end R1Z.PV_RunJoin_WeightSquare46
