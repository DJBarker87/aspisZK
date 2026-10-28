import R1Z.PV_RunJoin_WeightComplex46
import R1Z.PV_RunJoin_WeightMap46
set_option autoImplicit false
namespace R1Z.PV_RunJoin_WeightQuartic46
open Aeneas Aeneas.Std Result PV_RunJoin_WeightCarrier46
open PV_RunJoin_WeightMap46 (mapResult)

theorem add_value (a b : Q) :
    AspisR1ProducerRelease47.field.QM31.add (toQ a) (toQ b)=
      ok (toQ (PV_B2_C_251FieldValue.aspis_core.field.QM31.add a b)) := by
  change AspisR1ProducerRelease47.field.QM31.add
    ⟨PV_RunJoin_WeightComplex46.toC a.c0,PV_RunJoin_WeightComplex46.toC a.c1⟩
    ⟨PV_RunJoin_WeightComplex46.toC b.c0,PV_RunJoin_WeightComplex46.toC b.c1⟩=_
  simp only [AspisR1ProducerRelease47.field.QM31.add,
    PV_B2_C_251FieldValue.aspis_core.field.QM31.add,PV_RunJoin_WeightComplex46.add,bind_tc_ok] <;> rfl

theorem add (a b : Q) :
    AspisR1ProducerRelease47.field.QM31.add (toQ a) (toQ b)=
      mapResult toQ (PV_B2_251c1.aspis_core.field.QM31.add a b) := by
  rw [PV_B2_C_251FieldTotal.QM31_add]
  exact add_value a b
#print axioms add_value
#print axioms add

theorem sub_value (a b : Q) :
    AspisR1ProducerRelease47.field.QM31.sub (toQ a) (toQ b)=
      ok (toQ (PV_B2_C_251FieldValue.aspis_core.field.QM31.sub a b)) := by
  change AspisR1ProducerRelease47.field.QM31.sub
    ⟨PV_RunJoin_WeightComplex46.toC a.c0,PV_RunJoin_WeightComplex46.toC a.c1⟩
    ⟨PV_RunJoin_WeightComplex46.toC b.c0,PV_RunJoin_WeightComplex46.toC b.c1⟩=_
  simp only [AspisR1ProducerRelease47.field.QM31.sub,
    PV_B2_C_251FieldValue.aspis_core.field.QM31.sub,PV_RunJoin_WeightComplex46.sub,bind_tc_ok] <;> rfl

theorem sub (a b : Q) :
    AspisR1ProducerRelease47.field.QM31.sub (toQ a) (toQ b)=
      mapResult toQ (PV_B2_251c1.aspis_core.field.QM31.sub a b) := by
  rw [PV_B2_C_251FieldTotal.QM31_sub]
  exact sub_value a b
#print axioms sub_value
#print axioms sub

theorem mul_value (a b : Q) :
    AspisR1ProducerRelease47.field.QM31.mul (toQ a) (toQ b)=
      ok (toQ (PV_B2_C_251FieldValue.aspis_core.field.QM31.mul a b)) := by
  change AspisR1ProducerRelease47.field.QM31.mul
    ⟨PV_RunJoin_WeightComplex46.toC a.c0,PV_RunJoin_WeightComplex46.toC a.c1⟩
    ⟨PV_RunJoin_WeightComplex46.toC b.c0,PV_RunJoin_WeightComplex46.toC b.c1⟩=_
  simp only [AspisR1ProducerRelease47.field.QM31.mul,
    PV_B2_C_251FieldValue.aspis_core.field.QM31.mul,PV_RunJoin_WeightComplex46.mul,PV_RunJoin_WeightComplex46.add,PV_RunJoin_WeightComplex46.sub,PV_RunJoin_WeightComplex46.r_mul,bind_tc_ok] <;> rfl

theorem mul (a b : Q) :
    AspisR1ProducerRelease47.field.QM31.mul (toQ a) (toQ b)=
      mapResult toQ (PV_B2_251c1.aspis_core.field.QM31.mul a b) := by
  rw [PV_B2_C_251FieldTotal.QM31_mul]
  exact mul_value a b
#print axioms mul_value
#print axioms mul
theorem one : AspisR1ProducerRelease47.field.QM31.ONE=
    toQ PV_B2_251c1.aspis_core.field.QM31.ONE := by
  unfold AspisR1ProducerRelease47.field.QM31.ONE PV_B2_251c1.aspis_core.field.QM31.ONE
  rfl

theorem zero : AspisR1ProducerRelease47.field.QM31.ZERO=
    toQ PV_B2_251c1.aspis_core.field.QM31.ZERO := by
  unfold AspisR1ProducerRelease47.field.QM31.ZERO PV_B2_251c1.aspis_core.field.QM31.ZERO
  rfl
#print axioms one
#print axioms zero
end R1Z.PV_RunJoin_WeightQuartic46
