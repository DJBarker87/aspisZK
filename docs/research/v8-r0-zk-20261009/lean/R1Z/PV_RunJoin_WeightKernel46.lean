import R1Z.PV_RunJoin_WeightQuartic46
import R1Z.PV_RunJoin_WeightArray46
set_option autoImplicit false
namespace R1Z.PV_RunJoin_WeightKernel46
open Aeneas Aeneas.Std Result
open PV_B2_F_ConstructorCarrier (K to251Q amap)
open PV_RunJoin_WeightMap46 (mapResult)
def toQ (q : K) : PV_RunJoin_WeightCarrier46.MQ :=
  PV_RunJoin_WeightCarrier46.toQ (to251Q q)

theorem copied_add (a b : K) :
    to251Q (PV_B2_C_FieldValue.aspis_core.field.QM31.add a b)=
      PV_B2_C_251FieldValue.aspis_core.field.QM31.add (to251Q a) (to251Q b) := by
  rfl

theorem add (a b : K) :
    AspisR1ProducerRelease47.field.QM31.add (toQ a) (toQ b)=
      mapResult toQ (PV_B2_C_WeightsNative.aspis_core.field.QM31.add a b) := by
  rw [PV_B2_C_FieldTotal.QM31_add]
  change AspisR1ProducerRelease47.field.QM31.add
    (PV_RunJoin_WeightCarrier46.toQ (to251Q a))
    (PV_RunJoin_WeightCarrier46.toQ (to251Q b))=_
  rw [PV_RunJoin_WeightQuartic46.add_value,← copied_add]
  rfl
#print axioms copied_add
#print axioms add

theorem copied_sub (a b : K) :
    to251Q (PV_B2_C_FieldValue.aspis_core.field.QM31.sub a b)=
      PV_B2_C_251FieldValue.aspis_core.field.QM31.sub (to251Q a) (to251Q b) := by
  rfl

theorem sub (a b : K) :
    AspisR1ProducerRelease47.field.QM31.sub (toQ a) (toQ b)=
      mapResult toQ (PV_B2_C_WeightsNative.aspis_core.field.QM31.sub a b) := by
  rw [PV_B2_C_FieldTotal.QM31_sub]
  change AspisR1ProducerRelease47.field.QM31.sub
    (PV_RunJoin_WeightCarrier46.toQ (to251Q a))
    (PV_RunJoin_WeightCarrier46.toQ (to251Q b))=_
  rw [PV_RunJoin_WeightQuartic46.sub_value,← copied_sub]
  rfl
#print axioms copied_sub
#print axioms sub

theorem copied_mul (a b : K) :
    to251Q (PV_B2_C_FieldValue.aspis_core.field.QM31.mul a b)=
      PV_B2_C_251FieldValue.aspis_core.field.QM31.mul (to251Q a) (to251Q b) := by
  rfl

theorem mul (a b : K) :
    AspisR1ProducerRelease47.field.QM31.mul (toQ a) (toQ b)=
      mapResult toQ (PV_B2_C_WeightsNative.aspis_core.field.QM31.mul a b) := by
  rw [PV_B2_C_FieldTotal.QM31_mul]
  change AspisR1ProducerRelease47.field.QM31.mul
    (PV_RunJoin_WeightCarrier46.toQ (to251Q a))
    (PV_RunJoin_WeightCarrier46.toQ (to251Q b))=_
  rw [PV_RunJoin_WeightQuartic46.mul_value,← copied_mul]
  rfl
#print axioms copied_mul
#print axioms mul
end R1Z.PV_RunJoin_WeightKernel46
