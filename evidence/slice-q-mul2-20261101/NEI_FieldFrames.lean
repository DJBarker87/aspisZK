import NEI_FieldWide
set_option autoImplicit false
noncomputable section
namespace NEI_FieldFrames
open Aeneas Aeneas.Std Result NEI_FieldCarriers
open AspisR1PublicPreparation.RawExtractedSemanticCallOpsV20
def run {A B S Event : Type} (map:A→B) (state:S) (result:Result A) : Result (B × S × List Event) := do
 let value ← result;ok (map value,state,[])
theorem mapped {A B S Event : Type} (map:A→B) (state:S) (actual:Result A) (model:Result B)
 (same:resultMap map actual=model) :
 run (Event:=Event) map state actual=run (Event:=Event) id state model := by
 rw [← same];cases actual <;> rfl
theorem widen (x:U32) : (core.convert.num.FromU64U32.from x).val=x.val := by
 change (UScalar.cast .U64 x).val=x.val
 rw [UScalar.cast_val_eq]
 apply Nat.mod_eq_of_lt
 have bound:=x.hSize
 norm_num [UScalar.size,UScalarTy.numBits,U32.size,U32.numBits,U64.size,U64.numBits] at bound ⊢
 omega
theorem m_add {S Event:Type} (state:S) (x y:U32) :
 run (Event:=Event) id state (NEI_LineFull.aspis_core.field.M31.add x y) =
 run (Event:=Event) id state (AspisR1CurrentWide.field.M31.add x y) := by
 rw [NEI_FieldScalar.m_add]
#print axioms m_add
theorem m_sub {S Event:Type} (state:S) (x y:U32) :
 run (Event:=Event) id state (NEI_LineFull.aspis_core.field.M31.sub x y) =
 run (Event:=Event) id state (AspisR1CurrentWide.field.M31.sub x y) := by
 rw [NEI_FieldScalar.m_sub]
#print axioms m_sub
theorem m_double {S Event:Type} (state:S) (x:U32) :
 run (Event:=Event) id state (NEI_LineFull.aspis_core.field.M31.double x) =
 run (Event:=Event) id state (AspisR1CurrentWide.field.M31.double x) := by
 rw [NEI_FieldScalar.m_double]
#print axioms m_double
theorem reduce {S Event:Type} (state:S) (x:U64) :
 run (Event:=Event) id state (NEI_LineFull.aspis_core.field.reduce_u64 x) =
 run (Event:=Event) id state (AspisR1CurrentWide.field.reduce_u64 x) := by
 rw [NEI_FieldScalar.reduce]
#print axioms reduce
theorem m_reduce {S Event:Type} (state:S) (x:U64) :
 run (Event:=Event) id state (NEI_LineFull.aspis_core.field.M31.reduce_u64 x) =
 run (Event:=Event) id state (AspisR1CurrentWide.field.M31.reduce_u64 x) := by
 rw [NEI_FieldScalar.m_reduce_u64]
#print axioms m_reduce
theorem m_mul {S Event:Type} (state:S) (x y:U32) :
 run (Event:=Event) id state (NEI_LineFull.aspis_core.field.M31.mul x y) =
 run (Event:=Event) id state (AspisR1CurrentWide.field.M31.mul x y) := by
 rw [NEI_FieldScalar.m_mul]
#print axioms m_mul
theorem cm_add {S Event:Type} (state:S) (x y:N.C) :
 run (Event:=Event) toC state (NEI_LineFull.aspis_core.field.CM31.add x y) =
 run (Event:=Event) id state (AspisR1CurrentWide.field.CM31.add (toC x) (toC y)) := by
 exact mapped toC state _ _ (NEI_FieldCM.cm_add x y)
#print axioms cm_add
theorem cm_sub {S Event:Type} (state:S) (x y:N.C) :
 run (Event:=Event) toC state (NEI_LineFull.aspis_core.field.CM31.sub x y) =
 run (Event:=Event) id state (AspisR1CurrentWide.field.CM31.sub (toC x) (toC y)) := by
 exact mapped toC state _ _ (NEI_FieldCM.cm_sub x y)
#print axioms cm_sub
theorem cm_mul {S Event:Type} (state:S) (x y:N.C) :
 run (Event:=Event) toC state (NEI_LineFull.aspis_core.field.CM31.mul x y) =
 run (Event:=Event) id state (AspisR1CurrentWide.field.CM31.mul (toC x) (toC y)) := by
 exact mapped toC state _ _ (NEI_FieldCM.cm_mul x y)
#print axioms cm_mul
theorem cm_mul_m31 {S Event:Type} (state:S) (x:N.C) (y:U32) :
 run (Event:=Event) toC state (NEI_LineFull.aspis_core.field.CM31.mul_m31 x y) =
 run (Event:=Event) id state (AspisR1CurrentWide.field.CM31.mul_m31 (toC x) y) := by
 exact mapped toC state _ _ (NEI_FieldCM.cm_mul_m31 x y)
#print axioms cm_mul_m31
theorem by_r {S Event:Type} (state:S) (x:N.C) :
 run (Event:=Event) toC state (NEI_LineFull.aspis_core.field.mul_by_r x) =
 run (Event:=Event) id state (AspisR1CurrentWide.field.mul_by_r (toC x)) := by
 exact mapped toC state _ _ (NEI_FieldCM.by_r x)
#print axioms by_r
theorem qm_add {S Event:Type} (state:S) (x y:N.Q) :
 run (Event:=Event) toQ state (NEI_LineFull.aspis_core.field.QM31.add x y) =
 run (Event:=Event) id state (AspisR1CurrentWide.field.QM31.add (toQ x) (toQ y)) := by
 exact mapped toQ state _ _ (NEI_FieldQM.qm_add x y)
#print axioms qm_add
theorem qm_sub {S Event:Type} (state:S) (x y:N.Q) :
 run (Event:=Event) toQ state (NEI_LineFull.aspis_core.field.QM31.sub x y) =
 run (Event:=Event) id state (AspisR1CurrentWide.field.QM31.sub (toQ x) (toQ y)) := by
 exact mapped toQ state _ _ (NEI_FieldQM.qm_sub x y)
#print axioms qm_sub
theorem qm_mul {S Event:Type} (state:S) (x y:N.Q) :
 run (Event:=Event) toQ state (NEI_LineFull.aspis_core.field.QM31.mul x y) =
 run (Event:=Event) id state (AspisR1CurrentWide.field.QM31.mul (toQ x) (toQ y)) := by
 exact mapped toQ state _ _ (NEI_FieldQM.qm_mul x y)
#print axioms qm_mul
theorem qm_mul_m31 {S Event:Type} (state:S) (x:N.Q) (y:U32) :
 run (Event:=Event) toQ state (NEI_LineFull.aspis_core.field.QM31.mul_m31 x y) =
 run (Event:=Event) id state (AspisR1CurrentWide.field.QM31.mul_m31 (toQ x) y) := by
 exact mapped toQ state _ _ (NEI_FieldQM.qm_mul_m31 x y)
#print axioms qm_mul_m31
theorem mul_u {S Event:Type} (state:S) (x:N.Q) :
 run (Event:=Event) toQ state (NEI_LineFull.aspis_core.field.wide_exact.mul_u x) =
 run (Event:=Event) id state (AspisR1CurrentWide.field.wide_exact.mul_u (toQ x)) := by
 exact mapped toQ state _ _ (NEI_FieldQM.mul_u x)
#print axioms mul_u
theorem wide_add {S Event:Type} (state:S) (x y:N.E) :
 run (Event:=Event) toE state (NEI_LineFull.aspis_core.field.wide_exact.WideExact.add x y) =
 run (Event:=Event) id state (AspisR1CurrentWide.field.wide_exact.WideExact.add (toE x) (toE y)) := by
 exact mapped toE state _ _ (NEI_FieldWide.wide_add x y)
#print axioms wide_add
theorem wide_sub {S Event:Type} (state:S) (x y:N.E) :
 run (Event:=Event) toE state (NEI_LineFull.aspis_core.field.wide_exact.WideExact.sub x y) =
 run (Event:=Event) id state (AspisR1CurrentWide.field.wide_exact.WideExact.sub (toE x) (toE y)) := by
 exact mapped toE state _ _ (NEI_FieldWide.wide_sub x y)
#print axioms wide_sub
theorem wide_mul {S Event:Type} (state:S) (x y:N.E) :
 run (Event:=Event) toE state (NEI_LineFull.aspis_core.field.wide_exact.WideExact.mul x y) =
 run (Event:=Event) id state (AspisR1CurrentWide.field.wide_exact.WideExact.mul (toE x) (toE y)) := by
 exact mapped toE state _ _ (NEI_FieldWide.wide_mul x y)
#print axioms wide_mul
theorem wide_mul_m31 {S Event:Type} (state:S) (x:N.E) (y:U32) :
 run (Event:=Event) toE state (NEI_LineFull.aspis_core.field.wide_exact.WideExact.mul_m31 x y) =
 run (Event:=Event) id state (AspisR1CurrentWide.field.wide_exact.WideExact.mul_m31 (toE x) y) := by
 exact mapped toE state _ _ (NEI_FieldWide.wide_mul_m31 x y)
#print axioms wide_mul_m31
#print axioms mapped
#print axioms widen
end NEI_FieldFrames
end
