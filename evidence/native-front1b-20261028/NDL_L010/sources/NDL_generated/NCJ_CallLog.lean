import NBG_FieldDischarge
set_option autoImplicit false
noncomputable section
namespace NCJ_CallLog
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues
/-- An opaque reply is substituted only by the emitted definition's exact
successful value law, at the SAME operands and on its proved domain. -/
theorem qm_reply (x y reply : NQ) (hx : canonQ x) (hy : canonQ y)
    (logged : FIo_Native.aspis_core.field.QM31.mul x y = ok reply) :
    canonQ reply ∧ qw reply = mulQ (qw x) (qw y) := by
  obtain ⟨z,run,canonical,value⟩ := LPi_TowerValues.qm_mul x y hx hy
  have same := Result.ok.inj (run.symm.trans logged)
  subst reply
  exact ⟨canonical,value⟩

theorem wide_reply (x y reply : NE) (hx : canonE x) (hy : canonE y)
    (logged : FIo_Native.aspis_core.field.wide_exact.WideExact.mul x y = ok reply) :
    canonE reply ∧ ew reply = mulE (ew x) (ew y) := by
  obtain ⟨z,run,canonical,value⟩ := LPi_TowerValues.wide_mul x y hx hy
  have same := Result.ok.inj (run.symm.trans logged)
  subst reply
  exact ⟨canonical,value⟩

/-- Identical native calls may yield different opaque replies in Kani; actual
emitted multiplication is deterministic. This is needed by frozen double,
which calls x.mul(x) twice, while the constructor model shares the result. -/
theorem repeated_qm (x y a b : NQ)
    (ha : FIo_Native.aspis_core.field.QM31.mul x y = ok a)
    (hb : FIo_Native.aspis_core.field.QM31.mul x y = ok b) : a=b :=
  Result.ok.inj (ha.symm.trans hb)

/-- Exact closed constant for QUARTER*QUARTER. The multiplication theorem is
used; no concrete recurrence or native multiplication is evaluated. -/
theorem quarter_square :
    FIo_Native.aspis_core.field.M31.mul 536870912#u32 536870912#u32 = ok 134217728#u32 := by
  obtain ⟨z,run,value,_⟩ := LPf_BaseMultiply.source 536870912#u32 536870912#u32
  have hz : z=134217728#u32 := by
    apply UScalar.eq_of_val_eq
    simpa using value
  simpa only [hz] using run

#print axioms qm_reply
#print axioms wide_reply
#print axioms repeated_qm
#print axioms quarter_square
#print axioms LPi_TowerValues.qm_mul
#print axioms LPi_TowerValues.wide_mul
#print axioms NBG_FieldDischarge.wide_qm
#print axioms NBG_FieldDischarge.wide_scale
end NCJ_CallLog
