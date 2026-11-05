import NIT_FieldInterpretation
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIW_AlignFieldReply
open Aeneas Aeneas.Std Result LPi_FieldValues NIT_Cuts NIT_FieldInterpretation

def Produced {A : Type} (call : Result A) (spec : A → Prop) : Prop :=
 match call with | ok value => spec value | fail _ => False | div => False

/-- The actual emitted field reply discharges the arithmetic clause. A parent
needs no opaque-reply law hypothesis after observing this complete call. -/
theorem qm (a b : K) (ha : canonQ a) (hb : canonQ b) :
 Produced (FIo_Native.aspis_core.field.QM31.mul a b)
  (fun value=>QMul a b value ∧ canonQ value) := by
 obtain ⟨value,call,canonical,spec⟩ := LPi_TowerValues.qm_mul a b ha hb
 rw [call]
 exact ⟨spec,canonical⟩

theorem em (a b : E) (ha : canonE a) (hb : canonE b) :
 Produced (FIo_Native.aspis_core.field.wide_exact.WideExact.mul a b)
  (fun value=>EMul a b value ∧ canonE value) := by
 obtain ⟨value,call,canonical,spec⟩ := LPi_TowerValues.wide_mul a b ha hb
 rw [call]
 exact ⟨spec,canonical⟩

theorem ea (a b : E) (ha : canonE a) (hb : canonE b) :
 Produced (FIo_Native.aspis_core.field.wide_exact.WideExact.add a b)
  (fun value=>EAdd a b value ∧ canonE value) := by
 obtain ⟨lo,hlo,clo,vlo⟩ := LPi_TowerValues.qm_add a.c0 b.c0 ha.1 hb.1
 obtain ⟨hi,hhi,chi,vhi⟩ := LPi_TowerValues.qm_add a.c1 b.c1 ha.2 hb.2
 have call : FIo_Native.aspis_core.field.wide_exact.WideExact.add a b=ok ⟨lo,hi⟩ := by
  simp only [FIo_Native.aspis_core.field.wide_exact.WideExact.add,hlo,hhi,bind_tc_ok]
 rw [call]
 exact ⟨Prod.ext vlo vhi,clo,chi⟩

#print axioms qm
#print axioms em
#print axioms ea
end AspisR1.NIW_AlignFieldReply
