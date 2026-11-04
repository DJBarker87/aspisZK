import NFC_ScalarAdd
import NEV_DotCarrier
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFC_AddDomain
open Aeneas Aeneas.Std Result NEV_DotCarrier
theorem cm (left right : NC) (hl : canonC left) (hr : canonC right) :
    ∃ out,FIo_Native.aspis_core.field.CM31.add left right=ok out ∧ canonC out := by
  obtain ⟨a,ha,ca,_⟩:=NFC_ScalarAdd.total left.a right.a hl.1 hr.1
  obtain ⟨b,hb,cb,_⟩:=NFC_ScalarAdd.total left.b right.b hl.2 hr.2
  refine ⟨⟨a,b⟩,?_,ca,cb⟩
  simp only [FIo_Native.aspis_core.field.CM31.add,ha,hb,bind_tc_ok]

theorem qm (left right : NQ) (hl : canonQ left) (hr : canonQ right) :
    ∃ out,FIo_Native.aspis_core.field.QM31.add left right=ok out ∧ canonQ out := by
  obtain ⟨a,ha,ca⟩:=cm left.c0 right.c0 hl.1 hr.1
  obtain ⟨b,hb,cb⟩:=cm left.c1 right.c1 hl.2 hr.2
  refine ⟨⟨a,b⟩,?_,ca,cb⟩
  simp only [FIo_Native.aspis_core.field.QM31.add,ha,hb,bind_tc_ok]

/-- Actual final add returns a canonical value on exactly its operand domain. -/
theorem total (left right : NE) (hl : canonE left) (hr : canonE right) :
    ∃ out,FIo_Native.aspis_core.field.wide_exact.WideExact.add left right=ok out ∧ canonE out := by
  obtain ⟨a,ha,ca⟩:=qm left.c0 right.c0 hl.1 hr.1
  obtain ⟨b,hb,cb⟩:=qm left.c1 right.c1 hl.2 hr.2
  refine ⟨⟨a,b⟩,?_,ca,cb⟩
  simp only [FIo_Native.aspis_core.field.wide_exact.WideExact.add,ha,hb,bind_tc_ok]

theorem canonical (left right out : NE) (hl : canonE left) (hr : canonE right)
    (run : FIo_Native.aspis_core.field.wide_exact.WideExact.add left right=ok out) : canonE out := by
  obtain ⟨value,call,canonical⟩:=total left right hl hr
  have same : value=out := Result.ok.inj (call.symm.trans run)
  exact same ▸ canonical
#print axioms cm
#print axioms qm
#print axioms total
#print axioms canonical
end AspisR1.NFC_AddDomain
end
