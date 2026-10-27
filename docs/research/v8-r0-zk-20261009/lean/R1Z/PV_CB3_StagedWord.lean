import R1Z.PV_CB3_StagedTotal
import R1Z.PV_CB3_SamplerWordSource
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB3_StagedWord
open Aeneas Aeneas.Std Result
/-- Reuse the checked scalar source step at the newly extracted staged site. -/
theorem word_eq (w : U32) (r : U64) :
    PV_CB3_StagedSource.staged_reference.word_step w r =
      PV_CB3_ShippedOp249word.reference_split.word_step w r := by
  simp only [PV_CB3_StagedSource.staged_reference.word_step,
    PV_CB3_StagedSource.aspis_core.field.P, PV_CB3_StagedFields.aspis_core.field.P,
    PV_CB3_ShippedOp249word.reference_split.word_step,
    PV_CB3_ShippedOp249word.aspis_core.field.P, lift, bind_tc_ok]

theorem word_total (w : U32) (r : U64) :
    ∃ q r', PV_CB3_StagedSource.staged_reference.word_step w r = ok (q,r') := by
  rw [word_eq]
  exact PV_CB3_SamplerWordSource.word_total w r

def sum (d a : U32) : U64 :=
  U64.wrapping_add (core.convert.num.FromU64U32.from d) (core.convert.num.FromU64U32.from a)

theorem carry_total (d a : U32) :
    ∃ d' a', PV_CB3_StagedSource.staged_reference.carry_step d a = ok (d',a') := by
  obtain ⟨q,hq,_⟩ := UScalar.div_spec (sum d a) PV_CB3_SamplerWordSource.denominator_nonzero
  obtain ⟨r,hr,_⟩ := WP.spec_imp_exists
    (UScalar.rem_spec (sum d a) PV_CB3_SamplerWordSource.denominator_nonzero)
  refine ⟨UScalar.cast .U32 r,UScalar.cast .U32 q,?_⟩
  simp only [PV_CB3_StagedSource.staged_reference.carry_step,
    PV_CB3_StagedSource.aspis_core.field.P, PV_CB3_StagedFields.aspis_core.field.P,
    lift,bind_tc_ok]
  simp only [PV_CB3_SamplerWordSource.denominator,
    PV_CB3_ShippedOp249word.aspis_core.field.P] at hq hr
  change (do let r ← sum d a % core.convert.num.FromU64U32.from 2147483647#u32
             let q ← sum d a / core.convert.num.FromU64U32.from 2147483647#u32
             ok (UScalar.cast .U32 r,UScalar.cast .U32 q)) = _
  rw [hr]
  simp only [bind_tc_ok,hq]
#print axioms word_eq
#print axioms word_total
#print axioms carry_total
end R1Z.PV_CB3_StagedWord
