import NFG_SmallRefs.Funs
import NFG_ResultCongr
import AspisR72Sampler.Funs
set_option autoImplicit false
namespace NFG_SmallAssociation
open Aeneas Aeneas.Std Result
abbrev CM := NFG_SmallRefs.aspis_core.field.CM31
abbrev QM := NFG_SmallRefs.aspis_core.field.QM31
def cm (x : CM) : AspisR72Sampler.field.CM31 := ⟨x.a,x.b⟩
def qm (x : QM) : AspisR72Sampler.field.QM31 := ⟨cm x.c0,cm x.c1⟩
/-- Full checked subtraction Result, including noncanonical failure. -/
theorem word (x : U32) : NFG_SmallRefs.NFG_neg_word_ref x = AspisR72Sampler.field.M31.neg x := by
 simp only [NFG_SmallRefs.NFG_neg_word_ref,NFG_SmallRefs.NFG_P,
  AspisR72Sampler.field.M31.neg,AspisR72Sampler.field.P]
 split_ifs
 · rfl
 · cases (2147483647#u32 - x) <;> rfl
/-- Reference extracted byte-for-byte from the Kani ensures reference. -/
theorem neg (x : CM) :
 (do let out ← NFG_SmallRefs.NFG_cm_ref x; ok (cm out)) = AspisR72Sampler.field.CM31.neg (cm x) := by
 simp only [NFG_SmallRefs.NFG_cm_ref,AspisR72Sampler.field.CM31.neg,cm,word,bind_assoc_eq,bind_tc_ok]
theorem zero (x : QM) : NFG_SmallRefs.NFG_qm_zero_ref x = AspisR72Sampler.field.QM31.is_zero (qm x) := by
 simp only [NFG_SmallRefs.NFG_qm_zero_ref,AspisR72Sampler.field.QM31.is_zero,
  AspisR72Sampler.field.CM31.is_zero,AspisR72Sampler.field.M31.is_zero,qm,cm,bind_tc_ok]
 split_ifs <;> simp_all
#print axioms word
#print axioms neg
#print axioms zero
end NFG_SmallAssociation
