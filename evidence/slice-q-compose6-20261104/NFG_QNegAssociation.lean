import NFG_CheckedFieldRef.Funs
import AspisR72Sampler.Funs
set_option autoImplicit false
namespace NFG_QNegAssociation
open Aeneas Aeneas.Std Result
abbrev C := NFG_CheckedFieldRef.field.CM31
abbrev Q := NFG_CheckedFieldRef.field.QM31
def cm (x : C) : AspisR72Sampler.field.CM31 := ⟨x.a,x.b⟩
def qm (x : Q) : AspisR72Sampler.field.QM31 := ⟨cm x.c0,cm x.c1⟩
theorem word (x : U32) : NFG_CheckedFieldRef.field.M31.neg x = AspisR72Sampler.field.M31.neg x := by
 simp only [NFG_CheckedFieldRef.field.M31.neg,NFG_CheckedFieldRef.field.P,
  AspisR72Sampler.field.M31.neg,AspisR72Sampler.field.P]
/-- Full checked Result composition on the SAME four limbs. This is a call
expression, not a newly invented cohort QM31.neg root: R72 has no such symbol. -/
theorem result (x : Q) :
 (do let out ← NFG_CheckedFieldRef.field.QM31.neg x; ok (qm out)) =
 (do let a ← AspisR72Sampler.field.CM31.neg (cm x.c0)
     let b ← AspisR72Sampler.field.CM31.neg (cm x.c1)
     ok (AspisR72Sampler.field.QM31.mk a b)) := by
 simp only [NFG_CheckedFieldRef.field.QM31.neg,NFG_CheckedFieldRef.field.CM31.neg,
  AspisR72Sampler.field.CM31.neg,qm,cm,word,bind_assoc_eq,bind_tc_ok]
#print axioms word
#print axioms result
end NFG_QNegAssociation
