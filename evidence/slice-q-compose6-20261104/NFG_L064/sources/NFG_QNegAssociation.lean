import NFG_InverseRef.Funs
import AspisR72Sampler.Funs
set_option autoImplicit false
namespace NFG_QNegAssociation
open Aeneas Aeneas.Std Result
abbrev F := NFG_InverseRef.field.CM31
abbrev Q := NFG_InverseRef.field.QM31
def cm (x : F) : AspisR72Sampler.field.CM31 := ⟨x.a,x.b⟩
def qm (x : Q) : AspisR72Sampler.field.QM31 := ⟨cm x.c0,cm x.c1⟩
theorem word (x : U32) : NFG_InverseRef.field.M31.neg x = AspisR72Sampler.field.M31.neg x := rfl
/-- Full partial Result; native canonical input is narrower only at the root. -/
theorem result (x : Q) :
 (do let out ← NFG_InverseRef.field.QM31.neg x; ok (qm out)) = AspisR72Sampler.field.QM31.neg (qm x) := by
 simp only [NFG_InverseRef.field.QM31.neg,NFG_InverseRef.field.CM31.neg,
  AspisR72Sampler.field.QM31.neg,AspisR72Sampler.field.CM31.neg,qm,cm,word,bind_assoc_eq,bind_tc_ok]
#print axioms word
#print axioms result
end NFG_QNegAssociation
