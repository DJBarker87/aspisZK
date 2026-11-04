import NFQ_FieldLaws
set_option autoImplicit false
namespace NFQ_FieldDomains
open Aeneas Aeneas.Std Result
abbrev C := AspisS1M31Embedding.aspis_core.field.CM31
abbrev Q := AspisS1M31Embedding.aspis_core.field.QM31

def canonicalC (x : C) : Prop := x.a.val<2147483647 ∧ x.b.val<2147483647
def canonicalQ (x : Q) : Prop := canonicalC x.c0 ∧ canonicalC x.c1

theorem cm_domain (x : U32) (h : x.val<2147483647) :
 ∃ z : C, AspisS1M31Embedding.aspis_core.field.CM31.from_m31 x=ok z ∧ canonicalC z := by
 refine ⟨⟨x,0#u32⟩,NFQ_FieldLaws.cm_reference x,h,?_⟩
 change (0#u32).val<2147483647
 decide

theorem qm_domain (x : C) (h : canonicalC x) :
 ∃ z : Q, AspisS1M31Embedding.aspis_core.field.QM31.from_cm31 x=ok z ∧ canonicalQ z := by
 refine ⟨⟨x,⟨0#u32,0#u32⟩⟩,NFQ_FieldLaws.qm_reference x,h,?_⟩
 constructor <;> change (0#u32).val<2147483647
 decide
#print axioms cm_domain
#print axioms qm_domain
end NFQ_FieldDomains
