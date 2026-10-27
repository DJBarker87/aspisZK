import RPz8_F3T_Semantic
set_option autoImplicit false
namespace AspisR1.F3T_PublicExt

theorem public_ext (a b : LiteralTranscript.Public)
    (bytes : a.pubBytes=b.pubBytes) (tag : a.tag=b.tag) : a=b := by
  cases a
  cases b
  simp_all

theorem semantic_ext (a b : F3_Model.SemanticPublic)
    (bytes : a.value.pubBytes=b.value.pubBytes) (tag : a.value.tag=b.value.tag) : a=b := by
  cases a with
  | mk a=>cases b with
    | mk b=>exact congrArg F3_Model.SemanticPublic.mk (public_ext a b bytes tag)

#print axioms public_ext
#print axioms semantic_ext
end AspisR1.F3T_PublicExt
