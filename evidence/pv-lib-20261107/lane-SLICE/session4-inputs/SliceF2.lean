import PV_STX2_SliceSyntax
set_option autoImplicit false
namespace PV_STX2_SliceF2
open PV_STX2_Syntax PV_STX2_SliceSyntax
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node0 : Node :=
  .leaf (.storage ⟨2, 24, .array [(.atom "body"), (.atom "statements"), (.number 0)]⟩ true 0)
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node1 : Node :=
  .leaf (.storage ⟨2, 25, .array [(.atom "body"), (.atom "statements"), (.number 1)]⟩ true 2)
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node2 : Node :=
  .leaf (.storage ⟨2, 26, .array [(.atom "body"), (.atom "statements"), (.number 2)]⟩ true 3)
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node3 : Node :=
  .leaf (.call ⟨2, 27, .array [(.atom "body"), (.atom "statements"), (.number 3)]⟩ (.object [("Regular", (.object [("kind", (.object [("Fun", (.object [("Builtin", (.atom "ArrayToSliceShared"))]))])), ("generics", (.object [("regions", (.array [(.atom "Erased")])), ("types", (.array [(.object [("Deduplicated", (.number 939))])])), ("const_generics", (.array [(.object [("kind", (.object [("Literal", (.object [("Scalar", (.object [("Unsigned", (.array [(.atom "Usize"), (.atom "16")]))]))]))])), ("ty", (.object [("Deduplicated", (.number 940))]))])])), ("trait_refs", (.array []))]))]))]) [(.copy (.local 1))] (.local 3) [.abort ⟨2, 1105, .array [(.atom "body"), (.atom "statements"), (.number 3), (.atom "kind"), (.atom "Call"), (.atom "on_unwind"), (.atom "statements"), (.number 0)]⟩ (.atom "UndefinedBehavior")])
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node4 : Node :=
  .leaf (.storage ⟨2, 28, .array [(.atom "body"), (.atom "statements"), (.number 4)]⟩ true 5)
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node5 : Node :=
  .leaf (.bind ⟨2, 29, .array [(.atom "body"), (.atom "statements"), (.number 5)]⟩ (.local 5) (.rawPointer (.project (.local 3) (.deref)) (.copy (.project (.local 3) (.metadata)))))
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node6 : Node :=
  .leaf (.bind ⟨2, 30, .array [(.atom "body"), (.atom "statements"), (.number 6)]⟩ (.local 2) (.unary (.object [("Cast", (.object [("RawPtr", (.array [(.object [("Deduplicated", (.number 1122))]), (.object [("Deduplicated", (.number 1086))])]))]))]) (.copy (.local 5))))
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node7 : Node :=
  .leaf (.storage ⟨2, 31, .array [(.atom "body"), (.atom "statements"), (.number 7)]⟩ false 5)
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node8 : Node :=
  .leaf (.storage ⟨2, 32, .array [(.atom "body"), (.atom "statements"), (.number 8)]⟩ false 3)
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node9 : Node :=
  .leaf (.storage ⟨2, 33, .array [(.atom "body"), (.atom "statements"), (.number 9)]⟩ true 4)
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node10 : Node :=
  .leaf (.aggregateMove ⟨2, 34, .array [(.atom "body"), (.atom "statements"), (.number 10)]⟩ (.local 4) (.object [("Adt", (.array [(.object [("id", (.object [("Adt", (.number 5))])), ("generics", (.object [("regions", (.array [])), ("types", (.array [])), ("const_generics", (.array [])), ("trait_refs", (.array []))]))]), (.null), (.null)]))]) [(.copy (.local 2))])
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node11 : Node :=
  .leaf (.storage ⟨2, 35, .array [(.atom "body"), (.atom "statements"), (.number 11)]⟩ true 6)
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node12 : Node :=
  .leaf (.storage ⟨2, 36, .array [(.atom "body"), (.atom "statements"), (.number 12)]⟩ true 7)
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node13 : Node :=
  .leaf (.aggregateMove ⟨2, 37, .array [(.atom "body"), (.atom "statements"), (.number 13)]⟩ (.local 7) (.object [("Adt", (.array [(.object [("id", (.object [("Adt", (.number 7))])), ("generics", (.object [("regions", (.array [])), ("types", (.array [])), ("const_generics", (.array [])), ("trait_refs", (.array []))]))]), (.null), (.null)]))]) [(.copy (.local 4))])
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node14 : Node :=
  .leaf (.call ⟨2, 40, .array [(.atom "body"), (.atom "statements"), (.number 14)]⟩ (.object [("Regular", (.object [("kind", (.object [("Fun", (.object [("Regular", (.number 4))]))])), ("generics", (.object [("regions", (.array [])), ("types", (.array [])), ("const_generics", (.array [])), ("trait_refs", (.array []))]))]))]) [(.move (.local 7))] (.local 6) [.storage ⟨2, 38, .array [(.atom "body"), (.atom "statements"), (.number 14), (.atom "kind"), (.atom "Call"), (.atom "on_unwind"), (.atom "statements"), (.number 0)]⟩ false 1,
.unwind ⟨2, 39, .array [(.atom "body"), (.atom "statements"), (.number 14), (.atom "kind"), (.atom "Call"), (.atom "on_unwind"), (.atom "statements"), (.number 1)]⟩])
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node15 : Node :=
  .leaf (.storage ⟨2, 41, .array [(.atom "body"), (.atom "statements"), (.number 15)]⟩ false 7)
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node16 : Node :=
  .leaf (.bind ⟨2, 42, .array [(.atom "body"), (.atom "statements"), (.number 16)]⟩ (.local 0) (.use (.move (.project (.local 6) (.field 0)))))
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node17 : Node :=
  .leaf (.storage ⟨2, 43, .array [(.atom "body"), (.atom "statements"), (.number 17)]⟩ false 6)
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node18 : Node :=
  .leaf (.storage ⟨2, 44, .array [(.atom "body"), (.atom "statements"), (.number 18)]⟩ false 4)
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node19 : Node :=
  .leaf (.storage ⟨2, 45, .array [(.atom "body"), (.atom "statements"), (.number 19)]⟩ false 2)
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node20 : Node :=
  .leaf (.storage ⟨2, 46, .array [(.atom "body"), (.atom "statements"), (.number 20)]⟩ false 1)
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node21 : Node :=
  .leaf (.ret ⟨2, 47, .array [(.atom "body"), (.atom "statements"), (.number 21)]⟩ (.local 0))
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def block22 : List Node :=
  [node0, node1, node2, node3, node4, node5, node6, node7, node8, node9, node10, node11, node12, node13, node14, node15, node16, node17, node18, node19, node20, node21]
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def program : PV_STX2_SliceSyntax.Program :=
  ⟨2, .object [("opcode", (.atom "CallEntry")), ("function", (.number 2)), ("signature", (.object [("is_unsafe", (.boolean false)), ("abi", (.atom "Rust")), ("is_variadic", (.boolean false)), ("inputs", (.array [(.object [("Deduplicated", (.number 3361))])])), ("output", (.object [("Deduplicated", (.number 941))]))])), ("argument_count", (.number 1))], .array [(.object [("opcode", (.atom "LocalDeclaration")), ("function", (.number 2)), ("local", (.number 0)), ("role", (.atom "return")), ("declaration", (.object [("index", (.number 0)), ("name", (.null)), ("span", (.object [("data", (.object [("file_id", (.number 9)), ("beg", (.object [("line", (.number 469)), ("col", (.number 56))])), ("end", (.object [("line", (.number 469)), ("col", (.number 62))]))])), ("generated_from_span", (.null))])), ("ty", (.object [("Deduplicated", (.number 941))]))]))]), (.object [("opcode", (.atom "LocalDeclaration")), ("function", (.number 2)), ("local", (.number 1)), ("role", (.atom "argument")), ("declaration", (.object [("index", (.number 1)), ("name", (.atom "array")), ("span", (.object [("data", (.object [("file_id", (.number 9)), ("beg", (.object [("line", (.number 469)), ("col", (.number 37))])), ("end", (.object [("line", (.number 469)), ("col", (.number 42))]))])), ("generated_from_span", (.null))])), ("ty", (.object [("Deduplicated", (.number 1035))]))]))]), (.object [("opcode", (.atom "LocalDeclaration")), ("function", (.number 2)), ("local", (.number 2)), ("role", (.atom "temporary")), ("declaration", (.object [("index", (.number 2)), ("name", (.atom "ptr")), ("span", (.object [("data", (.object [("file_id", (.number 9)), ("beg", (.object [("line", (.number 470)), ("col", (.number 12))])), ("end", (.object [("line", (.number 470)), ("col", (.number 19))]))])), ("generated_from_span", (.null))])), ("ty", (.object [("Deduplicated", (.number 1086))]))]))]), (.object [("opcode", (.atom "LocalDeclaration")), ("function", (.number 2)), ("local", (.number 3)), ("role", (.atom "temporary")), ("declaration", (.object [("index", (.number 3)), ("name", (.atom "self")), ("span", (.object [("data", (.object [("file_id", (.number 9)), ("beg", (.object [("line", (.number 470)), ("col", (.number 32))])), ("end", (.object [("line", (.number 470)), ("col", (.number 37))]))])), ("generated_from_span", (.null))])), ("ty", (.object [("HashConsedValue", (.array [(.number 1093), (.object [("Ref", (.array [(.object [("Body", (.number 3))]), (.object [("Deduplicated", (.number 1091))]), (.atom "Shared")]))])]))]))]))]), (.object [("opcode", (.atom "LocalDeclaration")), ("function", (.number 2)), ("local", (.number 4)), ("role", (.atom "temporary")), ("declaration", (.object [("index", (.number 4)), ("name", (.atom "f")), ("span", (.object [("data", (.object [("file_id", (.number 9)), ("beg", (.object [("line", (.number 474)), ("col", (.number 16))])), ("end", (.object [("line", (.number 478)), ("col", (.number 9))]))])), ("generated_from_span", (.null))])), ("ty", (.object [("Deduplicated", (.number 1120))]))]))]), (.object [("opcode", (.atom "LocalDeclaration")), ("function", (.number 2)), ("local", (.number 5)), ("role", (.atom "temporary")), ("declaration", (.object [("index", (.number 5)), ("name", (.null)), ("span", (.object [("data", (.object [("file_id", (.number 12)), ("beg", (.object [("line", (.number 727)), ("col", (.number 8))])), ("end", (.object [("line", (.number 727)), ("col", (.number 26))]))])), ("generated_from_span", (.null))])), ("ty", (.object [("HashConsedValue", (.array [(.number 1122), (.object [("RawPtr", (.array [(.object [("Deduplicated", (.number 1091))]), (.atom "Shared")]))])]))]))]))]), (.object [("opcode", (.atom "LocalDeclaration")), ("function", (.number 2)), ("local", (.number 6)), ("role", (.atom "temporary")), ("declaration", (.object [("index", (.number 6)), ("name", (.null)), ("span", (.object [("data", (.object [("file_id", (.number 9)), ("beg", (.object [("line", (.number 114)), ("col", (.number 4))])), ("end", (.object [("line", (.number 114)), ("col", (.number 49))]))])), ("generated_from_span", (.null))])), ("ty", (.object [("HashConsedValue", (.array [(.number 1195), (.object [("Adt", (.object [("id", (.object [("Adt", (.number 6))])), ("generics", (.object [("regions", (.array [])), ("types", (.array [])), ("const_generics", (.array [])), ("trait_refs", (.array []))]))]))])]))]))]))]), (.object [("opcode", (.atom "LocalDeclaration")), ("function", (.number 2)), ("local", (.number 7)), ("role", (.atom "temporary")), ("declaration", (.object [("index", (.number 7)), ("name", (.null)), ("span", (.object [("data", (.object [("file_id", (.number 9)), ("beg", (.object [("line", (.number 114)), ("col", (.number 16))])), ("end", (.object [("line", (.number 114)), ("col", (.number 48))]))])), ("generated_from_span", (.null))])), ("ty", (.object [("Deduplicated", (.number 1225))]))]))])], block22⟩
#print axioms program
end PV_STX2_SliceF2
