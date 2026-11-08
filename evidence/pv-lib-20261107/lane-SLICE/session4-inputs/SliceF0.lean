import PV_STX2_SliceSyntax
set_option autoImplicit false
namespace PV_STX2_SliceF0
open PV_STX2_Syntax PV_STX2_SliceSyntax
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node0 : Node :=
  .leaf (.storage ⟨0, 0, .array [(.atom "body"), (.atom "statements"), (.number 0)]⟩ true 0)
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node1 : Node :=
  .leaf (.storage ⟨0, 1, .array [(.atom "body"), (.atom "statements"), (.number 1)]⟩ true 2)
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node2 : Node :=
  .leaf (.storage ⟨0, 2, .array [(.atom "body"), (.atom "statements"), (.number 2)]⟩ true 3)
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node3 : Node :=
  .leaf (.storage ⟨0, 3, .array [(.atom "body"), (.atom "statements"), (.number 3)]⟩ true 4)
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node4 : Node :=
  .leaf (.bind ⟨0, 4, .array [(.atom "body"), (.atom "statements"), (.number 4)]⟩ (.local 4) (.reference (.project (.project (.local 1) (.deref)) (.field 0)) (.constant (.object [("kind", (.object [("Adt", (.array [(.null), (.array [])]))])), ("ty", (.object [("Deduplicated", (.number 946))]))]))))
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node5 : Node :=
  .leaf (.bind ⟨0, 5, .array [(.atom "body"), (.atom "statements"), (.number 5)]⟩ (.local 3) (.reference (.project (.local 4) (.deref)) (.constant (.object [("kind", (.object [("Adt", (.array [(.null), (.array [])]))])), ("ty", (.object [("Deduplicated", (.number 946))]))]))))
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node6 : Node :=
  .leaf (.call ⟨0, 8, .array [(.atom "body"), (.atom "statements"), (.number 6)]⟩ (.object [("Regular", (.object [("kind", (.object [("Fun", (.object [("Regular", (.number 1))]))])), ("generics", (.object [("regions", (.array [(.object [("Body", (.number 6))])])), ("types", (.array [])), ("const_generics", (.array [])), ("trait_refs", (.array []))]))]))]) [(.move (.local 3))] (.local 2) [.storage ⟨0, 6, .array [(.atom "body"), (.atom "statements"), (.number 6), (.atom "kind"), (.atom "Call"), (.atom "on_unwind"), (.atom "statements"), (.number 0)]⟩ false 1,
.unwind ⟨0, 7, .array [(.atom "body"), (.atom "statements"), (.number 6), (.atom "kind"), (.atom "Call"), (.atom "on_unwind"), (.atom "statements"), (.number 1)]⟩])
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node7 : Node :=
  .leaf (.storage ⟨0, 9, .array [(.atom "body"), (.atom "statements"), (.number 7)]⟩ false 3)
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node8 : Node :=
  .leaf (.aggregateMove ⟨0, 10, .array [(.atom "body"), (.atom "statements"), (.number 8)]⟩ (.local 0) (.object [("Adt", (.array [(.object [("id", (.object [("Adt", (.number 0))])), ("generics", (.object [("regions", (.array [])), ("types", (.array [])), ("const_generics", (.array [])), ("trait_refs", (.array []))]))]), (.null), (.null)]))]) [(.move (.local 2))])
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node9 : Node :=
  .leaf (.drop ⟨0, 13, .array [(.atom "body"), (.atom "statements"), (.number 9)]⟩ (.local 2) (.object [("kind", (.object [("Fun", (.object [("Regular", (.number 3))]))])), ("generics", (.object [("regions", (.array [(.object [("Body", (.number 7))])])), ("types", (.array [])), ("const_generics", (.array [])), ("trait_refs", (.array []))]))]) true [.storage ⟨0, 11, .array [(.atom "body"), (.atom "statements"), (.number 9), (.atom "kind"), (.atom "Drop"), (.atom "on_unwind"), (.atom "statements"), (.number 0)]⟩ false 1,
.unwind ⟨0, 12, .array [(.atom "body"), (.atom "statements"), (.number 9), (.atom "kind"), (.atom "Drop"), (.atom "on_unwind"), (.atom "statements"), (.number 1)]⟩])
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node10 : Node :=
  .leaf (.storage ⟨0, 14, .array [(.atom "body"), (.atom "statements"), (.number 10)]⟩ false 4)
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node11 : Node :=
  .leaf (.storage ⟨0, 15, .array [(.atom "body"), (.atom "statements"), (.number 11)]⟩ false 2)
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node12 : Node :=
  .leaf (.storage ⟨0, 16, .array [(.atom "body"), (.atom "statements"), (.number 12)]⟩ false 1)
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node13 : Node :=
  .leaf (.ret ⟨0, 17, .array [(.atom "body"), (.atom "statements"), (.number 13)]⟩ (.local 0))
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def block14 : List Node :=
  [node0, node1, node2, node3, node4, node5, node6, node7, node8, node9, node10, node11, node12, node13]
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def program : PV_STX2_SliceSyntax.Program :=
  ⟨0, .object [("opcode", (.atom "CallEntry")), ("function", (.number 0)), ("signature", (.object [("is_unsafe", (.boolean false)), ("abi", (.atom "Rust")), ("is_variadic", (.boolean false)), ("inputs", (.array [(.object [("HashConsedValue", (.array [(.number 3360), (.object [("Ref", (.array [(.object [("Var", (.object [("Free", (.number 0))]))]), (.object [("HashConsedValue", (.array [(.number 799), (.object [("Adt", (.object [("id", (.object [("Adt", (.number 0))])), ("generics", (.object [("regions", (.array [])), ("types", (.array [])), ("const_generics", (.array [])), ("trait_refs", (.array []))]))]))])]))]), (.atom "Shared")]))])]))])])), ("output", (.object [("Deduplicated", (.number 799))]))])), ("argument_count", (.number 1))], .array [(.object [("opcode", (.atom "LocalDeclaration")), ("function", (.number 0)), ("local", (.number 0)), ("role", (.atom "return")), ("declaration", (.object [("index", (.number 0)), ("name", (.null)), ("span", (.object [("data", (.object [("file_id", (.number 0)), ("beg", (.object [("line", (.number 74)), ("col", (.number 9))])), ("end", (.object [("line", (.number 74)), ("col", (.number 14))]))])), ("generated_from_span", (.null))])), ("ty", (.object [("Deduplicated", (.number 799))]))]))]), (.object [("opcode", (.atom "LocalDeclaration")), ("function", (.number 0)), ("local", (.number 1)), ("role", (.atom "argument")), ("declaration", (.object [("index", (.number 1)), ("name", (.atom "self")), ("span", (.object [("data", (.object [("file_id", (.number 0)), ("beg", (.object [("line", (.number 74)), ("col", (.number 9))])), ("end", (.object [("line", (.number 74)), ("col", (.number 14))]))])), ("generated_from_span", (.null))])), ("ty", (.object [("HashConsedValue", (.array [(.number 804), (.object [("Ref", (.array [(.object [("Body", (.number 1))]), (.object [("Deduplicated", (.number 799))]), (.atom "Shared")]))])]))]))]))]), (.object [("opcode", (.atom "LocalDeclaration")), ("function", (.number 0)), ("local", (.number 2)), ("role", (.atom "temporary")), ("declaration", (.object [("index", (.number 2)), ("name", (.null)), ("span", (.object [("data", (.object [("file_id", (.number 0)), ("beg", (.object [("line", (.number 79)), ("col", (.number 4))])), ("end", (.object [("line", (.number 79)), ("col", (.number 45))]))])), ("generated_from_span", (.null))])), ("ty", (.object [("Deduplicated", (.number 941))]))]))]), (.object [("opcode", (.atom "LocalDeclaration")), ("function", (.number 0)), ("local", (.number 3)), ("role", (.atom "temporary")), ("declaration", (.object [("index", (.number 3)), ("name", (.null)), ("span", (.object [("data", (.object [("file_id", (.number 0)), ("beg", (.object [("line", (.number 79)), ("col", (.number 4))])), ("end", (.object [("line", (.number 79)), ("col", (.number 45))]))])), ("generated_from_span", (.null))])), ("ty", (.object [("HashConsedValue", (.array [(.number 944), (.object [("Ref", (.array [(.object [("Body", (.number 3))]), (.object [("Deduplicated", (.number 941))]), (.atom "Shared")]))])]))]))]))]), (.object [("opcode", (.atom "LocalDeclaration")), ("function", (.number 0)), ("local", (.number 4)), ("role", (.atom "temporary")), ("declaration", (.object [("index", (.number 4)), ("name", (.null)), ("span", (.object [("data", (.object [("file_id", (.number 0)), ("beg", (.object [("line", (.number 79)), ("col", (.number 4))])), ("end", (.object [("line", (.number 79)), ("col", (.number 45))]))])), ("generated_from_span", (.null))])), ("ty", (.object [("HashConsedValue", (.array [(.number 945), (.object [("Ref", (.array [(.object [("Body", (.number 4))]), (.object [("Deduplicated", (.number 941))]), (.atom "Shared")]))])]))]))]))])], block14⟩
#print axioms program
end PV_STX2_SliceF0
