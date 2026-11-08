import PV_STX2_SliceSyntax
set_option autoImplicit false
namespace PV_STX2_SliceF1
open PV_STX2_Syntax PV_STX2_SliceSyntax
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node0 : Node :=
  .leaf (.storage ⟨1, 18, .array [(.atom "body"), (.atom "statements"), (.number 0)]⟩ true 0)
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node1 : Node :=
  .leaf (.call ⟨1, 21, .array [(.atom "body"), (.atom "statements"), (.number 1)]⟩ (.object [("Regular", (.object [("kind", (.object [("Fun", (.object [("Regular", (.number 2))]))])), ("generics", (.object [("regions", (.array [(.object [("Body", (.number 3))])])), ("types", (.array [])), ("const_generics", (.array [])), ("trait_refs", (.array []))]))]))]) [(.move (.local 1))] (.local 0) [.storage ⟨1, 19, .array [(.atom "body"), (.atom "statements"), (.number 1), (.atom "kind"), (.atom "Call"), (.atom "on_unwind"), (.atom "statements"), (.number 0)]⟩ false 1,
.unwind ⟨1, 20, .array [(.atom "body"), (.atom "statements"), (.number 1), (.atom "kind"), (.atom "Call"), (.atom "on_unwind"), (.atom "statements"), (.number 1)]⟩])
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node2 : Node :=
  .leaf (.storage ⟨1, 22, .array [(.atom "body"), (.atom "statements"), (.number 2)]⟩ false 1)
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node3 : Node :=
  .leaf (.ret ⟨1, 23, .array [(.atom "body"), (.atom "statements"), (.number 3)]⟩ (.local 0))
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def block4 : List Node :=
  [node0, node1, node2, node3]
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def program : PV_STX2_SliceSyntax.Program :=
  ⟨1, .object [("opcode", (.atom "CallEntry")), ("function", (.number 1)), ("signature", (.object [("is_unsafe", (.boolean false)), ("abi", (.atom "Rust")), ("is_variadic", (.boolean false)), ("inputs", (.array [(.object [("HashConsedValue", (.array [(.number 3361), (.object [("Ref", (.array [(.object [("Var", (.object [("Free", (.number 0))]))]), (.object [("Deduplicated", (.number 941))]), (.atom "Shared")]))])]))])])), ("output", (.object [("Deduplicated", (.number 941))]))])), ("argument_count", (.number 1))], .array [(.object [("opcode", (.atom "LocalDeclaration")), ("function", (.number 1)), ("local", (.number 0)), ("role", (.atom "return")), ("declaration", (.object [("index", (.number 0)), ("name", (.null)), ("span", (.object [("data", (.object [("file_id", (.number 9)), ("beg", (.object [("line", (.number 449)), ("col", (.number 23))])), ("end", (.object [("line", (.number 449)), ("col", (.number 27))]))])), ("generated_from_span", (.null))])), ("ty", (.object [("Deduplicated", (.number 941))]))]))]), (.object [("opcode", (.atom "LocalDeclaration")), ("function", (.number 1)), ("local", (.number 1)), ("role", (.atom "argument")), ("declaration", (.object [("index", (.number 1)), ("name", (.atom "self")), ("span", (.object [("data", (.object [("file_id", (.number 9)), ("beg", (.object [("line", (.number 449)), ("col", (.number 13))])), ("end", (.object [("line", (.number 449)), ("col", (.number 18))]))])), ("generated_from_span", (.null))])), ("ty", (.object [("HashConsedValue", (.array [(.number 1035), (.object [("Ref", (.array [(.object [("Body", (.number 1))]), (.object [("Deduplicated", (.number 941))]), (.atom "Shared")]))])]))]))]))])], block4⟩
#print axioms program
end PV_STX2_SliceF1
