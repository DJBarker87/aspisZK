import PV_STX2_SliceSyntax
set_option autoImplicit false
namespace PV_STX2_SliceF5
open PV_STX2_Syntax PV_STX2_SliceSyntax
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node0 : Node :=
  .leaf (.storage ⟨5, 114, .array [(.atom "body"), (.atom "statements"), (.number 0)]⟩ true 0)
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node1 : Node :=
  .leaf (.storage ⟨5, 115, .array [(.atom "body"), (.atom "statements"), (.number 1)]⟩ true 3)
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node2 : Node :=
  .leaf (.bind ⟨5, 116, .array [(.atom "body"), (.atom "statements"), (.number 2)]⟩ (.local 3) (.reference (.local 1) (.constant (.object [("kind", (.object [("Adt", (.array [(.null), (.array [])]))])), ("ty", (.object [("Deduplicated", (.number 946))]))]))))
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node3 : Node :=
  .leaf (.call ⟨5, 126, .array [(.atom "body"), (.atom "statements"), (.number 3)]⟩ (.object [("Regular", (.object [("kind", (.object [("Trait", (.array [(.object [("HashConsedValue", (.array [(.number 1670), (.object [("kind", (.object [("TraitImpl", (.object [("id", (.number 6)), ("generics", (.object [("regions", (.array [])), ("types", (.array [])), ("const_generics", (.array [])), ("trait_refs", (.array []))]))]))])), ("trait_decl_ref", (.object [("regions", (.array [])), ("skip_binder", (.object [("id", (.number 4)), ("generics", (.object [("regions", (.array [])), ("types", (.array [(.object [("Deduplicated", (.number 1120))]), (.object [("Deduplicated", (.number 1259))])])), ("const_generics", (.array [])), ("trait_refs", (.array []))]))]))]))])]))]), (.number 0)]))])), ("generics", (.object [("regions", (.array [(.object [("Body", (.number 2))])])), ("types", (.array [])), ("const_generics", (.array [])), ("trait_refs", (.array []))]))]))]) [(.move (.local 3)), (.move (.local 2))] (.local 0) [.drop ⟨5, 121, .array [(.atom "body"), (.atom "statements"), (.number 3), (.atom "kind"), (.atom "Call"), (.atom "on_unwind"), (.atom "statements"), (.number 0)]⟩ (.local 1) (.object [("kind", (.object [("Fun", (.object [("Regular", (.number 19))]))])), ("generics", (.object [("regions", (.array [(.object [("Body", (.number 3))])])), ("types", (.array [])), ("const_generics", (.array [])), ("trait_refs", (.array []))]))]) false [.storage ⟨5, 117, .array [(.atom "body"), (.atom "statements"), (.number 3), (.atom "kind"), (.atom "Call"), (.atom "on_unwind"), (.atom "statements"), (.number 0), (.atom "kind"), (.atom "Drop"), (.atom "on_unwind"), (.atom "statements"), (.number 0)]⟩ false 3,
.storage ⟨5, 118, .array [(.atom "body"), (.atom "statements"), (.number 3), (.atom "kind"), (.atom "Call"), (.atom "on_unwind"), (.atom "statements"), (.number 0), (.atom "kind"), (.atom "Drop"), (.atom "on_unwind"), (.atom "statements"), (.number 1)]⟩ false 2,
.storage ⟨5, 119, .array [(.atom "body"), (.atom "statements"), (.number 3), (.atom "kind"), (.atom "Call"), (.atom "on_unwind"), (.atom "statements"), (.number 0), (.atom "kind"), (.atom "Drop"), (.atom "on_unwind"), (.atom "statements"), (.number 2)]⟩ false 1,
.abort ⟨5, 120, .array [(.atom "body"), (.atom "statements"), (.number 3), (.atom "kind"), (.atom "Call"), (.atom "on_unwind"), (.atom "statements"), (.number 0), (.atom "kind"), (.atom "Drop"), (.atom "on_unwind"), (.atom "statements"), (.number 3)]⟩ (.atom "UnwindTerminate")],
.storage ⟨5, 122, .array [(.atom "body"), (.atom "statements"), (.number 3), (.atom "kind"), (.atom "Call"), (.atom "on_unwind"), (.atom "statements"), (.number 1)]⟩ false 3,
.storage ⟨5, 123, .array [(.atom "body"), (.atom "statements"), (.number 3), (.atom "kind"), (.atom "Call"), (.atom "on_unwind"), (.atom "statements"), (.number 2)]⟩ false 2,
.storage ⟨5, 124, .array [(.atom "body"), (.atom "statements"), (.number 3), (.atom "kind"), (.atom "Call"), (.atom "on_unwind"), (.atom "statements"), (.number 3)]⟩ false 1,
.unwind ⟨5, 125, .array [(.atom "body"), (.atom "statements"), (.number 3), (.atom "kind"), (.atom "Call"), (.atom "on_unwind"), (.atom "statements"), (.number 4)]⟩])
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node4 : Node :=
  .leaf (.drop ⟨5, 131, .array [(.atom "body"), (.atom "statements"), (.number 4)]⟩ (.local 1) (.object [("kind", (.object [("Fun", (.object [("Regular", (.number 19))]))])), ("generics", (.object [("regions", (.array [(.object [("Body", (.number 4))])])), ("types", (.array [])), ("const_generics", (.array [])), ("trait_refs", (.array []))]))]) false [.storage ⟨5, 127, .array [(.atom "body"), (.atom "statements"), (.number 4), (.atom "kind"), (.atom "Drop"), (.atom "on_unwind"), (.atom "statements"), (.number 0)]⟩ false 3,
.storage ⟨5, 128, .array [(.atom "body"), (.atom "statements"), (.number 4), (.atom "kind"), (.atom "Drop"), (.atom "on_unwind"), (.atom "statements"), (.number 1)]⟩ false 2,
.storage ⟨5, 129, .array [(.atom "body"), (.atom "statements"), (.number 4), (.atom "kind"), (.atom "Drop"), (.atom "on_unwind"), (.atom "statements"), (.number 2)]⟩ false 1,
.unwind ⟨5, 130, .array [(.atom "body"), (.atom "statements"), (.number 4), (.atom "kind"), (.atom "Drop"), (.atom "on_unwind"), (.atom "statements"), (.number 3)]⟩])
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node5 : Node :=
  .leaf (.storage ⟨5, 132, .array [(.atom "body"), (.atom "statements"), (.number 5)]⟩ false 3)
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node6 : Node :=
  .leaf (.storage ⟨5, 133, .array [(.atom "body"), (.atom "statements"), (.number 6)]⟩ false 2)
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node7 : Node :=
  .leaf (.storage ⟨5, 134, .array [(.atom "body"), (.atom "statements"), (.number 7)]⟩ false 1)
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node8 : Node :=
  .leaf (.ret ⟨5, 135, .array [(.atom "body"), (.atom "statements"), (.number 8)]⟩ (.local 0))
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def block9 : List Node :=
  [node0, node1, node2, node3, node4, node5, node6, node7, node8]
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def program : PV_STX2_SliceSyntax.Program :=
  ⟨5, .object [("opcode", (.atom "CallEntry")), ("function", (.number 5)), ("signature", (.object [("is_unsafe", (.boolean false)), ("abi", (.atom "Rust")), ("is_variadic", (.boolean false)), ("inputs", (.array [(.object [("Deduplicated", (.number 1120))]), (.object [("HashConsedValue", (.array [(.number 1259), (.object [("Adt", (.object [("id", (.atom "Tuple")), ("generics", (.object [("regions", (.array [])), ("types", (.array [(.object [("Deduplicated", (.number 940))])])), ("const_generics", (.array [])), ("trait_refs", (.array []))]))]))])]))])])), ("output", (.object [("Deduplicated", (.number 939))]))])), ("argument_count", (.number 2))], .array [(.object [("opcode", (.atom "LocalDeclaration")), ("function", (.number 5)), ("local", (.number 0)), ("role", (.atom "return")), ("declaration", (.object [("index", (.number 0)), ("name", (.null)), ("span", (.object [("data", (.object [("file_id", (.number 15)), ("beg", (.object [("line", (.number 250)), ("col", (.number 4))])), ("end", (.object [("line", (.number 250)), ("col", (.number 70))]))])), ("generated_from_span", (.null))])), ("ty", (.object [("Deduplicated", (.number 939))]))]))]), (.object [("opcode", (.atom "LocalDeclaration")), ("function", (.number 5)), ("local", (.number 1)), ("role", (.atom "argument")), ("declaration", (.object [("index", (.number 1)), ("name", (.null)), ("span", (.object [("data", (.object [("file_id", (.number 15)), ("beg", (.object [("line", (.number 250)), ("col", (.number 4))])), ("end", (.object [("line", (.number 250)), ("col", (.number 70))]))])), ("generated_from_span", (.null))])), ("ty", (.object [("Deduplicated", (.number 1120))]))]))]), (.object [("opcode", (.atom "LocalDeclaration")), ("function", (.number 5)), ("local", (.number 2)), ("role", (.atom "argument")), ("declaration", (.object [("index", (.number 2)), ("name", (.null)), ("span", (.object [("data", (.object [("file_id", (.number 15)), ("beg", (.object [("line", (.number 250)), ("col", (.number 4))])), ("end", (.object [("line", (.number 250)), ("col", (.number 70))]))])), ("generated_from_span", (.null))])), ("ty", (.object [("Deduplicated", (.number 1259))]))]))]), (.object [("opcode", (.atom "LocalDeclaration")), ("function", (.number 5)), ("local", (.number 3)), ("role", (.atom "temporary")), ("declaration", (.object [("index", (.number 3)), ("name", (.null)), ("span", (.object [("data", (.object [("file_id", (.number 15)), ("beg", (.object [("line", (.number 250)), ("col", (.number 4))])), ("end", (.object [("line", (.number 250)), ("col", (.number 70))]))])), ("generated_from_span", (.null))])), ("ty", (.object [("HashConsedValue", (.array [(.number 1665), (.object [("Ref", (.array [(.object [("Body", (.number 1))]), (.object [("Deduplicated", (.number 1120))]), (.atom "Mut")]))])]))]))]))])], block9⟩
#print axioms program
end PV_STX2_SliceF5
