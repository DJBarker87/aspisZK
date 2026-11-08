import PV_STX2_SliceSyntax
set_option autoImplicit false
namespace PV_STX2_SliceF8
open PV_STX2_Syntax PV_STX2_SliceSyntax
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node0 : Node :=
  .leaf (.storage ⟨8, 183, .array [(.atom "body"), (.atom "statements"), (.number 0)]⟩ true 0)
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node1 : Node :=
  .leaf (.storage ⟨8, 184, .array [(.atom "body"), (.atom "statements"), (.number 1)]⟩ true 3)
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node2 : Node :=
  .leaf (.bind ⟨8, 185, .array [(.atom "body"), (.atom "statements"), (.number 2)]⟩ (.local 3) (.use (.move (.project (.local 2) (.field 0)))))
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node3 : Node :=
  .leaf (.storage ⟨8, 186, .array [(.atom "body"), (.atom "statements"), (.number 3)]⟩ true 4)
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node4 : Node :=
  .leaf (.storage ⟨8, 187, .array [(.atom "body"), (.atom "statements"), (.number 4)]⟩ true 5)
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node5 : Node :=
  .leaf (.bind ⟨8, 188, .array [(.atom "body"), (.atom "statements"), (.number 5)]⟩ (.local 5) (.reference (.project (.project (.local 1) (.deref)) (.field 0)) (.constant (.object [("kind", (.object [("Adt", (.array [(.null), (.array [])]))])), ("ty", (.object [("Deduplicated", (.number 946))]))]))))
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node6 : Node :=
  .leaf (.storage ⟨8, 189, .array [(.atom "body"), (.atom "statements"), (.number 6)]⟩ true 6)
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node7 : Node :=
  .leaf (.aggregateMove ⟨8, 190, .array [(.atom "body"), (.atom "statements"), (.number 7)]⟩ (.local 6) (.object [("Adt", (.array [(.object [("id", (.atom "Tuple")), ("generics", (.object [("regions", (.array [])), ("types", (.array [])), ("const_generics", (.array [])), ("trait_refs", (.array []))]))]), (.null), (.null)]))]) [(.copy (.local 3))])
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node8 : Node :=
  .leaf (.call ⟨8, 195, .array [(.atom "body"), (.atom "statements"), (.number 8)]⟩ (.object [("Regular", (.object [("kind", (.object [("Trait", (.array [(.object [("Deduplicated", (.number 1670))]), (.number 0)]))])), ("generics", (.object [("regions", (.array [(.object [("Body", (.number 4))])])), ("types", (.array [])), ("const_generics", (.array [])), ("trait_refs", (.array []))]))]))]) [(.move (.local 5)), (.move (.local 6))] (.local 4) [.storage ⟨8, 191, .array [(.atom "body"), (.atom "statements"), (.number 8), (.atom "kind"), (.atom "Call"), (.atom "on_unwind"), (.atom "statements"), (.number 0)]⟩ false 3,
.storage ⟨8, 192, .array [(.atom "body"), (.atom "statements"), (.number 8), (.atom "kind"), (.atom "Call"), (.atom "on_unwind"), (.atom "statements"), (.number 1)]⟩ false 2,
.storage ⟨8, 193, .array [(.atom "body"), (.atom "statements"), (.number 8), (.atom "kind"), (.atom "Call"), (.atom "on_unwind"), (.atom "statements"), (.number 2)]⟩ false 1,
.unwind ⟨8, 194, .array [(.atom "body"), (.atom "statements"), (.number 8), (.atom "kind"), (.atom "Call"), (.atom "on_unwind"), (.atom "statements"), (.number 3)]⟩])
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node9 : Node :=
  .leaf (.storage ⟨8, 196, .array [(.atom "body"), (.atom "statements"), (.number 9)]⟩ false 6)
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node10 : Node :=
  .leaf (.storage ⟨8, 197, .array [(.atom "body"), (.atom "statements"), (.number 10)]⟩ false 5)
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node11 : Node :=
  .leaf (.aggregateMove ⟨8, 198, .array [(.atom "body"), (.atom "statements"), (.number 11)]⟩ (.local 0) (.object [("Adt", (.array [(.object [("id", (.object [("Adt", (.number 8))])), ("generics", (.object [("regions", (.array [])), ("types", (.array [])), ("const_generics", (.array [])), ("trait_refs", (.array []))]))]), (.null), (.null)]))]) [(.move (.local 4))])
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node12 : Node :=
  .leaf (.storage ⟨8, 199, .array [(.atom "body"), (.atom "statements"), (.number 12)]⟩ false 4)
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node13 : Node :=
  .leaf (.storage ⟨8, 200, .array [(.atom "body"), (.atom "statements"), (.number 13)]⟩ false 3)
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node14 : Node :=
  .leaf (.storage ⟨8, 201, .array [(.atom "body"), (.atom "statements"), (.number 14)]⟩ false 2)
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node15 : Node :=
  .leaf (.storage ⟨8, 202, .array [(.atom "body"), (.atom "statements"), (.number 15)]⟩ false 1)
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node16 : Node :=
  .leaf (.ret ⟨8, 203, .array [(.atom "body"), (.atom "statements"), (.number 16)]⟩ (.local 0))
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def block17 : List Node :=
  [node0, node1, node2, node3, node4, node5, node6, node7, node8, node9, node10, node11, node12, node13, node14, node15, node16]
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def program : PV_STX2_SliceSyntax.Program :=
  ⟨8, .object [("opcode", (.atom "CallEntry")), ("function", (.number 8)), ("signature", (.object [("is_unsafe", (.boolean false)), ("abi", (.atom "Rust")), ("is_variadic", (.boolean false)), ("inputs", (.array [(.object [("HashConsedValue", (.array [(.number 3364), (.object [("Ref", (.array [(.object [("Var", (.object [("Free", (.number 0))]))]), (.object [("Deduplicated", (.number 1225))]), (.atom "Mut")]))])]))]), (.object [("Deduplicated", (.number 1259))])])), ("output", (.object [("Deduplicated", (.number 1224))]))])), ("argument_count", (.number 2))], .array [(.object [("opcode", (.atom "LocalDeclaration")), ("function", (.number 8)), ("local", (.number 0)), ("role", (.atom "return")), ("declaration", (.object [("index", (.number 0)), ("name", (.null)), ("span", (.object [("data", (.object [("file_id", (.number 13)), ("beg", (.object [("line", (.number 415)), ("col", (.number 22))])), ("end", (.object [("line", (.number 415)), ("col", (.number 22))]))])), ("generated_from_span", (.null))])), ("ty", (.object [("Deduplicated", (.number 1224))]))]))]), (.object [("opcode", (.atom "LocalDeclaration")), ("function", (.number 8)), ("local", (.number 1)), ("role", (.atom "argument")), ("declaration", (.object [("index", (.number 1)), ("name", (.null)), ("span", (.object [("data", (.object [("file_id", (.number 13)), ("beg", (.object [("line", (.number 415)), ("col", (.number 8))])), ("end", (.object [("line", (.number 415)), ("col", (.number 46))]))])), ("generated_from_span", (.null))])), ("ty", (.object [("Deduplicated", (.number 1681))]))]))]), (.object [("opcode", (.atom "LocalDeclaration")), ("function", (.number 8)), ("local", (.number 2)), ("role", (.atom "argument")), ("declaration", (.object [("index", (.number 2)), ("name", (.atom "tupled_args")), ("span", (.object [("data", (.object [("file_id", (.number 0)), ("beg", (.object [("line", (.number 0)), ("col", (.number 0))])), ("end", (.object [("line", (.number 0)), ("col", (.number 0))]))])), ("generated_from_span", (.null))])), ("ty", (.object [("Deduplicated", (.number 1259))]))]))]), (.object [("opcode", (.atom "LocalDeclaration")), ("function", (.number 8)), ("local", (.number 3)), ("role", (.atom "temporary")), ("declaration", (.object [("index", (.number 3)), ("name", (.atom "a")), ("span", (.object [("data", (.object [("file_id", (.number 13)), ("beg", (.object [("line", (.number 415)), ("col", (.number 20))])), ("end", (.object [("line", (.number 415)), ("col", (.number 21))]))])), ("generated_from_span", (.null))])), ("ty", (.object [("Deduplicated", (.number 940))]))]))]), (.object [("opcode", (.atom "LocalDeclaration")), ("function", (.number 8)), ("local", (.number 4)), ("role", (.atom "temporary")), ("declaration", (.object [("index", (.number 4)), ("name", (.null)), ("span", (.object [("data", (.object [("file_id", (.number 13)), ("beg", (.object [("line", (.number 415)), ("col", (.number 41))])), ("end", (.object [("line", (.number 415)), ("col", (.number 45))]))])), ("generated_from_span", (.null))])), ("ty", (.object [("Deduplicated", (.number 939))]))]))]), (.object [("opcode", (.atom "LocalDeclaration")), ("function", (.number 8)), ("local", (.number 5)), ("role", (.atom "temporary")), ("declaration", (.object [("index", (.number 5)), ("name", (.null)), ("span", (.object [("data", (.object [("file_id", (.number 13)), ("beg", (.object [("line", (.number 415)), ("col", (.number 41))])), ("end", (.object [("line", (.number 415)), ("col", (.number 42))]))])), ("generated_from_span", (.null))])), ("ty", (.object [("HashConsedValue", (.array [(.number 1691), (.object [("Ref", (.array [(.object [("Body", (.number 3))]), (.object [("Deduplicated", (.number 1120))]), (.atom "Mut")]))])]))]))]))]), (.object [("opcode", (.atom "LocalDeclaration")), ("function", (.number 8)), ("local", (.number 6)), ("role", (.atom "temporary")), ("declaration", (.object [("index", (.number 6)), ("name", (.null)), ("span", (.object [("data", (.object [("file_id", (.number 13)), ("beg", (.object [("line", (.number 415)), ("col", (.number 41))])), ("end", (.object [("line", (.number 415)), ("col", (.number 45))]))])), ("generated_from_span", (.null))])), ("ty", (.object [("Deduplicated", (.number 1259))]))]))])], block17⟩
#print axioms program
end PV_STX2_SliceF8
