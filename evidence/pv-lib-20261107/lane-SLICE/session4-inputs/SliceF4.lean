import PV_STX2_SliceSyntax
set_option autoImplicit false
namespace PV_STX2_SliceF4
open PV_STX2_Syntax PV_STX2_SliceSyntax
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node0 : Node :=
  .leaf (.storage ⟨4, 48, .array [(.atom "body"), (.atom "statements"), (.number 0)]⟩ true 10)
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node1 : Node :=
  .leaf (.storage ⟨4, 49, .array [(.atom "body"), (.atom "statements"), (.number 1)]⟩ true 11)
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node2 : Node :=
  .leaf (.call ⟨4, 51, .array [(.atom "body"), (.atom "statements"), (.number 2)]⟩ (.object [("Regular", (.object [("kind", (.object [("Fun", (.object [("Regular", (.number 23))]))])), ("generics", (.object [("regions", (.array [])), ("types", (.array [])), ("const_generics", (.array [])), ("trait_refs", (.array []))]))]))]) [] (.local 11) [.storage ⟨4, 1115, .array [(.atom "body"), (.atom "statements"), (.number 2), (.atom "kind"), (.atom "Call"), (.atom "on_unwind"), (.atom "statements"), (.number 0)]⟩ false 11,
.storage ⟨4, 1116, .array [(.atom "body"), (.atom "statements"), (.number 2), (.atom "kind"), (.atom "Call"), (.atom "on_unwind"), (.atom "statements"), (.number 1)]⟩ false 10,
.abort ⟨4, 50, .array [(.atom "body"), (.atom "statements"), (.number 2), (.atom "kind"), (.atom "Call"), (.atom "on_unwind"), (.atom "statements"), (.number 2)]⟩ (.atom "UndefinedBehavior")])
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node3 : Node :=
  .leaf (.bind ⟨4, 52, .array [(.atom "body"), (.atom "statements"), (.number 3)]⟩ (.local 10) (.use (.move (.local 11))))
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node4 : Node :=
  .leaf (.storage ⟨4, 53, .array [(.atom "body"), (.atom "statements"), (.number 4)]⟩ true 0)
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node5 : Node :=
  .leaf (.storage ⟨4, 55, .array [(.atom "body"), (.atom "statements"), (.number 5)]⟩ true 9)
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node6 : Node :=
  .leaf (.storage ⟨4, 56, .array [(.atom "body"), (.atom "statements"), (.number 6)]⟩ true 2)
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node7 : Node :=
  .leaf (.call ⟨4, 57, .array [(.atom "body"), (.atom "statements"), (.number 7)]⟩ (.object [("Regular", (.object [("kind", (.object [("Fun", (.object [("Builtin", (.atom "ArrayRepeat"))]))])), ("generics", (.object [("regions", (.array [])), ("types", (.array [(.object [("Deduplicated", (.number 1344))])])), ("const_generics", (.array [(.object [("kind", (.object [("Literal", (.object [("Scalar", (.object [("Unsigned", (.array [(.atom "Usize"), (.atom "16")]))]))]))])), ("ty", (.object [("Deduplicated", (.number 940))]))])])), ("trait_refs", (.array []))]))]))]) [(.move (.local 10))] (.local 2) [.storage ⟨4, 1117, .array [(.atom "body"), (.atom "statements"), (.number 7), (.atom "kind"), (.atom "Call"), (.atom "on_unwind"), (.atom "statements"), (.number 0)]⟩ false 11,
.storage ⟨4, 1118, .array [(.atom "body"), (.atom "statements"), (.number 7), (.atom "kind"), (.atom "Call"), (.atom "on_unwind"), (.atom "statements"), (.number 1)]⟩ false 10,
.abort ⟨4, 1106, .array [(.atom "body"), (.atom "statements"), (.number 7), (.atom "kind"), (.atom "Call"), (.atom "on_unwind"), (.atom "statements"), (.number 2)]⟩ (.atom "UndefinedBehavior")])
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node8 : Node :=
  .leaf (.storage ⟨4, 58, .array [(.atom "body"), (.atom "statements"), (.number 8)]⟩ true 3)
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node9 : Node :=
  .leaf (.storage ⟨4, 59, .array [(.atom "body"), (.atom "statements"), (.number 9)]⟩ true 4)
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node10 : Node :=
  .leaf (.storage ⟨4, 60, .array [(.atom "body"), (.atom "statements"), (.number 10)]⟩ true 5)
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node11 : Node :=
  .leaf (.bind ⟨4, 61, .array [(.atom "body"), (.atom "statements"), (.number 11)]⟩ (.local 5) (.reference (.local 2) (.constant (.object [("kind", (.object [("Adt", (.array [(.null), (.array [])]))])), ("ty", (.object [("Deduplicated", (.number 946))]))]))))
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node12 : Node :=
  .leaf (.call ⟨4, 62, .array [(.atom "body"), (.atom "statements"), (.number 12)]⟩ (.object [("Regular", (.object [("kind", (.object [("Fun", (.object [("Builtin", (.atom "ArrayToSliceMut"))]))])), ("generics", (.object [("regions", (.array [(.atom "Erased")])), ("types", (.array [(.object [("Deduplicated", (.number 1344))])])), ("const_generics", (.array [(.object [("kind", (.object [("Literal", (.object [("Scalar", (.object [("Unsigned", (.array [(.atom "Usize"), (.atom "16")]))]))]))])), ("ty", (.object [("Deduplicated", (.number 940))]))])])), ("trait_refs", (.array []))]))]))]) [(.copy (.local 5))] (.local 4) [.storage ⟨4, 1119, .array [(.atom "body"), (.atom "statements"), (.number 12), (.atom "kind"), (.atom "Call"), (.atom "on_unwind"), (.atom "statements"), (.number 0)]⟩ false 11,
.storage ⟨4, 1120, .array [(.atom "body"), (.atom "statements"), (.number 12), (.atom "kind"), (.atom "Call"), (.atom "on_unwind"), (.atom "statements"), (.number 1)]⟩ false 10,
.abort ⟨4, 1107, .array [(.atom "body"), (.atom "statements"), (.number 12), (.atom "kind"), (.atom "Call"), (.atom "on_unwind"), (.atom "statements"), (.number 2)]⟩ (.atom "UndefinedBehavior")])
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node13 : Node :=
  .leaf (.call ⟨4, 67, .array [(.atom "body"), (.atom "statements"), (.number 13)]⟩ (.object [("Regular", (.object [("kind", (.object [("Fun", (.object [("Regular", (.number 9))]))])), ("generics", (.object [("regions", (.array [(.object [("Body", (.number 6))])])), ("types", (.array [])), ("const_generics", (.array [])), ("trait_refs", (.array []))]))]))]) [(.move (.local 4)), (.move (.local 1))] (.local 3) [.storage ⟨4, 63, .array [(.atom "body"), (.atom "statements"), (.number 13), (.atom "kind"), (.atom "Call"), (.atom "on_unwind"), (.atom "statements"), (.number 0)]⟩ false 9,
.storage ⟨4, 65, .array [(.atom "body"), (.atom "statements"), (.number 13), (.atom "kind"), (.atom "Call"), (.atom "on_unwind"), (.atom "statements"), (.number 1)]⟩ false 1,
.unwind ⟨4, 66, .array [(.atom "body"), (.atom "statements"), (.number 13), (.atom "kind"), (.atom "Call"), (.atom "on_unwind"), (.atom "statements"), (.number 2)]⟩])
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node14 : Node :=
  .leaf (.storage ⟨4, 68, .array [(.atom "body"), (.atom "statements"), (.number 14)]⟩ false 4)
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def block15 : List Node :=
  []
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node16 : Node :=
  .leaf (.storage ⟨4, 71, .array [(.atom "body"), (.atom "statements"), (.number 15), (.atom "kind"), (.atom "Switch"), (.atom "Match"), (.number 1), (.number 1), (.number 1), (.atom "statements"), (.number 0)]⟩ true 6)
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node17 : Node :=
  .leaf (.bind ⟨4, 72, .array [(.atom "body"), (.atom "statements"), (.number 15), (.atom "kind"), (.atom "Switch"), (.atom "Match"), (.number 1), (.number 1), (.number 1), (.atom "statements"), (.number 1)]⟩ (.local 6) (.use (.move (.project (.local 3) (.field 0)))))
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node18 : Node :=
  .leaf (.call ⟨4, 77, .array [(.atom "body"), (.atom "statements"), (.number 15), (.atom "kind"), (.atom "Switch"), (.atom "Match"), (.number 1), (.number 1), (.number 1), (.atom "statements"), (.number 2)]⟩ (.object [("Regular", (.object [("kind", (.object [("Fun", (.object [("Regular", (.number 11))]))])), ("generics", (.object [("regions", (.array [])), ("types", (.array [])), ("const_generics", (.array [])), ("trait_refs", (.array []))]))]))]) [(.move (.local 6))] (.local 0) [.storage ⟨4, 73, .array [(.atom "body"), (.atom "statements"), (.number 15), (.atom "kind"), (.atom "Switch"), (.atom "Match"), (.number 1), (.number 1), (.number 1), (.atom "statements"), (.number 2), (.atom "kind"), (.atom "Call"), (.atom "on_unwind"), (.atom "statements"), (.number 0)]⟩ false 9,
.storage ⟨4, 75, .array [(.atom "body"), (.atom "statements"), (.number 15), (.atom "kind"), (.atom "Switch"), (.atom "Match"), (.number 1), (.number 1), (.number 1), (.atom "statements"), (.number 2), (.atom "kind"), (.atom "Call"), (.atom "on_unwind"), (.atom "statements"), (.number 1)]⟩ false 1,
.unwind ⟨4, 76, .array [(.atom "body"), (.atom "statements"), (.number 15), (.atom "kind"), (.atom "Switch"), (.atom "Match"), (.number 1), (.number 1), (.number 1), (.atom "statements"), (.number 2), (.atom "kind"), (.atom "Call"), (.atom "on_unwind"), (.atom "statements"), (.number 2)]⟩])
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node19 : Node :=
  .leaf (.storage ⟨4, 78, .array [(.atom "body"), (.atom "statements"), (.number 15), (.atom "kind"), (.atom "Switch"), (.atom "Match"), (.number 1), (.number 1), (.number 1), (.atom "statements"), (.number 3)]⟩ false 6)
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node20 : Node :=
  .leaf (.storage ⟨4, 79, .array [(.atom "body"), (.atom "statements"), (.number 15), (.atom "kind"), (.atom "Switch"), (.atom "Match"), (.number 1), (.number 1), (.number 1), (.atom "statements"), (.number 4)]⟩ false 5)
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node21 : Node :=
  .leaf (.storage ⟨4, 80, .array [(.atom "body"), (.atom "statements"), (.number 15), (.atom "kind"), (.atom "Switch"), (.atom "Match"), (.number 1), (.number 1), (.number 1), (.atom "statements"), (.number 5)]⟩ false 3)
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node22 : Node :=
  .leaf (.storage ⟨4, 81, .array [(.atom "body"), (.atom "statements"), (.number 15), (.atom "kind"), (.atom "Switch"), (.atom "Match"), (.number 1), (.number 1), (.number 1), (.atom "statements"), (.number 6)]⟩ false 2)
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node23 : Node :=
  .leaf (.storage ⟨4, 82, .array [(.atom "body"), (.atom "statements"), (.number 15), (.atom "kind"), (.atom "Switch"), (.atom "Match"), (.number 1), (.number 1), (.number 1), (.atom "statements"), (.number 7)]⟩ false 9)
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node24 : Node :=
  .leaf (.storage ⟨4, 84, .array [(.atom "body"), (.atom "statements"), (.number 15), (.atom "kind"), (.atom "Switch"), (.atom "Match"), (.number 1), (.number 1), (.number 1), (.atom "statements"), (.number 8)]⟩ false 1)
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node25 : Node :=
  .leaf (.storage ⟨4, 1121, .array [(.atom "body"), (.atom "statements"), (.number 15), (.atom "kind"), (.atom "Switch"), (.atom "Match"), (.number 1), (.number 1), (.number 1), (.atom "statements"), (.number 9)]⟩ false 11)
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node26 : Node :=
  .leaf (.storage ⟨4, 1122, .array [(.atom "body"), (.atom "statements"), (.number 15), (.atom "kind"), (.atom "Switch"), (.atom "Match"), (.number 1), (.number 1), (.number 1), (.atom "statements"), (.number 10)]⟩ false 10)
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node27 : Node :=
  .leaf (.ret ⟨4, 85, .array [(.atom "body"), (.atom "statements"), (.number 15), (.atom "kind"), (.atom "Switch"), (.atom "Match"), (.number 1), (.number 1), (.number 1), (.atom "statements"), (.number 11)]⟩ (.local 0))
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def block28 : List Node :=
  [node16, node17, node18, node19, node20, node21, node22, node23, node24, node25, node26, node27]
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node29 : Node :=
  .matchAdt ⟨4, 90, .array [(.atom "body"), (.atom "statements"), (.number 15)]⟩ (.local 3) [([0], block15), ([1], block28)] none
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node30 : Node :=
  .leaf (.storage ⟨4, 91, .array [(.atom "body"), (.atom "statements"), (.number 16)]⟩ true 7)
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node31 : Node :=
  .leaf (.storage ⟨4, 92, .array [(.atom "body"), (.atom "statements"), (.number 17)]⟩ true 8)
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node32 : Node :=
  .leaf (.bind ⟨4, 93, .array [(.atom "body"), (.atom "statements"), (.number 18)]⟩ (.local 8) (.use (.move (.local 2))))
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node33 : Node :=
  .leaf (.call ⟨4, 98, .array [(.atom "body"), (.atom "statements"), (.number 19)]⟩ (.object [("Regular", (.object [("kind", (.object [("Fun", (.object [("Regular", (.number 10))]))])), ("generics", (.object [("regions", (.array [])), ("types", (.array [])), ("const_generics", (.array [])), ("trait_refs", (.array []))]))]))]) [] (.local 9) [.storage ⟨4, 94, .array [(.atom "body"), (.atom "statements"), (.number 19), (.atom "kind"), (.atom "Call"), (.atom "on_unwind"), (.atom "statements"), (.number 0)]⟩ false 9,
.storage ⟨4, 96, .array [(.atom "body"), (.atom "statements"), (.number 19), (.atom "kind"), (.atom "Call"), (.atom "on_unwind"), (.atom "statements"), (.number 1)]⟩ false 1,
.storage ⟨4, 1123, .array [(.atom "body"), (.atom "statements"), (.number 19), (.atom "kind"), (.atom "Call"), (.atom "on_unwind"), (.atom "statements"), (.number 2)]⟩ false 11,
.storage ⟨4, 1124, .array [(.atom "body"), (.atom "statements"), (.number 19), (.atom "kind"), (.atom "Call"), (.atom "on_unwind"), (.atom "statements"), (.number 3)]⟩ false 10,
.abort ⟨4, 97, .array [(.atom "body"), (.atom "statements"), (.number 19), (.atom "kind"), (.atom "Call"), (.atom "on_unwind"), (.atom "statements"), (.number 4)]⟩ (.atom "UndefinedBehavior")])
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node34 : Node :=
  .leaf (.bind ⟨4, 99, .array [(.atom "body"), (.atom "statements"), (.number 20)]⟩ (.local 7) (.unary (.object [("Cast", (.object [("Transmute", (.array [(.object [("Deduplicated", (.number 1345))]), (.object [("Deduplicated", (.number 941))])]))]))]) (.copy (.local 8))))
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node35 : Node :=
  .leaf (.storage ⟨4, 100, .array [(.atom "body"), (.atom "statements"), (.number 21)]⟩ false 8)
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node36 : Node :=
  .leaf (.call ⟨4, 105, .array [(.atom "body"), (.atom "statements"), (.number 22)]⟩ (.object [("Regular", (.object [("kind", (.object [("Fun", (.object [("Regular", (.number 12))]))])), ("generics", (.object [("regions", (.array [])), ("types", (.array [])), ("const_generics", (.array [])), ("trait_refs", (.array []))]))]))]) [(.move (.local 7))] (.local 0) [.storage ⟨4, 101, .array [(.atom "body"), (.atom "statements"), (.number 22), (.atom "kind"), (.atom "Call"), (.atom "on_unwind"), (.atom "statements"), (.number 0)]⟩ false 9,
.storage ⟨4, 103, .array [(.atom "body"), (.atom "statements"), (.number 22), (.atom "kind"), (.atom "Call"), (.atom "on_unwind"), (.atom "statements"), (.number 1)]⟩ false 1,
.unwind ⟨4, 104, .array [(.atom "body"), (.atom "statements"), (.number 22), (.atom "kind"), (.atom "Call"), (.atom "on_unwind"), (.atom "statements"), (.number 2)]⟩])
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node37 : Node :=
  .leaf (.storage ⟨4, 106, .array [(.atom "body"), (.atom "statements"), (.number 23)]⟩ false 7)
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node38 : Node :=
  .leaf (.storage ⟨4, 107, .array [(.atom "body"), (.atom "statements"), (.number 24)]⟩ false 5)
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node39 : Node :=
  .leaf (.storage ⟨4, 108, .array [(.atom "body"), (.atom "statements"), (.number 25)]⟩ false 3)
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node40 : Node :=
  .leaf (.storage ⟨4, 109, .array [(.atom "body"), (.atom "statements"), (.number 26)]⟩ false 2)
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node41 : Node :=
  .leaf (.storage ⟨4, 110, .array [(.atom "body"), (.atom "statements"), (.number 27)]⟩ false 9)
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node42 : Node :=
  .leaf (.storage ⟨4, 112, .array [(.atom "body"), (.atom "statements"), (.number 28)]⟩ false 1)
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node43 : Node :=
  .leaf (.storage ⟨4, 1125, .array [(.atom "body"), (.atom "statements"), (.number 29)]⟩ false 11)
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node44 : Node :=
  .leaf (.storage ⟨4, 1126, .array [(.atom "body"), (.atom "statements"), (.number 30)]⟩ false 10)
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node45 : Node :=
  .leaf (.ret ⟨4, 113, .array [(.atom "body"), (.atom "statements"), (.number 31)]⟩ (.local 0))
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def block46 : List Node :=
  [node0, node1, node2, node3, node4, node5, node6, node7, node8, node9, node10, node11, node12, node13, node14, node29, node30, node31, node32, node33, node34, node35, node36, node37, node38, node39, node40, node41, node42, node43, node44, node45]
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def program : PV_STX2_SliceSyntax.Program :=
  ⟨4, .object [("opcode", (.atom "CallEntry")), ("function", (.number 4)), ("signature", (.object [("is_unsafe", (.boolean false)), ("abi", (.atom "Rust")), ("is_variadic", (.boolean false)), ("inputs", (.array [(.object [("Deduplicated", (.number 1225))])])), ("output", (.object [("Deduplicated", (.number 1195))]))])), ("argument_count", (.number 1))], .array [(.object [("opcode", (.atom "LocalDeclaration")), ("function", (.number 4)), ("local", (.number 0)), ("role", (.atom "return")), ("declaration", (.object [("index", (.number 0)), ("name", (.null)), ("span", (.object [("data", (.object [("file_id", (.number 9)), ("beg", (.object [("line", (.number 149)), ("col", (.number 57))])), ("end", (.object [("line", (.number 149)), ("col", (.number 92))]))])), ("generated_from_span", (.null))])), ("ty", (.object [("Deduplicated", (.number 1195))]))]))]), (.object [("opcode", (.atom "LocalDeclaration")), ("function", (.number 4)), ("local", (.number 1)), ("role", (.atom "argument")), ("declaration", (.object [("index", (.number 1)), ("name", (.atom "cb")), ("span", (.object [("data", (.object [("file_id", (.number 9)), ("beg", (.object [("line", (.number 149)), ("col", (.number 47))])), ("end", (.object [("line", (.number 149)), ("col", (.number 49))]))])), ("generated_from_span", (.null))])), ("ty", (.object [("Deduplicated", (.number 1225))]))]))]), (.object [("opcode", (.atom "LocalDeclaration")), ("function", (.number 4)), ("local", (.number 2)), ("role", (.atom "temporary")), ("declaration", (.object [("index", (.number 2)), ("name", (.atom "array")), ("span", (.object [("data", (.object [("file_id", (.number 9)), ("beg", (.object [("line", (.number 154)), ("col", (.number 8))])), ("end", (.object [("line", (.number 154)), ("col", (.number 17))]))])), ("generated_from_span", (.null))])), ("ty", (.object [("HashConsedValue", (.array [(.number 1345), (.object [("Array", (.array [(.object [("Deduplicated", (.number 1344))]), (.object [("kind", (.object [("Literal", (.object [("Scalar", (.object [("Unsigned", (.array [(.atom "Usize"), (.atom "16")]))]))]))])), ("ty", (.object [("Deduplicated", (.number 940))]))])]))])]))]))]))]), (.object [("opcode", (.atom "LocalDeclaration")), ("function", (.number 4)), ("local", (.number 3)), ("role", (.atom "temporary")), ("declaration", (.object [("index", (.number 3)), ("name", (.null)), ("span", (.object [("data", (.object [("file_id", (.number 9)), ("beg", (.object [("line", (.number 155)), ("col", (.number 10))])), ("end", (.object [("line", (.number 155)), ("col", (.number 44))]))])), ("generated_from_span", (.null))])), ("ty", (.object [("HashConsedValue", (.array [(.number 1360), (.object [("Adt", (.object [("id", (.object [("Adt", (.number 10))])), ("generics", (.object [("regions", (.array [])), ("types", (.array [])), ("const_generics", (.array [])), ("trait_refs", (.array []))]))]))])]))]))]))]), (.object [("opcode", (.atom "LocalDeclaration")), ("function", (.number 4)), ("local", (.number 4)), ("role", (.atom "temporary")), ("declaration", (.object [("index", (.number 4)), ("name", (.null)), ("span", (.object [("data", (.object [("file_id", (.number 9)), ("beg", (.object [("line", (.number 155)), ("col", (.number 29))])), ("end", (.object [("line", (.number 155)), ("col", (.number 39))]))])), ("generated_from_span", (.null))])), ("ty", (.object [("HashConsedValue", (.array [(.number 1366), (.object [("Ref", (.array [(.object [("Body", (.number 1))]), (.object [("Deduplicated", (.number 1364))]), (.atom "Mut")]))])]))]))]))]), (.object [("opcode", (.atom "LocalDeclaration")), ("function", (.number 4)), ("local", (.number 5)), ("role", (.atom "temporary")), ("declaration", (.object [("index", (.number 5)), ("name", (.null)), ("span", (.object [("data", (.object [("file_id", (.number 9)), ("beg", (.object [("line", (.number 155)), ("col", (.number 29))])), ("end", (.object [("line", (.number 155)), ("col", (.number 39))]))])), ("generated_from_span", (.null))])), ("ty", (.object [("HashConsedValue", (.array [(.number 1369), (.object [("Ref", (.array [(.object [("Body", (.number 3))]), (.object [("Deduplicated", (.number 1345))]), (.atom "Mut")]))])]))]))]))]), (.object [("opcode", (.atom "LocalDeclaration")), ("function", (.number 4)), ("local", (.number 6)), ("role", (.atom "temporary")), ("declaration", (.object [("index", (.number 6)), ("name", (.atom "r")), ("span", (.object [("data", (.object [("file_id", (.number 9)), ("beg", (.object [("line", (.number 156)), ("col", (.number 27))])), ("end", (.object [("line", (.number 156)), ("col", (.number 28))]))])), ("generated_from_span", (.null))])), ("ty", (.object [("Deduplicated", (.number 1359))]))]))]), (.object [("opcode", (.atom "LocalDeclaration")), ("function", (.number 4)), ("local", (.number 7)), ("role", (.atom "temporary")), ("declaration", (.object [("index", (.number 7)), ("name", (.null)), ("span", (.object [("data", (.object [("file_id", (.number 9)), ("beg", (.object [("line", (.number 159)), ("col", (.number 18))])), ("end", (.object [("line", (.number 159)), ("col", (.number 66))]))])), ("generated_from_span", (.null))])), ("ty", (.object [("Deduplicated", (.number 941))]))]))]), (.object [("opcode", (.atom "LocalDeclaration")), ("function", (.number 4)), ("local", (.number 8)), ("role", (.atom "temporary")), ("declaration", (.object [("index", (.number 8)), ("name", (.atom "array")), ("span", (.object [("data", (.object [("file_id", (.number 9)), ("beg", (.object [("line", (.number 159)), ("col", (.number 58))])), ("end", (.object [("line", (.number 159)), ("col", (.number 63))]))])), ("generated_from_span", (.null))])), ("ty", (.object [("Deduplicated", (.number 1345))]))]))]), (.object [("opcode", (.atom "LocalDeclaration")), ("function", (.number 4)), ("local", (.number 9)), ("role", (.atom "temporary")), ("declaration", (.object [("index", (.number 9)), ("name", (.null)), ("span", (.object [("data", (.object [("file_id", (.number 16)), ("beg", (.object [("line", (.number 1054)), ("col", (.number 12))])), ("end", (.object [("line", (.number 1054)), ("col", (.number 52))]))])), ("generated_from_span", (.null))])), ("ty", (.object [("Deduplicated", (.number 946))]))]))]), (.object [("opcode", (.atom "LocalDeclaration")), ("function", (.number 4)), ("local", (.number 10)), ("role", (.atom "temporary")), ("declaration", (.object [("index", (.number 10)), ("name", (.null)), ("span", (.object [("data", (.object [("file_id", (.number 0)), ("beg", (.object [("line", (.number 0)), ("col", (.number 0))])), ("end", (.object [("line", (.number 0)), ("col", (.number 0))]))])), ("generated_from_span", (.null))])), ("ty", (.object [("Deduplicated", (.number 1344))]))]))]), (.object [("opcode", (.atom "LocalDeclaration")), ("function", (.number 4)), ("local", (.number 11)), ("role", (.atom "temporary")), ("declaration", (.object [("index", (.number 11)), ("name", (.null)), ("span", (.object [("data", (.object [("file_id", (.number 9)), ("beg", (.object [("line", (.number 154)), ("col", (.number 27))])), ("end", (.object [("line", (.number 154)), ("col", (.number 52))]))])), ("generated_from_span", (.null))])), ("ty", (.object [("Deduplicated", (.number 1344))]))]))])], block46⟩
#print axioms program
end PV_STX2_SliceF4
