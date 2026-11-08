import PV_STX2_SliceSyntax
set_option autoImplicit false
namespace PV_STX2_SliceF6
open PV_STX2_Syntax PV_STX2_SliceSyntax
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node0 : Node :=
  .leaf (.storage ⟨6, 136, .array [(.atom "body"), (.atom "statements"), (.number 0)]⟩ true 0)
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node1 : Node :=
  .leaf (.storage ⟨6, 137, .array [(.atom "body"), (.atom "statements"), (.number 1)]⟩ true 3)
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node2 : Node :=
  .leaf (.bind ⟨6, 138, .array [(.atom "body"), (.atom "statements"), (.number 2)]⟩ (.local 3) (.use (.move (.project (.local 2) (.field 0)))))
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node3 : Node :=
  .leaf (.storage ⟨6, 139, .array [(.atom "body"), (.atom "statements"), (.number 3)]⟩ true 4)
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node4 : Node :=
  .leaf (.bind ⟨6, 140, .array [(.atom "body"), (.atom "statements"), (.number 4)]⟩ (.local 4) (.use (.copy (.project (.project (.local 1) (.deref)) (.field 0)))))
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node5 : Node :=
  .leaf (.storage ⟨6, 141, .array [(.atom "body"), (.atom "statements"), (.number 5)]⟩ true 5)
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node6 : Node :=
  .leaf (.storage ⟨6, 142, .array [(.atom "body"), (.atom "statements"), (.number 6)]⟩ true 6)
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node7 : Node :=
  .leaf (.bind ⟨6, 143, .array [(.atom "body"), (.atom "statements"), (.number 7)]⟩ (.local 6) (.use (.copy (.project (.project (.local 1) (.deref)) (.field 0)))))
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node8 : Node :=
  .leaf (.bind ⟨6, 144, .array [(.atom "body"), (.atom "statements"), (.number 8)]⟩ (.local 5) (.binary "Offset" (.copy (.local 6)) (.constant (.object [("kind", (.object [("Literal", (.object [("Scalar", (.object [("Unsigned", (.array [(.atom "Usize"), (.atom "1")]))]))]))])), ("ty", (.object [("Deduplicated", (.number 940))]))]))))
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node9 : Node :=
  .leaf (.storage ⟨6, 145, .array [(.atom "body"), (.atom "statements"), (.number 9)]⟩ false 6)
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node10 : Node :=
  .leaf (.bind ⟨6, 146, .array [(.atom "body"), (.atom "statements"), (.number 10)]⟩ (.project (.project (.local 1) (.deref)) (.field 0)) (.use (.copy (.local 5))))
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node11 : Node :=
  .leaf (.storage ⟨6, 147, .array [(.atom "body"), (.atom "statements"), (.number 11)]⟩ false 5)
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node12 : Node :=
  .leaf (.storage ⟨6, 148, .array [(.atom "body"), (.atom "statements"), (.number 12)]⟩ true 7)
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node13 : Node :=
  .leaf (.bind ⟨6, 149, .array [(.atom "body"), (.atom "statements"), (.number 13)]⟩ (.local 7) (.reference (.project (.local 4) (.deref)) (.constant (.object [("kind", (.object [("Adt", (.array [(.null), (.array [])]))])), ("ty", (.object [("Deduplicated", (.number 946))]))]))))
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node14 : Node :=
  .leaf (.call ⟨6, 154, .array [(.atom "body"), (.atom "statements"), (.number 14)]⟩ (.object [("Regular", (.object [("kind", (.object [("Fun", (.object [("Regular", (.number 13))]))])), ("generics", (.object [("regions", (.array [(.object [("Body", (.number 5))])])), ("types", (.array [])), ("const_generics", (.array [])), ("trait_refs", (.array []))]))]))]) [(.move (.local 7))] (.local 0) [.storage ⟨6, 150, .array [(.atom "body"), (.atom "statements"), (.number 14), (.atom "kind"), (.atom "Call"), (.atom "on_unwind"), (.atom "statements"), (.number 0)]⟩ false 3,
.storage ⟨6, 151, .array [(.atom "body"), (.atom "statements"), (.number 14), (.atom "kind"), (.atom "Call"), (.atom "on_unwind"), (.atom "statements"), (.number 1)]⟩ false 2,
.storage ⟨6, 152, .array [(.atom "body"), (.atom "statements"), (.number 14), (.atom "kind"), (.atom "Call"), (.atom "on_unwind"), (.atom "statements"), (.number 2)]⟩ false 1,
.unwind ⟨6, 153, .array [(.atom "body"), (.atom "statements"), (.number 14), (.atom "kind"), (.atom "Call"), (.atom "on_unwind"), (.atom "statements"), (.number 3)]⟩])
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node15 : Node :=
  .leaf (.storage ⟨6, 155, .array [(.atom "body"), (.atom "statements"), (.number 15)]⟩ false 7)
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node16 : Node :=
  .leaf (.storage ⟨6, 156, .array [(.atom "body"), (.atom "statements"), (.number 16)]⟩ false 4)
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node17 : Node :=
  .leaf (.storage ⟨6, 157, .array [(.atom "body"), (.atom "statements"), (.number 17)]⟩ false 3)
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node18 : Node :=
  .leaf (.storage ⟨6, 158, .array [(.atom "body"), (.atom "statements"), (.number 18)]⟩ false 2)
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node19 : Node :=
  .leaf (.storage ⟨6, 159, .array [(.atom "body"), (.atom "statements"), (.number 19)]⟩ false 1)
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node20 : Node :=
  .leaf (.ret ⟨6, 160, .array [(.atom "body"), (.atom "statements"), (.number 20)]⟩ (.local 0))
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def block21 : List Node :=
  [node0, node1, node2, node3, node4, node5, node6, node7, node8, node9, node10, node11, node12, node13, node14, node15, node16, node17, node18, node19, node20]
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def program : PV_STX2_SliceSyntax.Program :=
  ⟨6, .object [("opcode", (.atom "CallEntry")), ("function", (.number 6)), ("signature", (.object [("is_unsafe", (.boolean false)), ("abi", (.atom "Rust")), ("is_variadic", (.boolean false)), ("inputs", (.array [(.object [("HashConsedValue", (.array [(.number 3363), (.object [("Ref", (.array [(.object [("Var", (.object [("Free", (.number 0))]))]), (.object [("Deduplicated", (.number 1120))]), (.atom "Mut")]))])]))]), (.object [("Deduplicated", (.number 1259))])])), ("output", (.object [("Deduplicated", (.number 939))]))])), ("argument_count", (.number 2))], .array [(.object [("opcode", (.atom "LocalDeclaration")), ("function", (.number 6)), ("local", (.number 0)), ("role", (.atom "return")), ("declaration", (.object [("index", (.number 0)), ("name", (.null)), ("span", (.object [("data", (.object [("file_id", (.number 9)), ("beg", (.object [("line", (.number 474)), ("col", (.number 24))])), ("end", (.object [("line", (.number 474)), ("col", (.number 24))]))])), ("generated_from_span", (.null))])), ("ty", (.object [("Deduplicated", (.number 939))]))]))]), (.object [("opcode", (.atom "LocalDeclaration")), ("function", (.number 6)), ("local", (.number 1)), ("role", (.atom "argument")), ("declaration", (.object [("index", (.number 1)), ("name", (.null)), ("span", (.object [("data", (.object [("file_id", (.number 9)), ("beg", (.object [("line", (.number 474)), ("col", (.number 16))])), ("end", (.object [("line", (.number 478)), ("col", (.number 9))]))])), ("generated_from_span", (.null))])), ("ty", (.object [("Deduplicated", (.number 1665))]))]))]), (.object [("opcode", (.atom "LocalDeclaration")), ("function", (.number 6)), ("local", (.number 2)), ("role", (.atom "argument")), ("declaration", (.object [("index", (.number 2)), ("name", (.atom "tupled_args")), ("span", (.object [("data", (.object [("file_id", (.number 0)), ("beg", (.object [("line", (.number 0)), ("col", (.number 0))])), ("end", (.object [("line", (.number 0)), ("col", (.number 0))]))])), ("generated_from_span", (.null))])), ("ty", (.object [("Deduplicated", (.number 1259))]))]))]), (.object [("opcode", (.atom "LocalDeclaration")), ("function", (.number 6)), ("local", (.number 3)), ("role", (.atom "temporary")), ("declaration", (.object [("index", (.number 3)), ("name", (.null)), ("span", (.object [("data", (.object [("file_id", (.number 9)), ("beg", (.object [("line", (.number 474)), ("col", (.number 22))])), ("end", (.object [("line", (.number 474)), ("col", (.number 23))]))])), ("generated_from_span", (.null))])), ("ty", (.object [("Deduplicated", (.number 940))]))]))]), (.object [("opcode", (.atom "LocalDeclaration")), ("function", (.number 6)), ("local", (.number 4)), ("role", (.atom "temporary")), ("declaration", (.object [("index", (.number 4)), ("name", (.atom "old")), ("span", (.object [("data", (.object [("file_id", (.number 9)), ("beg", (.object [("line", (.number 475)), ("col", (.number 16))])), ("end", (.object [("line", (.number 475)), ("col", (.number 19))]))])), ("generated_from_span", (.null))])), ("ty", (.object [("Deduplicated", (.number 1086))]))]))]), (.object [("opcode", (.atom "LocalDeclaration")), ("function", (.number 6)), ("local", (.number 5)), ("role", (.atom "temporary")), ("declaration", (.object [("index", (.number 5)), ("name", (.null)), ("span", (.object [("data", (.object [("file_id", (.number 9)), ("beg", (.object [("line", (.number 476)), ("col", (.number 18))])), ("end", (.object [("line", (.number 476)), ("col", (.number 28))]))])), ("generated_from_span", (.null))])), ("ty", (.object [("Deduplicated", (.number 1086))]))]))]), (.object [("opcode", (.atom "LocalDeclaration")), ("function", (.number 6)), ("local", (.number 6)), ("role", (.atom "temporary")), ("declaration", (.object [("index", (.number 6)), ("name", (.atom "self")), ("span", (.object [("data", (.object [("file_id", (.number 9)), ("beg", (.object [("line", (.number 476)), ("col", (.number 18))])), ("end", (.object [("line", (.number 476)), ("col", (.number 21))]))])), ("generated_from_span", (.null))])), ("ty", (.object [("Deduplicated", (.number 1086))]))]))]), (.object [("opcode", (.atom "LocalDeclaration")), ("function", (.number 6)), ("local", (.number 7)), ("role", (.atom "temporary")), ("declaration", (.object [("index", (.number 7)), ("name", (.null)), ("span", (.object [("data", (.object [("file_id", (.number 9)), ("beg", (.object [("line", (.number 477)), ("col", (.number 12))])), ("end", (.object [("line", (.number 477)), ("col", (.number 19))]))])), ("generated_from_span", (.null))])), ("ty", (.object [("HashConsedValue", (.array [(.number 1677), (.object [("Ref", (.array [(.object [("Body", (.number 3))]), (.object [("Deduplicated", (.number 939))]), (.atom "Shared")]))])]))]))]))])], block21⟩
#print axioms program
end PV_STX2_SliceF6
