import PV_STX2_SliceSyntax
set_option autoImplicit false
namespace PV_STX2_SliceF13
open PV_STX2_Syntax PV_STX2_SliceSyntax
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node0 : Node :=
  .leaf (.storage ⟨13, 523, .array [(.atom "body"), (.atom "statements"), (.number 0)]⟩ true 0)
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node1 : Node :=
  .leaf (.storage ⟨13, 524, .array [(.atom "body"), (.atom "statements"), (.number 1)]⟩ true 2)
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node2 : Node :=
  .leaf (.storage ⟨13, 525, .array [(.atom "body"), (.atom "statements"), (.number 2)]⟩ true 3)
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node3 : Node :=
  .leaf (.bind ⟨13, 526, .array [(.atom "body"), (.atom "statements"), (.number 3)]⟩ (.local 3) (.reference (.project (.project (.project (.project (.local 1) (.deref)) (.field 0)) (.field 0)) (.field 2)) (.constant (.object [("kind", (.object [("Adt", (.array [(.null), (.array [])]))])), ("ty", (.object [("Deduplicated", (.number 946))]))]))))
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node4 : Node :=
  .leaf (.call ⟨13, 529, .array [(.atom "body"), (.atom "statements"), (.number 4)]⟩ (.object [("Regular", (.object [("kind", (.object [("Fun", (.object [("Regular", (.number 20))]))])), ("generics", (.object [("regions", (.array [(.object [("Body", (.number 7))])])), ("types", (.array [])), ("const_generics", (.array [])), ("trait_refs", (.array []))]))]))]) [(.move (.local 3))] (.local 2) [.storage ⟨13, 527, .array [(.atom "body"), (.atom "statements"), (.number 4), (.atom "kind"), (.atom "Call"), (.atom "on_unwind"), (.atom "statements"), (.number 0)]⟩ false 1,
.unwind ⟨13, 528, .array [(.atom "body"), (.atom "statements"), (.number 4), (.atom "kind"), (.atom "Call"), (.atom "on_unwind"), (.atom "statements"), (.number 1)]⟩])
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node5 : Node :=
  .leaf (.storage ⟨13, 530, .array [(.atom "body"), (.atom "statements"), (.number 5)]⟩ false 3)
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node6 : Node :=
  .leaf (.storage ⟨13, 531, .array [(.atom "body"), (.atom "statements"), (.number 6)]⟩ true 4)
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node7 : Node :=
  .leaf (.storage ⟨13, 532, .array [(.atom "body"), (.atom "statements"), (.number 7)]⟩ true 5)
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node8 : Node :=
  .leaf (.storage ⟨13, 533, .array [(.atom "body"), (.atom "statements"), (.number 8)]⟩ true 6)
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node9 : Node :=
  .leaf (.storage ⟨13, 534, .array [(.atom "body"), (.atom "statements"), (.number 9)]⟩ true 8)
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node10 : Node :=
  .leaf (.bind ⟨13, 535, .array [(.atom "body"), (.atom "statements"), (.number 10)]⟩ (.local 8) (.use (.copy (.project (.project (.project (.project (.project (.local 1) (.deref)) (.field 0)) (.field 0)) (.field 0)) (.field 0)))))
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node11 : Node :=
  .leaf (.bind ⟨13, 536, .array [(.atom "body"), (.atom "statements"), (.number 11)]⟩ (.local 6) (.unary (.object [("Cast", (.object [("Transmute", (.array [(.object [("Deduplicated", (.number 2205))]), (.object [("Deduplicated", (.number 2147))])]))]))]) (.copy (.local 8))))
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node12 : Node :=
  .leaf (.storage ⟨13, 537, .array [(.atom "body"), (.atom "statements"), (.number 12)]⟩ false 8)
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node13 : Node :=
  .leaf (.storage ⟨13, 538, .array [(.atom "body"), (.atom "statements"), (.number 13)]⟩ true 7)
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node14 : Node :=
  .leaf (.bind ⟨13, 539, .array [(.atom "body"), (.atom "statements"), (.number 14)]⟩ (.local 7) (.use (.copy (.project (.project (.local 1) (.deref)) (.field 1)))))
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node15 : Node :=
  .leaf (.call ⟨13, 540, .array [(.atom "body"), (.atom "statements"), (.number 15)]⟩ (.object [("Regular", (.object [("kind", (.object [("Fun", (.object [("Builtin", (.object [("PtrFromParts", (.atom "Shared"))]))]))])), ("generics", (.object [("regions", (.array [(.atom "Erased")])), ("types", (.array [(.object [("Deduplicated", (.number 2141))])])), ("const_generics", (.array [])), ("trait_refs", (.array []))]))]))]) [(.copy (.local 6)), (.move (.local 7))] (.local 5) [.abort ⟨13, 1113, .array [(.atom "body"), (.atom "statements"), (.number 15), (.atom "kind"), (.atom "Call"), (.atom "on_unwind"), (.atom "statements"), (.number 0)]⟩ (.atom "UndefinedBehavior")])
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node16 : Node :=
  .leaf (.storage ⟨13, 541, .array [(.atom "body"), (.atom "statements"), (.number 16)]⟩ false 7)
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node17 : Node :=
  .leaf (.storage ⟨13, 542, .array [(.atom "body"), (.atom "statements"), (.number 17)]⟩ false 6)
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node18 : Node :=
  .leaf (.bind ⟨13, 543, .array [(.atom "body"), (.atom "statements"), (.number 18)]⟩ (.local 4) (.reference (.project (.local 5) (.deref)) (.copy (.project (.local 5) (.metadata)))))
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node19 : Node :=
  .leaf (.storage ⟨13, 544, .array [(.atom "body"), (.atom "statements"), (.number 19)]⟩ false 5)
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node20 : Node :=
  .leaf (.call ⟨13, 547, .array [(.atom "body"), (.atom "statements"), (.number 20)]⟩ (.object [("Regular", (.object [("kind", (.object [("Fun", (.object [("Regular", (.number 21))]))])), ("generics", (.object [("regions", (.array [(.object [("Body", (.number 9))])])), ("types", (.array [])), ("const_generics", (.array [])), ("trait_refs", (.array []))]))]))]) [(.move (.local 4)), (.move (.local 2))] (.local 0) [.storage ⟨13, 545, .array [(.atom "body"), (.atom "statements"), (.number 20), (.atom "kind"), (.atom "Call"), (.atom "on_unwind"), (.atom "statements"), (.number 0)]⟩ false 1,
.unwind ⟨13, 546, .array [(.atom "body"), (.atom "statements"), (.number 20), (.atom "kind"), (.atom "Call"), (.atom "on_unwind"), (.atom "statements"), (.number 1)]⟩])
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node21 : Node :=
  .leaf (.storage ⟨13, 548, .array [(.atom "body"), (.atom "statements"), (.number 21)]⟩ false 4)
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node22 : Node :=
  .leaf (.storage ⟨13, 549, .array [(.atom "body"), (.atom "statements"), (.number 22)]⟩ false 2)
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node23 : Node :=
  .leaf (.storage ⟨13, 550, .array [(.atom "body"), (.atom "statements"), (.number 23)]⟩ false 1)
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def node24 : Node :=
  .leaf (.ret ⟨13, 551, .array [(.atom "body"), (.atom "statements"), (.number 24)]⟩ (.local 0))
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def block25 : List Node :=
  [node0, node1, node2, node3, node4, node5, node6, node7, node8, node9, node10, node11, node12, node13, node14, node15, node16, node17, node18, node19, node20, node21, node22, node23, node24]
/-- Conditional on owner acceptance of the translator patch. Generated verbatim
from option-on N94906, including branch and unwind payloads. -/
def program : PV_STX2_SliceSyntax.Program :=
  ⟨13, .object [("opcode", (.atom "CallEntry")), ("function", (.number 13)), ("signature", (.object [("is_unsafe", (.boolean false)), ("abi", (.atom "Rust")), ("is_variadic", (.boolean false)), ("inputs", (.array [(.object [("HashConsedValue", (.array [(.number 3369), (.object [("Ref", (.array [(.object [("Var", (.object [("Free", (.number 0))]))]), (.object [("Deduplicated", (.number 939))]), (.atom "Shared")]))])]))])])), ("output", (.object [("Deduplicated", (.number 939))]))])), ("argument_count", (.number 1))], .array [(.object [("opcode", (.atom "LocalDeclaration")), ("function", (.number 13)), ("local", (.number 0)), ("role", (.atom "return")), ("declaration", (.object [("index", (.number 0)), ("name", (.null)), ("span", (.object [("data", (.object [("file_id", (.number 4)), ("beg", (.object [("line", (.number 3813)), ("col", (.number 23))])), ("end", (.object [("line", (.number 3813)), ("col", (.number 27))]))])), ("generated_from_span", (.null))])), ("ty", (.object [("Deduplicated", (.number 939))]))]))]), (.object [("opcode", (.atom "LocalDeclaration")), ("function", (.number 13)), ("local", (.number 1)), ("role", (.atom "argument")), ("declaration", (.object [("index", (.number 1)), ("name", (.atom "self")), ("span", (.object [("data", (.object [("file_id", (.number 4)), ("beg", (.object [("line", (.number 3813)), ("col", (.number 13))])), ("end", (.object [("line", (.number 3813)), ("col", (.number 18))]))])), ("generated_from_span", (.null))])), ("ty", (.object [("HashConsedValue", (.array [(.number 2134), (.object [("Ref", (.array [(.object [("Body", (.number 1))]), (.object [("Deduplicated", (.number 939))]), (.atom "Shared")]))])]))]))]))]), (.object [("opcode", (.atom "LocalDeclaration")), ("function", (.number 13)), ("local", (.number 2)), ("role", (.atom "temporary")), ("declaration", (.object [("index", (.number 2)), ("name", (.atom "alloc")), ("span", (.object [("data", (.object [("file_id", (.number 4)), ("beg", (.object [("line", (.number 3814)), ("col", (.number 12))])), ("end", (.object [("line", (.number 3814)), ("col", (.number 17))]))])), ("generated_from_span", (.null))])), ("ty", (.object [("Deduplicated", (.number 938))]))]))]), (.object [("opcode", (.atom "LocalDeclaration")), ("function", (.number 13)), ("local", (.number 3)), ("role", (.atom "temporary")), ("declaration", (.object [("index", (.number 3)), ("name", (.null)), ("span", (.object [("data", (.object [("file_id", (.number 4)), ("beg", (.object [("line", (.number 3814)), ("col", (.number 20))])), ("end", (.object [("line", (.number 3814)), ("col", (.number 36))]))])), ("generated_from_span", (.null))])), ("ty", (.object [("HashConsedValue", (.array [(.number 2137), (.object [("Ref", (.array [(.object [("Body", (.number 3))]), (.object [("Deduplicated", (.number 938))]), (.atom "Shared")]))])]))]))]))]), (.object [("opcode", (.atom "LocalDeclaration")), ("function", (.number 13)), ("local", (.number 4)), ("role", (.atom "temporary")), ("declaration", (.object [("index", (.number 4)), ("name", (.null)), ("span", (.object [("data", (.object [("file_id", (.number 4)), ("beg", (.object [("line", (.number 3815)), ("col", (.number 26))])), ("end", (.object [("line", (.number 3815)), ("col", (.number 32))]))])), ("generated_from_span", (.null))])), ("ty", (.object [("HashConsedValue", (.array [(.number 2143), (.object [("Ref", (.array [(.object [("Body", (.number 5))]), (.object [("HashConsedValue", (.array [(.number 2141), (.object [("Slice", (.object [("Deduplicated", (.number 919))]))])]))]), (.atom "Shared")]))])]))]))]))]), (.object [("opcode", (.atom "LocalDeclaration")), ("function", (.number 13)), ("local", (.number 5)), ("role", (.atom "temporary")), ("declaration", (.object [("index", (.number 5)), ("name", (.atom "self")), ("span", (.object [("data", (.object [("file_id", (.number 4)), ("beg", (.object [("line", (.number 1871)), ("col", (.number 14))])), ("end", (.object [("line", (.number 1871)), ("col", (.number 94))]))])), ("generated_from_span", (.null))])), ("ty", (.object [("HashConsedValue", (.array [(.number 2145), (.object [("RawPtr", (.array [(.object [("Deduplicated", (.number 2141))]), (.atom "Shared")]))])]))]))]))]), (.object [("opcode", (.atom "LocalDeclaration")), ("function", (.number 13)), ("local", (.number 6)), ("role", (.atom "temporary")), ("declaration", (.object [("index", (.number 6)), ("name", (.null)), ("span", (.object [("data", (.object [("file_id", (.number 4)), ("beg", (.object [("line", (.number 1871)), ("col", (.number 70))])), ("end", (.object [("line", (.number 1871)), ("col", (.number 83))]))])), ("generated_from_span", (.null))])), ("ty", (.object [("HashConsedValue", (.array [(.number 2147), (.object [("RawPtr", (.array [(.object [("Deduplicated", (.number 919))]), (.atom "Shared")]))])]))]))]))]), (.object [("opcode", (.atom "LocalDeclaration")), ("function", (.number 13)), ("local", (.number 7)), ("role", (.atom "temporary")), ("declaration", (.object [("index", (.number 7)), ("name", (.null)), ("span", (.object [("data", (.object [("file_id", (.number 4)), ("beg", (.object [("line", (.number 1871)), ("col", (.number 85))])), ("end", (.object [("line", (.number 1871)), ("col", (.number 93))]))])), ("generated_from_span", (.null))])), ("ty", (.object [("Deduplicated", (.number 940))]))]))]), (.object [("opcode", (.atom "LocalDeclaration")), ("function", (.number 13)), ("local", (.number 8)), ("role", (.atom "temporary")), ("declaration", (.object [("index", (.number 8)), ("name", (.null)), ("span", (.object [("data", (.object [("file_id", (.number 11)), ("beg", (.object [("line", (.number 614)), ("col", (.number 8))])), ("end", (.object [("line", (.number 614)), ("col", (.number 16))]))])), ("generated_from_span", (.null))])), ("ty", (.object [("HashConsedValue", (.array [(.number 2205), (.object [("Adt", (.object [("id", (.object [("Adt", (.number 21))])), ("generics", (.object [("regions", (.array [])), ("types", (.array [])), ("const_generics", (.array [])), ("trait_refs", (.array []))]))]))])]))]))]))])], block25⟩
#print axioms program
end PV_STX2_SliceF13
