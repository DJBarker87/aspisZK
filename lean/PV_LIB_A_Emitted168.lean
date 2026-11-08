import PV_STX2_SliceSyntax
set_option autoImplicit false
namespace PV_LIB_A_Emitted168
open PV_STX2_Syntax PV_STX2_SliceSyntax
/- Exact retained N95808 syntax, converted with unchanged pinned helpers. Syntax only. -/
def node0 : Node :=
  .leaf (.storage ⟨168, 7980, .array [(.atom "body"), (.atom "statements"), (.number 0)]⟩ true 0)
def node1 : Node :=
  .leaf (.storage ⟨168, 7981, .array [(.atom "body"), (.atom "statements"), (.number 1)]⟩ true 2)
def node2 : Node :=
  .leaf (.bind ⟨168, 7982, .array [(.atom "body"), (.atom "statements"), (.number 2)]⟩ (.local 2) (.use (.move (.project (.local 1) (.field 0)))))
def node3 : Node :=
  .leaf (.call ⟨168, 7985, .array [(.atom "body"), (.atom "statements"), (.number 3)]⟩ (.object [("Regular", (.object [("kind", (.object [("Fun", (.object [("Regular", (.number 274))]))])), ("generics", (.object [("regions", (.array [(.object [("Body", (.number 9))])])), ("types", (.array [(.object [("Deduplicated", (.number 38184))])])), ("const_generics", (.array [])), ("trait_refs", (.array []))]))]))]) [(.move (.local 2))] (.local 0) [.storage ⟨168, 7983, .array [(.atom "body"), (.atom "statements"), (.number 3), (.atom "kind"), (.atom "Call"), (.atom "on_unwind"), (.atom "statements"), (.number 0)]⟩ false 1,
.unwind ⟨168, 7984, .array [(.atom "body"), (.atom "statements"), (.number 3), (.atom "kind"), (.atom "Call"), (.atom "on_unwind"), (.atom "statements"), (.number 1)]⟩])
def node4 : Node :=
  .leaf (.storage ⟨168, 7986, .array [(.atom "body"), (.atom "statements"), (.number 4)]⟩ false 2)
def node5 : Node :=
  .leaf (.storage ⟨168, 7987, .array [(.atom "body"), (.atom "statements"), (.number 5)]⟩ false 1)
def node6 : Node :=
  .leaf (.ret ⟨168, 7988, .array [(.atom "body"), (.atom "statements"), (.number 6)]⟩ (.local 0))
def block7 : List Node :=
  [node0, node1, node2, node3, node4, node5, node6]
def program : PV_STX2_SliceSyntax.Program :=
  ⟨168, .object [("opcode", (.atom "CallEntry")), ("function", (.number 168)), ("signature", (.object [("is_unsafe", (.boolean false)), ("abi", (.atom "Rust")), ("is_variadic", (.boolean false)), ("inputs", (.array [(.object [("HashConsedValue", (.array [(.number 38332), (.object [("Adt", (.object [("id", (.object [("Adt", (.number 66))])), ("generics", (.object [("regions", (.array [(.object [("Var", (.object [("Free", (.number 0))]))])])), ("types", (.array [(.object [("Deduplicated", (.number 38184))])])), ("const_generics", (.array [])), ("trait_refs", (.array []))]))]))])]))])])), ("output", (.object [("Deduplicated", (.number 38248))]))])), ("argument_count", (.number 1))], .array [(.object [("opcode", (.atom "LocalDeclaration")), ("function", (.number 168)), ("local", (.number 0)), ("role", (.atom "return")), ("declaration", (.object [("index", (.number 0)), ("name", (.null)), ("span", (.object [("data", (.object [("file_id", (.number 17)), ("beg", (.object [("line", (.number 322)), ("col", (.number 25))])), ("end", (.object [("line", (.number 322)), ("col", (.number 34))]))])), ("generated_from_span", (.null))])), ("ty", (.object [("HashConsedValue", (.array [(.number 38939), (.object [("Adt", (.object [("id", (.object [("Adt", (.number 12))])), ("generics", (.object [("regions", (.array [])), ("types", (.array [(.object [("Deduplicated", (.number 38184))]), (.object [("Deduplicated", (.number 36040))])])), ("const_generics", (.array [])), ("trait_refs", (.array []))]))]))])]))]))]))]), (.object [("opcode", (.atom "LocalDeclaration")), ("function", (.number 168)), ("local", (.number 1)), ("role", (.atom "argument")), ("declaration", (.object [("index", (.number 1)), ("name", (.atom "self")), ("span", (.object [("data", (.object [("file_id", (.number 17)), ("beg", (.object [("line", (.number 322)), ("col", (.number 16))])), ("end", (.object [("line", (.number 322)), ("col", (.number 20))]))])), ("generated_from_span", (.null))])), ("ty", (.object [("HashConsedValue", (.array [(.number 38940), (.object [("Adt", (.object [("id", (.object [("Adt", (.number 66))])), ("generics", (.object [("regions", (.array [(.object [("Body", (.number 5))])])), ("types", (.array [(.object [("Deduplicated", (.number 38184))])])), ("const_generics", (.array [])), ("trait_refs", (.array []))]))]))])]))]))]))]), (.object [("opcode", (.atom "LocalDeclaration")), ("function", (.number 168)), ("local", (.number 2)), ("role", (.atom "temporary")), ("declaration", (.object [("index", (.number 2)), ("name", (.null)), ("span", (.object [("data", (.object [("file_id", (.number 17)), ("beg", (.object [("line", (.number 323)), ("col", (.number 8))])), ("end", (.object [("line", (.number 323)), ("col", (.number 14))]))])), ("generated_from_span", (.null))])), ("ty", (.object [("HashConsedValue", (.array [(.number 38941), (.object [("Adt", (.object [("id", (.object [("Adt", (.number 93))])), ("generics", (.object [("regions", (.array [(.object [("Body", (.number 7))])])), ("types", (.array [(.object [("Deduplicated", (.number 38184))])])), ("const_generics", (.array [])), ("trait_refs", (.array []))]))]))])]))]))]))])], block7⟩
#print axioms program
end PV_LIB_A_Emitted168
