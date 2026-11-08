import PV_THR2_Program
set_option autoImplicit false
namespace PV_THR2_F220
open PV_STX2_Syntax PV_STX2_SliceSyntax
/-- Conditional on owner acceptance of amended translator. Hypotheses: none.
Generated syntax only; original cleanup retained without interpreting matches. -/
def node0 : Node :=
  .leaf (.storage ⟨220, 9236, .array [(.atom "body"), (.atom "statements"), (.number 0)]⟩ true 0)
/-- Conditional on owner acceptance of amended translator. Hypotheses: none.
Generated syntax only; original cleanup retained without interpreting matches. -/
def node1 : Node :=
  .leaf (.storage ⟨220, 9237, .array [(.atom "body"), (.atom "statements"), (.number 1)]⟩ true 3)
/-- Conditional on owner acceptance of amended translator. Hypotheses: none.
Generated syntax only; original cleanup retained without interpreting matches. -/
def node2 : Node :=
  .leaf (.bind ⟨220, 9238, .array [(.atom "body"), (.atom "statements"), (.number 2)]⟩ (.local 3) (.use (.move (.project (.local 1) (.field 0)))))
/-- Conditional on owner acceptance of amended translator. Hypotheses: none.
Generated syntax only; original cleanup retained without interpreting matches. -/
def node3 : Node :=
  .leaf (.storage ⟨220, 9239, .array [(.atom "body"), (.atom "statements"), (.number 3)]⟩ true 4)
/-- Conditional on owner acceptance of amended translator. Hypotheses: none.
Generated syntax only; original cleanup retained without interpreting matches. -/
def node4 : Node :=
  .leaf (.aggregateMove ⟨220, 9240, .array [(.atom "body"), (.atom "statements"), (.number 4)]⟩ (.local 4) (.object [("Adt", (.array [(.object [("id", (.atom "Tuple")), ("generics", (.object [("regions", (.array [])), ("types", (.array [])), ("const_generics", (.array [])), ("trait_refs", (.array []))]))]), (.null), (.null)]))]) [])
/-- Conditional on owner acceptance of amended translator. Hypotheses: none.
Generated syntax only; original cleanup retained without interpreting matches. -/
def node5 : Node :=
  .leaf (.call ⟨220, 9244, .array [(.atom "body"), (.atom "statements"), (.number 5)]⟩ (.object [("Regular", (.object [("kind", (.object [("Trait", (.array [(.object [("Deduplicated", (.number 38321))]), (.number 0)]))])), ("generics", (.object [("regions", (.array [])), ("types", (.array [])), ("const_generics", (.array [])), ("trait_refs", (.array []))]))]))]) [(.move (.local 3)), (.move (.local 4))] (.local 0) [])
/-- Conditional on owner acceptance of amended translator. Hypotheses: none.
Generated syntax only; original cleanup retained without interpreting matches. -/
def node6 : Node :=
  .leaf (.storage ⟨220, 9245, .array [(.atom "body"), (.atom "statements"), (.number 6)]⟩ false 4)
/-- Conditional on owner acceptance of amended translator. Hypotheses: none.
Generated syntax only; original cleanup retained without interpreting matches. -/
def node7 : Node :=
  .leaf (.storage ⟨220, 9246, .array [(.atom "body"), (.atom "statements"), (.number 7)]⟩ false 3)
/-- Conditional on owner acceptance of amended translator. Hypotheses: none.
Generated syntax only; original cleanup retained without interpreting matches. -/
def node8 : Node :=
  .leaf (.storage ⟨220, 9247, .array [(.atom "body"), (.atom "statements"), (.number 8)]⟩ false 2)
/-- Conditional on owner acceptance of amended translator. Hypotheses: none.
Generated syntax only; original cleanup retained without interpreting matches. -/
def node9 : Node :=
  .leaf (.storage ⟨220, 9248, .array [(.atom "body"), (.atom "statements"), (.number 9)]⟩ false 1)
/-- Conditional on owner acceptance of amended translator. Hypotheses: none.
Generated syntax only; original cleanup retained without interpreting matches. -/
def node10 : Node :=
  .leaf (.ret ⟨220, 9249, .array [(.atom "body"), (.atom "statements"), (.number 10)]⟩ (.local 0))
/-- Conditional on owner acceptance of amended translator. Hypotheses: none.
Generated syntax only; original cleanup retained without interpreting matches. -/
def block11 : List Node :=
  [node0, node1, node2, node3, node4, node5, node6, node7, node8, node9, node10]
/-- Conditional on owner acceptance of amended translator. Hypotheses: none.
Generated syntax only; original cleanup retained without interpreting matches. -/
def live : PV_STX2_SliceSyntax.Program :=
  ⟨220, .object [("opcode", (.atom "CallEntry")), ("function", (.number 220)), ("signature", (.object [("is_unsafe", (.boolean false)), ("abi", (.object [("Other", (.atom "rust-call"))])), ("is_variadic", (.boolean false)), ("inputs", (.array [(.object [("HashConsedValue", (.array [(.number 38320), (.object [("Adt", (.object [("id", (.object [("Adt", (.number 59))])), ("generics", (.object [("regions", (.array [])), ("types", (.array [(.object [("Deduplicated", (.number 38186))])])), ("const_generics", (.array [])), ("trait_refs", (.array []))]))]))])]))]), (.object [("Deduplicated", (.number 646))])])), ("output", (.object [("Deduplicated", (.number 38184))]))])), ("argument_count", (.number 2))], .array [(.object [("opcode", (.atom "LocalDeclaration")), ("function", (.number 220)), ("local", (.number 0)), ("role", (.atom "return")), ("declaration", (.object [("index", (.number 0)), ("name", (.null)), ("span", (.object [("data", (.object [("file_id", (.number 71)), ("beg", (.object [("line", (.number 274)), ("col", (.number 56))])), ("end", (.object [("line", (.number 274)), ("col", (.number 57))]))])), ("generated_from_span", (.null))])), ("ty", (.object [("Deduplicated", (.number 38184))]))]))]), (.object [("opcode", (.atom "LocalDeclaration")), ("function", (.number 220)), ("local", (.number 1)), ("role", (.atom "argument")), ("declaration", (.object [("index", (.number 1)), ("name", (.atom "self")), ("span", (.object [("data", (.object [("file_id", (.number 71)), ("beg", (.object [("line", (.number 274)), ("col", (.number 36))])), ("end", (.object [("line", (.number 274)), ("col", (.number 40))]))])), ("generated_from_span", (.null))])), ("ty", (.object [("Deduplicated", (.number 38320))]))]))]), (.object [("opcode", (.atom "LocalDeclaration")), ("function", (.number 220)), ("local", (.number 2)), ("role", (.atom "argument")), ("declaration", (.object [("index", (.number 2)), ("name", (.atom "_args")), ("span", (.object [("data", (.object [("file_id", (.number 71)), ("beg", (.object [("line", (.number 274)), ("col", (.number 42))])), ("end", (.object [("line", (.number 274)), ("col", (.number 47))]))])), ("generated_from_span", (.null))])), ("ty", (.object [("Deduplicated", (.number 646))]))]))]), (.object [("opcode", (.atom "LocalDeclaration")), ("function", (.number 220)), ("local", (.number 3)), ("role", (.atom "temporary")), ("declaration", (.object [("index", (.number 3)), ("name", (.null)), ("span", (.object [("data", (.object [("file_id", (.number 71)), ("beg", (.object [("line", (.number 275)), ("col", (.number 8))])), ("end", (.object [("line", (.number 275)), ("col", (.number 16))]))])), ("generated_from_span", (.null))])), ("ty", (.object [("Deduplicated", (.number 38186))]))]))]), (.object [("opcode", (.atom "LocalDeclaration")), ("function", (.number 220)), ("local", (.number 4)), ("role", (.atom "temporary")), ("declaration", (.object [("index", (.number 4)), ("name", (.null)), ("span", (.object [("data", (.object [("file_id", (.number 71)), ("beg", (.object [("line", (.number 275)), ("col", (.number 8))])), ("end", (.object [("line", (.number 275)), ("col", (.number 18))]))])), ("generated_from_span", (.null))])), ("ty", (.object [("Deduplicated", (.number 646))]))]))])], block11⟩
/-- Conditional on owner acceptance of amended translator. Hypotheses: none.
Generated syntax only; original cleanup retained without interpreting matches. -/
def cleanup0 : String := "{\"span\":{\"data\":{\"file_id\":71,\"beg\":{\"line\":274,\"col\":4},\"end\":{\"line\":276,\"col\":5}},\"generated_from_span\":null},\"statements\":[{\"opcode\":\"Native.StorageDead\",\"identity\":{\"function\":220,\"statement\":9241,\"path\":[\"body\",\"statements\",5,\"kind\",\"Call\",\"on_unwind\",\"statements\",0]},\"span\":{\"data\":{\"file_id\":71,\"beg\":{\"line\":274,\"col\":4},\"end\":{\"line\":276,\"col\":5}},\"generated_from_span\":null},\"comments_before\":[],\"native_opcode\":\"StorageDead\",\"native\":{\"StorageDead\":2}},{\"opcode\":\"Native.StorageDead\",\"identity\":{\"function\":220,\"statement\":9242,\"path\":[\"body\",\"statements\",5,\"kind\",\"Call\",\"on_unwind\",\"statements\",1]},\"span\":{\"data\":{\"file_id\":71,\"beg\":{\"line\":274,\"col\":4},\"end\":{\"line\":276,\"col\":5}},\"generated_from_span\":null},\"comments_before\":[],\"native_opcode\":\"StorageDead\",\"native\":{\"StorageDead\":1}},{\"opcode\":\"Native.UnwindResume\",\"identity\":{\"function\":220,\"statement\":9243,\"path\":[\"body\",\"statements\",5,\"kind\",\"Call\",\"on_unwind\",\"statements\",2]},\"span\":{\"data\":{\"file_id\":71,\"beg\":{\"line\":274,\"col\":4},\"end\":{\"line\":276,\"col\":5}},\"generated_from_span\":null},\"comments_before\":[],\"native_opcode\":\"UnwindResume\",\"native\":\"UnwindResume\"}]}"
/-- Conditional on owner acceptance of amended translator. Hypotheses: none.
Generated syntax only; original cleanup retained without interpreting matches. -/
def cleanupSite0 : Site := ⟨220, 9244, .array [(.atom "body"), (.atom "statements"), (.number 5)]⟩
/-- Conditional on owner acceptance of amended translator. Hypotheses: none.
Generated syntax only; original cleanup retained without interpreting matches. -/
def program : PV_THR2_Program.Program :=
  ⟨live, [(cleanupSite0, cleanup0)]⟩
#print axioms program
end PV_THR2_F220
