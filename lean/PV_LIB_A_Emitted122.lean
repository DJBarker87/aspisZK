import PV_STX2_SliceSyntax
set_option autoImplicit false
namespace PV_LIB_A_Emitted122
open PV_STX2_Syntax PV_STX2_SliceSyntax
/- Exact retained N95808 syntax, converted with unchanged pinned helpers. Syntax only. -/
def node0 : Node :=
  .leaf (.storage ⟨122, 4842, .array [(.atom "body"), (.atom "statements"), (.number 0)]⟩ true 0)
def node1 : Node :=
  .leaf (.storage ⟨122, 4843, .array [(.atom "body"), (.atom "statements"), (.number 1)]⟩ true 1)
def node2 : Node :=
  .leaf (.storage ⟨122, 4844, .array [(.atom "body"), (.atom "statements"), (.number 2)]⟩ true 2)
def node3 : Node :=
  .leaf (.storage ⟨122, 4845, .array [(.atom "body"), (.atom "statements"), (.number 3)]⟩ true 3)
def node4 : Node :=
  .leaf (.bind ⟨122, 4846, .array [(.atom "body"), (.atom "statements"), (.number 4)]⟩ (.local 3) (.reference (.global 9) (.constant (.object [("kind", (.object [("Adt", (.array [(.null), (.array [])]))])), ("ty", (.object [("Deduplicated", (.number 646))]))]))))
def node5 : Node :=
  .leaf (.bind ⟨122, 4847, .array [(.atom "body"), (.atom "statements"), (.number 5)]⟩ (.local 2) (.reference (.project (.local 3) (.deref)) (.constant (.object [("kind", (.object [("Adt", (.array [(.null), (.array [])]))])), ("ty", (.object [("Deduplicated", (.number 646))]))]))))
def node6 : Node :=
  .leaf (.call ⟨122, 4849, .array [(.atom "body"), (.atom "statements"), (.number 6)]⟩ (.object [("Regular", (.object [("kind", (.object [("Fun", (.object [("Regular", (.number 209))]))])), ("generics", (.object [("regions", (.array [(.object [("Body", (.number 9))])])), ("types", (.array [])), ("const_generics", (.array [])), ("trait_refs", (.array []))]))]))]) [(.move (.local 2))] (.local 1) [.unwind ⟨122, 4848, .array [(.atom "body"), (.atom "statements"), (.number 6), (.atom "kind"), (.atom "Call"), (.atom "on_unwind"), (.atom "statements"), (.number 0)]⟩])
def node7 : Node :=
  .leaf (.storage ⟨122, 4850, .array [(.atom "body"), (.atom "statements"), (.number 7)]⟩ false 2)
def node8 : Node :=
  .leaf (.storage ⟨122, 4851, .array [(.atom "body"), (.atom "statements"), (.number 8)]⟩ false 3)
def node9 : Node :=
  .leaf (.storage ⟨122, 4852, .array [(.atom "body"), (.atom "statements"), (.number 9)]⟩ true 4)
def node10 : Node :=
  .leaf (.storage ⟨122, 4853, .array [(.atom "body"), (.atom "statements"), (.number 10)]⟩ true 5)
def node11 : Node :=
  .leaf (.bind ⟨122, 4854, .array [(.atom "body"), (.atom "statements"), (.number 11)]⟩ (.local 5) (.use (.copy (.local 1))))
def node12 : Node :=
  .leaf (.bind ⟨122, 4855, .array [(.atom "body"), (.atom "statements"), (.number 12)]⟩ (.local 4) (.binary "Gt" (.move (.local 5)) (.copy (.global 10))))
def block13 : List Node :=
  []
def node14 : Node :=
  .leaf (.storage ⟨122, 4857, .array [(.atom "body"), (.atom "statements"), (.number 13), (.atom "kind"), (.atom "Switch"), (.atom "If"), (.number 2), (.atom "statements"), (.number 0)]⟩ false 5)
def node15 : Node :=
  .leaf (.storage ⟨122, 4858, .array [(.atom "body"), (.atom "statements"), (.number 13), (.atom "kind"), (.atom "Switch"), (.atom "If"), (.number 2), (.atom "statements"), (.number 1)]⟩ true 13)
def node16 : Node :=
  .leaf (.storage ⟨122, 4859, .array [(.atom "body"), (.atom "statements"), (.number 13), (.atom "kind"), (.atom "Switch"), (.atom "If"), (.number 2), (.atom "statements"), (.number 2)]⟩ true 14)
def node17 : Node :=
  .leaf (.bind ⟨122, 4860, .array [(.atom "body"), (.atom "statements"), (.number 13), (.atom "kind"), (.atom "Switch"), (.atom "If"), (.number 2), (.atom "statements"), (.number 3)]⟩ (.local 14) (.use (.copy (.local 1))))
def node18 : Node :=
  .leaf (.bind ⟨122, 4861, .array [(.atom "body"), (.atom "statements"), (.number 13), (.atom "kind"), (.atom "Switch"), (.atom "If"), (.number 2), (.atom "statements"), (.number 4)]⟩ (.local 13) (.binary "Eq" (.move (.local 14)) (.copy (.global 10))))
def node19 : Node :=
  .leaf (.storage ⟨122, 4862, .array [(.atom "body"), (.atom "statements"), (.number 13), (.atom "kind"), (.atom "Switch"), (.atom "If"), (.number 2), (.atom "statements"), (.number 5), (.atom "kind"), (.atom "Switch"), (.atom "If"), (.number 1), (.atom "statements"), (.number 0)]⟩ false 14)
def node20 : Node :=
  .leaf (.storage ⟨122, 4863, .array [(.atom "body"), (.atom "statements"), (.number 13), (.atom "kind"), (.atom "Switch"), (.atom "If"), (.number 2), (.atom "statements"), (.number 5), (.atom "kind"), (.atom "Switch"), (.atom "If"), (.number 1), (.atom "statements"), (.number 1)]⟩ true 15)
def node21 : Node :=
  .leaf (.call ⟨122, 4865, .array [(.atom "body"), (.atom "statements"), (.number 13), (.atom "kind"), (.atom "Switch"), (.atom "If"), (.number 2), (.atom "statements"), (.number 5), (.atom "kind"), (.atom "Switch"), (.atom "If"), (.number 1), (.atom "statements"), (.number 2)]⟩ (.object [("Regular", (.object [("kind", (.object [("Fun", (.object [("Regular", (.number 211))]))])), ("generics", (.object [("regions", (.array [])), ("types", (.array [])), ("const_generics", (.array [])), ("trait_refs", (.array []))]))]))]) [] (.local 15) [.unwind ⟨122, 4864, .array [(.atom "body"), (.atom "statements"), (.number 13), (.atom "kind"), (.atom "Switch"), (.atom "If"), (.number 2), (.atom "statements"), (.number 5), (.atom "kind"), (.atom "Switch"), (.atom "If"), (.number 1), (.atom "statements"), (.number 2), (.atom "kind"), (.atom "Call"), (.atom "on_unwind"), (.atom "statements"), (.number 0)]⟩])
def node22 : Node :=
  .leaf (.storage ⟨122, 4866, .array [(.atom "body"), (.atom "statements"), (.number 13), (.atom "kind"), (.atom "Switch"), (.atom "If"), (.number 2), (.atom "statements"), (.number 5), (.atom "kind"), (.atom "Switch"), (.atom "If"), (.number 1), (.atom "statements"), (.number 3)]⟩ true 16)
def node23 : Node :=
  .leaf (.aggregateMove ⟨122, 4867, .array [(.atom "body"), (.atom "statements"), (.number 13), (.atom "kind"), (.atom "Switch"), (.atom "If"), (.number 2), (.atom "statements"), (.number 5), (.atom "kind"), (.atom "Switch"), (.atom "If"), (.number 1), (.atom "statements"), (.number 4)]⟩ (.local 16) (.object [("Adt", (.array [(.object [("id", (.object [("Adt", (.number 17))])), ("generics", (.object [("regions", (.array [])), ("types", (.array [(.object [("Deduplicated", (.number 8229))])])), ("const_generics", (.array [])), ("trait_refs", (.array []))]))]), (.number 0), (.null)]))]) [])
def node24 : Node :=
  .leaf (.call ⟨122, 4869, .array [(.atom "body"), (.atom "statements"), (.number 13), (.atom "kind"), (.atom "Switch"), (.atom "If"), (.number 2), (.atom "statements"), (.number 5), (.atom "kind"), (.atom "Switch"), (.atom "If"), (.number 1), (.atom "statements"), (.number 5)]⟩ (.object [("Regular", (.object [("kind", (.object [("Fun", (.object [("Regular", (.number 213))]))])), ("generics", (.object [("regions", (.array [])), ("types", (.array [])), ("const_generics", (.array [])), ("trait_refs", (.array []))]))]))]) [(.move (.local 15)), (.move (.local 16))] (.local 0) [.unwind ⟨122, 4868, .array [(.atom "body"), (.atom "statements"), (.number 13), (.atom "kind"), (.atom "Switch"), (.atom "If"), (.number 2), (.atom "statements"), (.number 5), (.atom "kind"), (.atom "Switch"), (.atom "If"), (.number 1), (.atom "statements"), (.number 5), (.atom "kind"), (.atom "Call"), (.atom "on_unwind"), (.atom "statements"), (.number 0)]⟩])
def node25 : Node :=
  .leaf (.storage ⟨122, 4870, .array [(.atom "body"), (.atom "statements"), (.number 13), (.atom "kind"), (.atom "Switch"), (.atom "If"), (.number 2), (.atom "statements"), (.number 5), (.atom "kind"), (.atom "Switch"), (.atom "If"), (.number 1), (.atom "statements"), (.number 6)]⟩ false 16)
def node26 : Node :=
  .leaf (.storage ⟨122, 4871, .array [(.atom "body"), (.atom "statements"), (.number 13), (.atom "kind"), (.atom "Switch"), (.atom "If"), (.number 2), (.atom "statements"), (.number 5), (.atom "kind"), (.atom "Switch"), (.atom "If"), (.number 1), (.atom "statements"), (.number 7)]⟩ false 15)
def block27 : List Node :=
  [node19, node20, node21, node22, node23, node24, node25, node26]
def node28 : Node :=
  .leaf (.storage ⟨122, 4873, .array [(.atom "body"), (.atom "statements"), (.number 13), (.atom "kind"), (.atom "Switch"), (.atom "If"), (.number 2), (.atom "statements"), (.number 5), (.atom "kind"), (.atom "Switch"), (.atom "If"), (.number 2), (.atom "statements"), (.number 0)]⟩ false 14)
def node29 : Node :=
  .leaf (.storage ⟨122, 4874, .array [(.atom "body"), (.atom "statements"), (.number 13), (.atom "kind"), (.atom "Switch"), (.atom "If"), (.number 2), (.atom "statements"), (.number 5), (.atom "kind"), (.atom "Switch"), (.atom "If"), (.number 2), (.atom "statements"), (.number 1)]⟩ true 17)
def node30 : Node :=
  .leaf (.bind ⟨122, 4875, .array [(.atom "body"), (.atom "statements"), (.number 13), (.atom "kind"), (.atom "Switch"), (.atom "If"), (.number 2), (.atom "statements"), (.number 5), (.atom "kind"), (.atom "Switch"), (.atom "If"), (.number 2), (.atom "statements"), (.number 2)]⟩ (.local 17) (.use (.copy (.local 1))))
def node31 : Node :=
  .leaf (.call ⟨122, 4877, .array [(.atom "body"), (.atom "statements"), (.number 13), (.atom "kind"), (.atom "Switch"), (.atom "If"), (.number 2), (.atom "statements"), (.number 5), (.atom "kind"), (.atom "Switch"), (.atom "If"), (.number 2), (.atom "statements"), (.number 3)]⟩ (.object [("Regular", (.object [("kind", (.object [("Fun", (.object [("Regular", (.number 212))]))])), ("generics", (.object [("regions", (.array [])), ("types", (.array [])), ("const_generics", (.array [])), ("trait_refs", (.array []))]))]))]) [(.move (.local 17))] (.local 0) [.unwind ⟨122, 4876, .array [(.atom "body"), (.atom "statements"), (.number 13), (.atom "kind"), (.atom "Switch"), (.atom "If"), (.number 2), (.atom "statements"), (.number 5), (.atom "kind"), (.atom "Switch"), (.atom "If"), (.number 2), (.atom "statements"), (.number 3), (.atom "kind"), (.atom "Call"), (.atom "on_unwind"), (.atom "statements"), (.number 0)]⟩])
def node32 : Node :=
  .leaf (.storage ⟨122, 4878, .array [(.atom "body"), (.atom "statements"), (.number 13), (.atom "kind"), (.atom "Switch"), (.atom "If"), (.number 2), (.atom "statements"), (.number 5), (.atom "kind"), (.atom "Switch"), (.atom "If"), (.number 2), (.atom "statements"), (.number 4)]⟩ false 17)
def block33 : List Node :=
  [node28, node29, node30, node31, node32]
def node34 : Node :=
  .branch ⟨122, 4880, .array [(.atom "body"), (.atom "statements"), (.number 13), (.atom "kind"), (.atom "Switch"), (.atom "If"), (.number 2), (.atom "statements"), (.number 5)]⟩ (.move (.local 13)) block27 block33
def node35 : Node :=
  .leaf (.storage ⟨122, 4881, .array [(.atom "body"), (.atom "statements"), (.number 13), (.atom "kind"), (.atom "Switch"), (.atom "If"), (.number 2), (.atom "statements"), (.number 6)]⟩ false 13)
def node36 : Node :=
  .leaf (.storage ⟨122, 4882, .array [(.atom "body"), (.atom "statements"), (.number 13), (.atom "kind"), (.atom "Switch"), (.atom "If"), (.number 2), (.atom "statements"), (.number 7)]⟩ false 4)
def node37 : Node :=
  .leaf (.storage ⟨122, 4883, .array [(.atom "body"), (.atom "statements"), (.number 13), (.atom "kind"), (.atom "Switch"), (.atom "If"), (.number 2), (.atom "statements"), (.number 8)]⟩ false 1)
def node38 : Node :=
  .leaf (.ret ⟨122, 4884, .array [(.atom "body"), (.atom "statements"), (.number 13), (.atom "kind"), (.atom "Switch"), (.atom "If"), (.number 2), (.atom "statements"), (.number 9)]⟩ (.local 0))
def block39 : List Node :=
  [node14, node15, node16, node17, node18, node34, node35, node36, node37, node38]
def node40 : Node :=
  .branch ⟨122, 4885, .array [(.atom "body"), (.atom "statements"), (.number 13)]⟩ (.move (.local 4)) block13 block39
def node41 : Node :=
  .leaf (.storage ⟨122, 4886, .array [(.atom "body"), (.atom "statements"), (.number 14)]⟩ false 5)
def node42 : Node :=
  .leaf (.storage ⟨122, 4887, .array [(.atom "body"), (.atom "statements"), (.number 15)]⟩ true 6)
def node43 : Node :=
  .leaf (.storage ⟨122, 4888, .array [(.atom "body"), (.atom "statements"), (.number 16)]⟩ true 7)
def node44 : Node :=
  .leaf (.storage ⟨122, 4889, .array [(.atom "body"), (.atom "statements"), (.number 17)]⟩ true 8)
def node45 : Node :=
  .leaf (.storage ⟨122, 4890, .array [(.atom "body"), (.atom "statements"), (.number 18)]⟩ true 9)
def node46 : Node :=
  .leaf (.bind ⟨122, 4891, .array [(.atom "body"), (.atom "statements"), (.number 19)]⟩ (.local 9) (.use (.copy (.local 1))))
def node47 : Node :=
  .leaf (.bind ⟨122, 4892, .array [(.atom "body"), (.atom "statements"), (.number 20)]⟩ (.local 8) (.unary (.object [("Cast", (.object [("RawPtr", (.array [(.object [("Deduplicated", (.number 8111))]), (.object [("Deduplicated", (.number 8184))])]))]))]) (.move (.local 9))))
def node48 : Node :=
  .leaf (.storage ⟨122, 4893, .array [(.atom "body"), (.atom "statements"), (.number 21)]⟩ false 9)
def node49 : Node :=
  .leaf (.call ⟨122, 4895, .array [(.atom "body"), (.atom "statements"), (.number 22)]⟩ (.object [("Regular", (.object [("kind", (.object [("Fun", (.object [("Regular", (.number 210))]))])), ("generics", (.object [("regions", (.array [])), ("types", (.array [])), ("const_generics", (.array [])), ("trait_refs", (.array []))]))]))]) [(.move (.local 8))] (.local 7) [.unwind ⟨122, 4894, .array [(.atom "body"), (.atom "statements"), (.number 22), (.atom "kind"), (.atom "Call"), (.atom "on_unwind"), (.atom "statements"), (.number 0)]⟩])
def node50 : Node :=
  .leaf (.storage ⟨122, 4896, .array [(.atom "body"), (.atom "statements"), (.number 23)]⟩ false 8)
def node51 : Node :=
  .leaf (.call ⟨122, 4898, .array [(.atom "body"), (.atom "statements"), (.number 24)]⟩ (.object [("Regular", (.object [("kind", (.object [("Fun", (.object [("Regular", (.number 134))]))])), ("generics", (.object [("regions", (.array [])), ("types", (.array [(.object [("Deduplicated", (.number 5054))])])), ("const_generics", (.array [])), ("trait_refs", (.array []))]))]))]) [(.move (.local 7))] (.local 6) [.unwind ⟨122, 4897, .array [(.atom "body"), (.atom "statements"), (.number 24), (.atom "kind"), (.atom "Call"), (.atom "on_unwind"), (.atom "statements"), (.number 0)]⟩])
def node52 : Node :=
  .leaf (.storage ⟨122, 4899, .array [(.atom "body"), (.atom "statements"), (.number 25)]⟩ false 7)
def node53 : Node :=
  .leaf (.storage ⟨122, 4900, .array [(.atom "body"), (.atom "statements"), (.number 26)]⟩ true 10)
def node54 : Node :=
  .leaf (.storage ⟨122, 4901, .array [(.atom "body"), (.atom "statements"), (.number 27)]⟩ true 11)
def node55 : Node :=
  .leaf (.storage ⟨122, 4902, .array [(.atom "body"), (.atom "statements"), (.number 28)]⟩ true 12)
def node56 : Node :=
  .leaf (.bind ⟨122, 4903, .array [(.atom "body"), (.atom "statements"), (.number 29)]⟩ (.local 12) (.reference (.local 6) (.constant (.object [("kind", (.object [("Adt", (.array [(.null), (.array [])]))])), ("ty", (.object [("Deduplicated", (.number 646))]))]))))
def node57 : Node :=
  .leaf (.call ⟨122, 4905, .array [(.atom "body"), (.atom "statements"), (.number 30)]⟩ (.object [("Regular", (.object [("kind", (.object [("Fun", (.object [("Regular", (.number 135))]))])), ("generics", (.object [("regions", (.array [(.object [("Body", (.number 11))])])), ("types", (.array [(.object [("Deduplicated", (.number 5054))])])), ("const_generics", (.array [])), ("trait_refs", (.array []))]))]))]) [(.move (.local 12))] (.local 11) [.unwind ⟨122, 4904, .array [(.atom "body"), (.atom "statements"), (.number 30), (.atom "kind"), (.atom "Call"), (.atom "on_unwind"), (.atom "statements"), (.number 0)]⟩])
def node58 : Node :=
  .leaf (.bind ⟨122, 4906, .array [(.atom "body"), (.atom "statements"), (.number 31)]⟩ (.local 10) (.reference (.project (.local 11) (.deref)) (.constant (.object [("kind", (.object [("Adt", (.array [(.null), (.array [])]))])), ("ty", (.object [("Deduplicated", (.number 646))]))]))))
def node59 : Node :=
  .leaf (.storage ⟨122, 4907, .array [(.atom "body"), (.atom "statements"), (.number 32)]⟩ false 12)
def node60 : Node :=
  .leaf (.call ⟨122, 4909, .array [(.atom "body"), (.atom "statements"), (.number 33)]⟩ (.object [("Regular", (.object [("kind", (.object [("Fun", (.object [("Regular", (.number 214))]))])), ("generics", (.object [("regions", (.array [(.object [("Body", (.number 13))])])), ("types", (.array [])), ("const_generics", (.array [])), ("trait_refs", (.array []))]))]))]) [(.move (.local 10))] (.local 0) [.unwind ⟨122, 4908, .array [(.atom "body"), (.atom "statements"), (.number 33), (.atom "kind"), (.atom "Call"), (.atom "on_unwind"), (.atom "statements"), (.number 0)]⟩])
def node61 : Node :=
  .leaf (.storage ⟨122, 4910, .array [(.atom "body"), (.atom "statements"), (.number 34)]⟩ false 11)
def node62 : Node :=
  .leaf (.storage ⟨122, 4911, .array [(.atom "body"), (.atom "statements"), (.number 35)]⟩ false 10)
def node63 : Node :=
  .leaf (.storage ⟨122, 4912, .array [(.atom "body"), (.atom "statements"), (.number 36)]⟩ false 6)
def node64 : Node :=
  .leaf (.storage ⟨122, 4913, .array [(.atom "body"), (.atom "statements"), (.number 37)]⟩ false 4)
def node65 : Node :=
  .leaf (.storage ⟨122, 4914, .array [(.atom "body"), (.atom "statements"), (.number 38)]⟩ false 1)
def node66 : Node :=
  .leaf (.ret ⟨122, 4915, .array [(.atom "body"), (.atom "statements"), (.number 39)]⟩ (.local 0))
def block67 : List Node :=
  [node0, node1, node2, node3, node4, node5, node6, node7, node8, node9, node10, node11, node12, node40, node41, node42, node43, node44, node45, node46, node47, node48, node49, node50, node51, node52, node53, node54, node55, node56, node57, node58, node59, node60, node61, node62, node63, node64, node65, node66]
def program : PV_STX2_SliceSyntax.Program :=
  ⟨122, .object [("opcode", (.atom "CallEntry")), ("function", (.number 122)), ("signature", (.object [("is_unsafe", (.boolean false)), ("abi", (.atom "Rust")), ("is_variadic", (.boolean false)), ("inputs", (.array [])), ("output", (.object [("Deduplicated", (.number 5054))]))])), ("argument_count", (.number 0))], .array [(.object [("opcode", (.atom "LocalDeclaration")), ("function", (.number 122)), ("local", (.number 0)), ("role", (.atom "return")), ("declaration", (.object [("index", (.number 0)), ("name", (.null)), ("span", (.object [("data", (.object [("file_id", (.number 74)), ("beg", (.object [("line", (.number 241)), ("col", (.number 38))])), ("end", (.object [("line", (.number 241)), ("col", (.number 44))]))])), ("generated_from_span", (.null))])), ("ty", (.object [("Deduplicated", (.number 5054))]))]))]), (.object [("opcode", (.atom "LocalDeclaration")), ("function", (.number 122)), ("local", (.number 1)), ("role", (.atom "temporary")), ("declaration", (.object [("index", (.number 1)), ("name", (.atom "current")), ("span", (.object [("data", (.object [("file_id", (.number 74)), ("beg", (.object [("line", (.number 242)), ("col", (.number 8))])), ("end", (.object [("line", (.number 242)), ("col", (.number 15))]))])), ("generated_from_span", (.null))])), ("ty", (.object [("HashConsedValue", (.array [(.number 8111), (.object [("RawPtr", (.array [(.object [("Deduplicated", (.number 646))]), (.atom "Mut")]))])]))]))]))]), (.object [("opcode", (.atom "LocalDeclaration")), ("function", (.number 122)), ("local", (.number 2)), ("role", (.atom "temporary")), ("declaration", (.object [("index", (.number 2)), ("name", (.null)), ("span", (.object [("data", (.object [("file_id", (.number 74)), ("beg", (.object [("line", (.number 242)), ("col", (.number 18))])), ("end", (.object [("line", (.number 242)), ("col", (.number 25))]))])), ("generated_from_span", (.null))])), ("ty", (.object [("HashConsedValue", (.array [(.number 8179), (.object [("Ref", (.array [(.object [("Body", (.number 1))]), (.object [("Deduplicated", (.number 8177))]), (.atom "Shared")]))])]))]))]))]), (.object [("opcode", (.atom "LocalDeclaration")), ("function", (.number 122)), ("local", (.number 3)), ("role", (.atom "temporary")), ("declaration", (.object [("index", (.number 3)), ("name", (.null)), ("span", (.object [("data", (.object [("file_id", (.number 74)), ("beg", (.object [("line", (.number 242)), ("col", (.number 18))])), ("end", (.object [("line", (.number 242)), ("col", (.number 25))]))])), ("generated_from_span", (.null))])), ("ty", (.object [("HashConsedValue", (.array [(.number 8180), (.object [("Ref", (.array [(.object [("Body", (.number 2))]), (.object [("Deduplicated", (.number 8177))]), (.atom "Shared")]))])]))]))]))]), (.object [("opcode", (.atom "LocalDeclaration")), ("function", (.number 122)), ("local", (.number 4)), ("role", (.atom "temporary")), ("declaration", (.object [("index", (.number 4)), ("name", (.null)), ("span", (.object [("data", (.object [("file_id", (.number 74)), ("beg", (.object [("line", (.number 243)), ("col", (.number 7))])), ("end", (.object [("line", (.number 243)), ("col", (.number 26))]))])), ("generated_from_span", (.null))])), ("ty", (.object [("Deduplicated", (.number 556))]))]))]), (.object [("opcode", (.atom "LocalDeclaration")), ("function", (.number 122)), ("local", (.number 5)), ("role", (.atom "temporary")), ("declaration", (.object [("index", (.number 5)), ("name", (.null)), ("span", (.object [("data", (.object [("file_id", (.number 74)), ("beg", (.object [("line", (.number 243)), ("col", (.number 7))])), ("end", (.object [("line", (.number 243)), ("col", (.number 14))]))])), ("generated_from_span", (.null))])), ("ty", (.object [("Deduplicated", (.number 8111))]))]))]), (.object [("opcode", (.atom "LocalDeclaration")), ("function", (.number 122)), ("local", (.number 6)), ("role", (.atom "temporary")), ("declaration", (.object [("index", (.number 6)), ("name", (.atom "current")), ("span", (.object [("data", (.object [("file_id", (.number 74)), ("beg", (.object [("line", (.number 245)), ("col", (.number 16))])), ("end", (.object [("line", (.number 245)), ("col", (.number 23))]))])), ("generated_from_span", (.null))])), ("ty", (.object [("HashConsedValue", (.array [(.number 8183), (.object [("Adt", (.object [("id", (.object [("Adt", (.number 24))])), ("generics", (.object [("regions", (.array [])), ("types", (.array [(.object [("Deduplicated", (.number 5054))])])), ("const_generics", (.array [])), ("trait_refs", (.array []))]))]))])]))]))]))]), (.object [("opcode", (.atom "LocalDeclaration")), ("function", (.number 122)), ("local", (.number 7)), ("role", (.atom "temporary")), ("declaration", (.object [("index", (.number 7)), ("name", (.null)), ("span", (.object [("data", (.object [("file_id", (.number 74)), ("beg", (.object [("line", (.number 245)), ("col", (.number 44))])), ("end", (.object [("line", (.number 245)), ("col", (.number 69))]))])), ("generated_from_span", (.null))])), ("ty", (.object [("Deduplicated", (.number 5054))]))]))]), (.object [("opcode", (.atom "LocalDeclaration")), ("function", (.number 122)), ("local", (.number 8)), ("role", (.atom "temporary")), ("declaration", (.object [("index", (.number 8)), ("name", (.null)), ("span", (.object [("data", (.object [("file_id", (.number 74)), ("beg", (.object [("line", (.number 245)), ("col", (.number 61))])), ("end", (.object [("line", (.number 245)), ("col", (.number 68))]))])), ("generated_from_span", (.null))])), ("ty", (.object [("HashConsedValue", (.array [(.number 8184), (.object [("RawPtr", (.array [(.object [("Deduplicated", (.number 646))]), (.atom "Shared")]))])]))]))]))]), (.object [("opcode", (.atom "LocalDeclaration")), ("function", (.number 122)), ("local", (.number 9)), ("role", (.atom "temporary")), ("declaration", (.object [("index", (.number 9)), ("name", (.null)), ("span", (.object [("data", (.object [("file_id", (.number 74)), ("beg", (.object [("line", (.number 245)), ("col", (.number 61))])), ("end", (.object [("line", (.number 245)), ("col", (.number 68))]))])), ("generated_from_span", (.null))])), ("ty", (.object [("Deduplicated", (.number 8111))]))]))]), (.object [("opcode", (.atom "LocalDeclaration")), ("function", (.number 122)), ("local", (.number 10)), ("role", (.atom "temporary")), ("declaration", (.object [("index", (.number 10)), ("name", (.null)), ("span", (.object [("data", (.object [("file_id", (.number 74)), ("beg", (.object [("line", (.number 246)), ("col", (.number 12))])), ("end", (.object [("line", (.number 246)), ("col", (.number 22))]))])), ("generated_from_span", (.null))])), ("ty", (.object [("HashConsedValue", (.array [(.number 8186), (.object [("Ref", (.array [(.object [("Body", (.number 4))]), (.object [("Deduplicated", (.number 5054))]), (.atom "Shared")]))])]))]))]))]), (.object [("opcode", (.atom "LocalDeclaration")), ("function", (.number 122)), ("local", (.number 11)), ("role", (.atom "temporary")), ("declaration", (.object [("index", (.number 11)), ("name", (.null)), ("span", (.object [("data", (.object [("file_id", (.number 74)), ("beg", (.object [("line", (.number 246)), ("col", (.number 12))])), ("end", (.object [("line", (.number 246)), ("col", (.number 22))]))])), ("generated_from_span", (.null))])), ("ty", (.object [("HashConsedValue", (.array [(.number 8187), (.object [("Ref", (.array [(.object [("Body", (.number 5))]), (.object [("Deduplicated", (.number 5054))]), (.atom "Shared")]))])]))]))]))]), (.object [("opcode", (.atom "LocalDeclaration")), ("function", (.number 122)), ("local", (.number 12)), ("role", (.atom "temporary")), ("declaration", (.object [("index", (.number 12)), ("name", (.null)), ("span", (.object [("data", (.object [("file_id", (.number 74)), ("beg", (.object [("line", (.number 246)), ("col", (.number 14))])), ("end", (.object [("line", (.number 246)), ("col", (.number 21))]))])), ("generated_from_span", (.null))])), ("ty", (.object [("HashConsedValue", (.array [(.number 8190), (.object [("Ref", (.array [(.object [("Body", (.number 7))]), (.object [("Deduplicated", (.number 8183))]), (.atom "Shared")]))])]))]))]))]), (.object [("opcode", (.atom "LocalDeclaration")), ("function", (.number 122)), ("local", (.number 13)), ("role", (.atom "temporary")), ("declaration", (.object [("index", (.number 13)), ("name", (.null)), ("span", (.object [("data", (.object [("file_id", (.number 74)), ("beg", (.object [("line", (.number 248)), ("col", (.number 14))])), ("end", (.object [("line", (.number 248)), ("col", (.number 34))]))])), ("generated_from_span", (.null))])), ("ty", (.object [("Deduplicated", (.number 556))]))]))]), (.object [("opcode", (.atom "LocalDeclaration")), ("function", (.number 122)), ("local", (.number 14)), ("role", (.atom "temporary")), ("declaration", (.object [("index", (.number 14)), ("name", (.null)), ("span", (.object [("data", (.object [("file_id", (.number 74)), ("beg", (.object [("line", (.number 248)), ("col", (.number 14))])), ("end", (.object [("line", (.number 248)), ("col", (.number 21))]))])), ("generated_from_span", (.null))])), ("ty", (.object [("Deduplicated", (.number 8111))]))]))]), (.object [("opcode", (.atom "LocalDeclaration")), ("function", (.number 122)), ("local", (.number 15)), ("role", (.atom "temporary")), ("declaration", (.object [("index", (.number 15)), ("name", (.null)), ("span", (.object [("data", (.object [("file_id", (.number 74)), ("beg", (.object [("line", (.number 249)), ("col", (.number 20))])), ("end", (.object [("line", (.number 249)), ("col", (.number 37))]))])), ("generated_from_span", (.null))])), ("ty", (.object [("Deduplicated", (.number 8202))]))]))]), (.object [("opcode", (.atom "LocalDeclaration")), ("function", (.number 122)), ("local", (.number 16)), ("role", (.atom "temporary")), ("declaration", (.object [("index", (.number 16)), ("name", (.null)), ("span", (.object [("data", (.object [("file_id", (.number 74)), ("beg", (.object [("line", (.number 249)), ("col", (.number 39))])), ("end", (.object [("line", (.number 249)), ("col", (.number 43))]))])), ("generated_from_span", (.null))])), ("ty", (.object [("Deduplicated", (.number 8230))]))]))]), (.object [("opcode", (.atom "LocalDeclaration")), ("function", (.number 122)), ("local", (.number 17)), ("role", (.atom "temporary")), ("declaration", (.object [("index", (.number 17)), ("name", (.null)), ("span", (.object [("data", (.object [("file_id", (.number 74)), ("beg", (.object [("line", (.number 251)), ("col", (.number 21))])), ("end", (.object [("line", (.number 251)), ("col", (.number 28))]))])), ("generated_from_span", (.null))])), ("ty", (.object [("Deduplicated", (.number 8111))]))]))])], block67⟩
#print axioms program
end PV_LIB_A_Emitted122
