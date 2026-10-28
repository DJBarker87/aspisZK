import NDO_JGo_TX2_MessageRead
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGo_TX2_Message16
open Aeneas Aeneas.Std Result
attribute [local irreducible] JFx_NativeBytes.proof JFw_Frames.window
def bytes16 : Array U8 32#usize := ⟨JGe_Window31.c16,by rfl⟩
def value16 : AspisR1Stage2.Stage2Finish.E := ⟨⟨⟨803870182#u32,1437850321#u32⟩,⟨1097546635#u32,478299721#u32⟩⟩,⟨⟨1135309810#u32,617984551#u32⟩,⟨483028248#u32,1325182773#u32⟩⟩⟩
def record16 : AspisR1RecordParser.field.wide_exact.WideExact := ⟨⟨⟨803870182#u32,1437850321#u32⟩,⟨1097546635#u32,478299721#u32⟩⟩,⟨⟨1135309810#u32,617984551#u32⟩,⟨483028248#u32,1325182773#u32⟩⟩⟩
theorem selected16 : ((JFw_Frames.window 8007 2048).val.drop (32*16)).take 32=bytes16.val := by
  rw [JGo_TX2_MessageRead.cell 16 (by decide)]
  exact JGe_Window31.selected16
#print axioms selected16
theorem parser16 : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes16)=ok (some record16) := by
  apply (AspisR1.ExtractedRecordByteCanonicality.fixed_success_iff bytes16 record16).mpr
  constructor
  · intro j
    fin_cases j <;> decide
  · rfl
#print axioms parser16
theorem field16 : FIn_Primitives.field (JFw_Frames.window 8007 2048) 16#usize=ok value16 :=
  JGo_TX2_FieldRead.source _ _ bytes16 record16
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    selected16 parser16
#print axioms field16
theorem native_parser16 : FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes16)=ok (some (FIo_Install.toE value16)) := by
  with_unfolding_all rfl
#print axioms native_parser16
theorem native_field16 : FIo_Native.weights.field (JFw_Frames.window 8007 2048) 16#usize=
    ok (FIo_Install.toE value16) :=
  JGo_TX2_MessageRead.native _ 16#usize 512#usize 17#usize 544#usize bytes16 _
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 16#usize 32#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 16#usize 1#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 17#usize 32#usize (by decide)))
    (JGo_TX2_MessageRead.range _ _ _ bytes16 (by decide)
      (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
      (by decide) selected16) native_parser16
#print axioms native_field16
theorem canonical16 : Port4C_QueryArithmetic.CanonE value16 := by
  change (803870182<2147483647 ∧ 1437850321<2147483647 ∧ 1097546635<2147483647 ∧ 478299721<2147483647) ∧
    (1135309810<2147483647 ∧ 617984551<2147483647 ∧ 483028248<2147483647 ∧ 1325182773<2147483647)
  omega
#print axioms canonical16
def bytes17 : Array U8 32#usize := ⟨JGe_Window31.c17,by rfl⟩
def value17 : AspisR1Stage2.Stage2Finish.E := ⟨⟨⟨1755312639#u32,414966063#u32⟩,⟨1075065169#u32,1645423591#u32⟩⟩,⟨⟨271932602#u32,294888196#u32⟩,⟨1031140955#u32,1176464510#u32⟩⟩⟩
def record17 : AspisR1RecordParser.field.wide_exact.WideExact := ⟨⟨⟨1755312639#u32,414966063#u32⟩,⟨1075065169#u32,1645423591#u32⟩⟩,⟨⟨271932602#u32,294888196#u32⟩,⟨1031140955#u32,1176464510#u32⟩⟩⟩
theorem selected17 : ((JFw_Frames.window 8007 2048).val.drop (32*17)).take 32=bytes17.val := by
  rw [JGo_TX2_MessageRead.cell 17 (by decide)]
  exact JGe_Window31.selected17
#print axioms selected17
theorem parser17 : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes17)=ok (some record17) := by
  apply (AspisR1.ExtractedRecordByteCanonicality.fixed_success_iff bytes17 record17).mpr
  constructor
  · intro j
    fin_cases j <;> decide
  · rfl
#print axioms parser17
theorem field17 : FIn_Primitives.field (JFw_Frames.window 8007 2048) 17#usize=ok value17 :=
  JGo_TX2_FieldRead.source _ _ bytes17 record17
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    selected17 parser17
#print axioms field17
theorem native_parser17 : FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes17)=ok (some (FIo_Install.toE value17)) := by
  with_unfolding_all rfl
#print axioms native_parser17
theorem native_field17 : FIo_Native.weights.field (JFw_Frames.window 8007 2048) 17#usize=
    ok (FIo_Install.toE value17) :=
  JGo_TX2_MessageRead.native _ 17#usize 544#usize 18#usize 576#usize bytes17 _
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 17#usize 32#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 17#usize 1#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 18#usize 32#usize (by decide)))
    (JGo_TX2_MessageRead.range _ _ _ bytes17 (by decide)
      (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
      (by decide) selected17) native_parser17
#print axioms native_field17
theorem canonical17 : Port4C_QueryArithmetic.CanonE value17 := by
  change (1755312639<2147483647 ∧ 414966063<2147483647 ∧ 1075065169<2147483647 ∧ 1645423591<2147483647) ∧
    (271932602<2147483647 ∧ 294888196<2147483647 ∧ 1031140955<2147483647 ∧ 1176464510<2147483647)
  omega
#print axioms canonical17
def bytes18 : Array U8 32#usize := ⟨JGe_Window31.c18,by rfl⟩
def value18 : AspisR1Stage2.Stage2Finish.E := ⟨⟨⟨109647748#u32,201213140#u32⟩,⟨553884543#u32,1398416490#u32⟩⟩,⟨⟨156717614#u32,2092462383#u32⟩,⟨1147831875#u32,51980416#u32⟩⟩⟩
def record18 : AspisR1RecordParser.field.wide_exact.WideExact := ⟨⟨⟨109647748#u32,201213140#u32⟩,⟨553884543#u32,1398416490#u32⟩⟩,⟨⟨156717614#u32,2092462383#u32⟩,⟨1147831875#u32,51980416#u32⟩⟩⟩
theorem selected18 : ((JFw_Frames.window 8007 2048).val.drop (32*18)).take 32=bytes18.val := by
  rw [JGo_TX2_MessageRead.cell 18 (by decide)]
  exact JGe_Window31.selected18
#print axioms selected18
theorem parser18 : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes18)=ok (some record18) := by
  apply (AspisR1.ExtractedRecordByteCanonicality.fixed_success_iff bytes18 record18).mpr
  constructor
  · intro j
    fin_cases j <;> decide
  · rfl
#print axioms parser18
theorem field18 : FIn_Primitives.field (JFw_Frames.window 8007 2048) 18#usize=ok value18 :=
  JGo_TX2_FieldRead.source _ _ bytes18 record18
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    selected18 parser18
#print axioms field18
theorem native_parser18 : FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes18)=ok (some (FIo_Install.toE value18)) := by
  with_unfolding_all rfl
#print axioms native_parser18
theorem native_field18 : FIo_Native.weights.field (JFw_Frames.window 8007 2048) 18#usize=
    ok (FIo_Install.toE value18) :=
  JGo_TX2_MessageRead.native _ 18#usize 576#usize 19#usize 608#usize bytes18 _
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 18#usize 32#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 18#usize 1#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 19#usize 32#usize (by decide)))
    (JGo_TX2_MessageRead.range _ _ _ bytes18 (by decide)
      (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
      (by decide) selected18) native_parser18
#print axioms native_field18
theorem canonical18 : Port4C_QueryArithmetic.CanonE value18 := by
  change (109647748<2147483647 ∧ 201213140<2147483647 ∧ 553884543<2147483647 ∧ 1398416490<2147483647) ∧
    (156717614<2147483647 ∧ 2092462383<2147483647 ∧ 1147831875<2147483647 ∧ 51980416<2147483647)
  omega
#print axioms canonical18
def bytes19 : Array U8 32#usize := ⟨JGe_Window31.c19,by rfl⟩
def value19 : AspisR1Stage2.Stage2Finish.E := ⟨⟨⟨790106188#u32,711980126#u32⟩,⟨1345686379#u32,122984751#u32⟩⟩,⟨⟨1554095960#u32,2135203752#u32⟩,⟨165871690#u32,1642350721#u32⟩⟩⟩
def record19 : AspisR1RecordParser.field.wide_exact.WideExact := ⟨⟨⟨790106188#u32,711980126#u32⟩,⟨1345686379#u32,122984751#u32⟩⟩,⟨⟨1554095960#u32,2135203752#u32⟩,⟨165871690#u32,1642350721#u32⟩⟩⟩
theorem selected19 : ((JFw_Frames.window 8007 2048).val.drop (32*19)).take 32=bytes19.val := by
  rw [JGo_TX2_MessageRead.cell 19 (by decide)]
  exact JGe_Window31.selected19
#print axioms selected19
theorem parser19 : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes19)=ok (some record19) := by
  apply (AspisR1.ExtractedRecordByteCanonicality.fixed_success_iff bytes19 record19).mpr
  constructor
  · intro j
    fin_cases j <;> decide
  · rfl
#print axioms parser19
theorem field19 : FIn_Primitives.field (JFw_Frames.window 8007 2048) 19#usize=ok value19 :=
  JGo_TX2_FieldRead.source _ _ bytes19 record19
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    selected19 parser19
#print axioms field19
theorem native_parser19 : FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes19)=ok (some (FIo_Install.toE value19)) := by
  with_unfolding_all rfl
#print axioms native_parser19
theorem native_field19 : FIo_Native.weights.field (JFw_Frames.window 8007 2048) 19#usize=
    ok (FIo_Install.toE value19) :=
  JGo_TX2_MessageRead.native _ 19#usize 608#usize 20#usize 640#usize bytes19 _
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 19#usize 32#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 19#usize 1#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 20#usize 32#usize (by decide)))
    (JGo_TX2_MessageRead.range _ _ _ bytes19 (by decide)
      (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
      (by decide) selected19) native_parser19
#print axioms native_field19
theorem canonical19 : Port4C_QueryArithmetic.CanonE value19 := by
  change (790106188<2147483647 ∧ 711980126<2147483647 ∧ 1345686379<2147483647 ∧ 122984751<2147483647) ∧
    (1554095960<2147483647 ∧ 2135203752<2147483647 ∧ 165871690<2147483647 ∧ 1642350721<2147483647)
  omega
#print axioms canonical19
def bytes20 : Array U8 32#usize := ⟨JGe_Window31.c20,by rfl⟩
def value20 : AspisR1Stage2.Stage2Finish.E := ⟨⟨⟨570697237#u32,146763607#u32⟩,⟨174606966#u32,685074848#u32⟩⟩,⟨⟨1050027617#u32,143494836#u32⟩,⟨1292108628#u32,1089579126#u32⟩⟩⟩
def record20 : AspisR1RecordParser.field.wide_exact.WideExact := ⟨⟨⟨570697237#u32,146763607#u32⟩,⟨174606966#u32,685074848#u32⟩⟩,⟨⟨1050027617#u32,143494836#u32⟩,⟨1292108628#u32,1089579126#u32⟩⟩⟩
theorem selected20 : ((JFw_Frames.window 8007 2048).val.drop (32*20)).take 32=bytes20.val := by
  rw [JGo_TX2_MessageRead.cell 20 (by decide)]
  exact JGe_Window31.selected20
#print axioms selected20
theorem parser20 : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes20)=ok (some record20) := by
  apply (AspisR1.ExtractedRecordByteCanonicality.fixed_success_iff bytes20 record20).mpr
  constructor
  · intro j
    fin_cases j <;> decide
  · rfl
#print axioms parser20
theorem field20 : FIn_Primitives.field (JFw_Frames.window 8007 2048) 20#usize=ok value20 :=
  JGo_TX2_FieldRead.source _ _ bytes20 record20
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    selected20 parser20
#print axioms field20
theorem native_parser20 : FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes20)=ok (some (FIo_Install.toE value20)) := by
  with_unfolding_all rfl
#print axioms native_parser20
theorem native_field20 : FIo_Native.weights.field (JFw_Frames.window 8007 2048) 20#usize=
    ok (FIo_Install.toE value20) :=
  JGo_TX2_MessageRead.native _ 20#usize 640#usize 21#usize 672#usize bytes20 _
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 20#usize 32#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 20#usize 1#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 21#usize 32#usize (by decide)))
    (JGo_TX2_MessageRead.range _ _ _ bytes20 (by decide)
      (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
      (by decide) selected20) native_parser20
#print axioms native_field20
theorem canonical20 : Port4C_QueryArithmetic.CanonE value20 := by
  change (570697237<2147483647 ∧ 146763607<2147483647 ∧ 174606966<2147483647 ∧ 685074848<2147483647) ∧
    (1050027617<2147483647 ∧ 143494836<2147483647 ∧ 1292108628<2147483647 ∧ 1089579126<2147483647)
  omega
#print axioms canonical20
def bytes21 : Array U8 32#usize := ⟨JGe_Window31.c21,by rfl⟩
def value21 : AspisR1Stage2.Stage2Finish.E := ⟨⟨⟨330464783#u32,1628494784#u32⟩,⟨1504715279#u32,840227872#u32⟩⟩,⟨⟨122933294#u32,2023303258#u32⟩,⟨1253537412#u32,346603045#u32⟩⟩⟩
def record21 : AspisR1RecordParser.field.wide_exact.WideExact := ⟨⟨⟨330464783#u32,1628494784#u32⟩,⟨1504715279#u32,840227872#u32⟩⟩,⟨⟨122933294#u32,2023303258#u32⟩,⟨1253537412#u32,346603045#u32⟩⟩⟩
theorem selected21 : ((JFw_Frames.window 8007 2048).val.drop (32*21)).take 32=bytes21.val := by
  rw [JGo_TX2_MessageRead.cell 21 (by decide)]
  exact JGe_Window31.selected21
#print axioms selected21
theorem parser21 : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes21)=ok (some record21) := by
  apply (AspisR1.ExtractedRecordByteCanonicality.fixed_success_iff bytes21 record21).mpr
  constructor
  · intro j
    fin_cases j <;> decide
  · rfl
#print axioms parser21
theorem field21 : FIn_Primitives.field (JFw_Frames.window 8007 2048) 21#usize=ok value21 :=
  JGo_TX2_FieldRead.source _ _ bytes21 record21
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    selected21 parser21
#print axioms field21
theorem native_parser21 : FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes21)=ok (some (FIo_Install.toE value21)) := by
  with_unfolding_all rfl
#print axioms native_parser21
theorem native_field21 : FIo_Native.weights.field (JFw_Frames.window 8007 2048) 21#usize=
    ok (FIo_Install.toE value21) :=
  JGo_TX2_MessageRead.native _ 21#usize 672#usize 22#usize 704#usize bytes21 _
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 21#usize 32#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 21#usize 1#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 22#usize 32#usize (by decide)))
    (JGo_TX2_MessageRead.range _ _ _ bytes21 (by decide)
      (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
      (by decide) selected21) native_parser21
#print axioms native_field21
theorem canonical21 : Port4C_QueryArithmetic.CanonE value21 := by
  change (330464783<2147483647 ∧ 1628494784<2147483647 ∧ 1504715279<2147483647 ∧ 840227872<2147483647) ∧
    (122933294<2147483647 ∧ 2023303258<2147483647 ∧ 1253537412<2147483647 ∧ 346603045<2147483647)
  omega
#print axioms canonical21
def bytes22 : Array U8 32#usize := ⟨JGe_Window31.c22,by rfl⟩
def value22 : AspisR1Stage2.Stage2Finish.E := ⟨⟨⟨629995855#u32,1517635747#u32⟩,⟨2010751207#u32,677992755#u32⟩⟩,⟨⟨778803902#u32,396967976#u32⟩,⟨1988266906#u32,1551872716#u32⟩⟩⟩
def record22 : AspisR1RecordParser.field.wide_exact.WideExact := ⟨⟨⟨629995855#u32,1517635747#u32⟩,⟨2010751207#u32,677992755#u32⟩⟩,⟨⟨778803902#u32,396967976#u32⟩,⟨1988266906#u32,1551872716#u32⟩⟩⟩
theorem selected22 : ((JFw_Frames.window 8007 2048).val.drop (32*22)).take 32=bytes22.val := by
  rw [JGo_TX2_MessageRead.cell 22 (by decide)]
  exact JGe_Window31.selected22
#print axioms selected22
theorem parser22 : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes22)=ok (some record22) := by
  apply (AspisR1.ExtractedRecordByteCanonicality.fixed_success_iff bytes22 record22).mpr
  constructor
  · intro j
    fin_cases j <;> decide
  · rfl
#print axioms parser22
theorem field22 : FIn_Primitives.field (JFw_Frames.window 8007 2048) 22#usize=ok value22 :=
  JGo_TX2_FieldRead.source _ _ bytes22 record22
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    selected22 parser22
#print axioms field22
theorem native_parser22 : FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes22)=ok (some (FIo_Install.toE value22)) := by
  with_unfolding_all rfl
#print axioms native_parser22
theorem native_field22 : FIo_Native.weights.field (JFw_Frames.window 8007 2048) 22#usize=
    ok (FIo_Install.toE value22) :=
  JGo_TX2_MessageRead.native _ 22#usize 704#usize 23#usize 736#usize bytes22 _
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 22#usize 32#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 22#usize 1#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 23#usize 32#usize (by decide)))
    (JGo_TX2_MessageRead.range _ _ _ bytes22 (by decide)
      (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
      (by decide) selected22) native_parser22
#print axioms native_field22
theorem canonical22 : Port4C_QueryArithmetic.CanonE value22 := by
  change (629995855<2147483647 ∧ 1517635747<2147483647 ∧ 2010751207<2147483647 ∧ 677992755<2147483647) ∧
    (778803902<2147483647 ∧ 396967976<2147483647 ∧ 1988266906<2147483647 ∧ 1551872716<2147483647)
  omega
#print axioms canonical22
def bytes23 : Array U8 32#usize := ⟨JGe_Window31.c23,by rfl⟩
def value23 : AspisR1Stage2.Stage2Finish.E := ⟨⟨⟨1207827015#u32,311444072#u32⟩,⟨1731366999#u32,1690228129#u32⟩⟩,⟨⟨1255544679#u32,479585198#u32⟩,⟨672088416#u32,1688079279#u32⟩⟩⟩
def record23 : AspisR1RecordParser.field.wide_exact.WideExact := ⟨⟨⟨1207827015#u32,311444072#u32⟩,⟨1731366999#u32,1690228129#u32⟩⟩,⟨⟨1255544679#u32,479585198#u32⟩,⟨672088416#u32,1688079279#u32⟩⟩⟩
theorem selected23 : ((JFw_Frames.window 8007 2048).val.drop (32*23)).take 32=bytes23.val := by
  rw [JGo_TX2_MessageRead.cell 23 (by decide)]
  exact JGe_Window31.selected23
#print axioms selected23
theorem parser23 : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes23)=ok (some record23) := by
  apply (AspisR1.ExtractedRecordByteCanonicality.fixed_success_iff bytes23 record23).mpr
  constructor
  · intro j
    fin_cases j <;> decide
  · rfl
#print axioms parser23
theorem field23 : FIn_Primitives.field (JFw_Frames.window 8007 2048) 23#usize=ok value23 :=
  JGo_TX2_FieldRead.source _ _ bytes23 record23
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    selected23 parser23
#print axioms field23
theorem native_parser23 : FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes23)=ok (some (FIo_Install.toE value23)) := by
  with_unfolding_all rfl
#print axioms native_parser23
theorem native_field23 : FIo_Native.weights.field (JFw_Frames.window 8007 2048) 23#usize=
    ok (FIo_Install.toE value23) :=
  JGo_TX2_MessageRead.native _ 23#usize 736#usize 24#usize 768#usize bytes23 _
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 23#usize 32#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 23#usize 1#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 24#usize 32#usize (by decide)))
    (JGo_TX2_MessageRead.range _ _ _ bytes23 (by decide)
      (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
      (by decide) selected23) native_parser23
#print axioms native_field23
theorem canonical23 : Port4C_QueryArithmetic.CanonE value23 := by
  change (1207827015<2147483647 ∧ 311444072<2147483647 ∧ 1731366999<2147483647 ∧ 1690228129<2147483647) ∧
    (1255544679<2147483647 ∧ 479585198<2147483647 ∧ 672088416<2147483647 ∧ 1688079279<2147483647)
  omega
#print axioms canonical23
end AspisR1.JGo_TX2_Message16
end
