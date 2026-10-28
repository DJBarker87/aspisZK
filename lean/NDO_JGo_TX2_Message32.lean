import NDO_JGo_TX2_MessageRead
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGo_TX2_Message32
open Aeneas Aeneas.Std Result
attribute [local irreducible] JFx_NativeBytes.proof JFw_Frames.window
def bytes32 : Array U8 32#usize := ⟨JGe_Window31.c32,by rfl⟩
def value32 : AspisR1Stage2.Stage2Finish.E := ⟨⟨⟨1343359687#u32,1460376740#u32⟩,⟨566623144#u32,19950988#u32⟩⟩,⟨⟨570807964#u32,736313575#u32⟩,⟨1196970012#u32,1739767892#u32⟩⟩⟩
def record32 : AspisR1RecordParser.field.wide_exact.WideExact := ⟨⟨⟨1343359687#u32,1460376740#u32⟩,⟨566623144#u32,19950988#u32⟩⟩,⟨⟨570807964#u32,736313575#u32⟩,⟨1196970012#u32,1739767892#u32⟩⟩⟩
theorem selected32 : ((JFw_Frames.window 8007 2048).val.drop (32*32)).take 32=bytes32.val := by
  rw [JGo_TX2_MessageRead.cell 32 (by decide)]
  exact JGe_Window31.selected32
#print axioms selected32
theorem parser32 : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes32)=ok (some record32) := by
  apply (AspisR1.ExtractedRecordByteCanonicality.fixed_success_iff bytes32 record32).mpr
  constructor
  · intro j
    fin_cases j <;> decide
  · rfl
#print axioms parser32
theorem field32 : FIn_Primitives.field (JFw_Frames.window 8007 2048) 32#usize=ok value32 :=
  JGo_TX2_FieldRead.source _ _ bytes32 record32
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    selected32 parser32
#print axioms field32
theorem native_parser32 : FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes32)=ok (some (FIo_Install.toE value32)) := by
  with_unfolding_all rfl
#print axioms native_parser32
theorem native_field32 : FIo_Native.weights.field (JFw_Frames.window 8007 2048) 32#usize=
    ok (FIo_Install.toE value32) :=
  JGo_TX2_MessageRead.native _ 32#usize 1024#usize 33#usize 1056#usize bytes32 _
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 32#usize 32#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 32#usize 1#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 33#usize 32#usize (by decide)))
    (JGo_TX2_MessageRead.range _ _ _ bytes32 (by decide)
      (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
      (by decide) selected32) native_parser32
#print axioms native_field32
theorem canonical32 : Port4C_QueryArithmetic.CanonE value32 := by
  change (1343359687<2147483647 ∧ 1460376740<2147483647 ∧ 566623144<2147483647 ∧ 19950988<2147483647) ∧
    (570807964<2147483647 ∧ 736313575<2147483647 ∧ 1196970012<2147483647 ∧ 1739767892<2147483647)
  omega
#print axioms canonical32
def bytes33 : Array U8 32#usize := ⟨JGe_Window31.c33,by rfl⟩
def value33 : AspisR1Stage2.Stage2Finish.E := ⟨⟨⟨1239414400#u32,1450183684#u32⟩,⟨1306321059#u32,1249137014#u32⟩⟩,⟨⟨174553357#u32,1566886620#u32⟩,⟨1144183827#u32,654731156#u32⟩⟩⟩
def record33 : AspisR1RecordParser.field.wide_exact.WideExact := ⟨⟨⟨1239414400#u32,1450183684#u32⟩,⟨1306321059#u32,1249137014#u32⟩⟩,⟨⟨174553357#u32,1566886620#u32⟩,⟨1144183827#u32,654731156#u32⟩⟩⟩
theorem selected33 : ((JFw_Frames.window 8007 2048).val.drop (32*33)).take 32=bytes33.val := by
  rw [JGo_TX2_MessageRead.cell 33 (by decide)]
  exact JGe_Window31.selected33
#print axioms selected33
theorem parser33 : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes33)=ok (some record33) := by
  apply (AspisR1.ExtractedRecordByteCanonicality.fixed_success_iff bytes33 record33).mpr
  constructor
  · intro j
    fin_cases j <;> decide
  · rfl
#print axioms parser33
theorem field33 : FIn_Primitives.field (JFw_Frames.window 8007 2048) 33#usize=ok value33 :=
  JGo_TX2_FieldRead.source _ _ bytes33 record33
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    selected33 parser33
#print axioms field33
theorem native_parser33 : FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes33)=ok (some (FIo_Install.toE value33)) := by
  with_unfolding_all rfl
#print axioms native_parser33
theorem native_field33 : FIo_Native.weights.field (JFw_Frames.window 8007 2048) 33#usize=
    ok (FIo_Install.toE value33) :=
  JGo_TX2_MessageRead.native _ 33#usize 1056#usize 34#usize 1088#usize bytes33 _
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 33#usize 32#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 33#usize 1#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 34#usize 32#usize (by decide)))
    (JGo_TX2_MessageRead.range _ _ _ bytes33 (by decide)
      (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
      (by decide) selected33) native_parser33
#print axioms native_field33
theorem canonical33 : Port4C_QueryArithmetic.CanonE value33 := by
  change (1239414400<2147483647 ∧ 1450183684<2147483647 ∧ 1306321059<2147483647 ∧ 1249137014<2147483647) ∧
    (174553357<2147483647 ∧ 1566886620<2147483647 ∧ 1144183827<2147483647 ∧ 654731156<2147483647)
  omega
#print axioms canonical33
def bytes34 : Array U8 32#usize := ⟨JGe_Window31.c34,by rfl⟩
def value34 : AspisR1Stage2.Stage2Finish.E := ⟨⟨⟨127090766#u32,660309850#u32⟩,⟨740823635#u32,1993332303#u32⟩⟩,⟨⟨573853959#u32,1503389365#u32⟩,⟨1794350121#u32,900802407#u32⟩⟩⟩
def record34 : AspisR1RecordParser.field.wide_exact.WideExact := ⟨⟨⟨127090766#u32,660309850#u32⟩,⟨740823635#u32,1993332303#u32⟩⟩,⟨⟨573853959#u32,1503389365#u32⟩,⟨1794350121#u32,900802407#u32⟩⟩⟩
theorem selected34 : ((JFw_Frames.window 8007 2048).val.drop (32*34)).take 32=bytes34.val := by
  rw [JGo_TX2_MessageRead.cell 34 (by decide)]
  exact JGe_Window31.selected34
#print axioms selected34
theorem parser34 : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes34)=ok (some record34) := by
  apply (AspisR1.ExtractedRecordByteCanonicality.fixed_success_iff bytes34 record34).mpr
  constructor
  · intro j
    fin_cases j <;> decide
  · rfl
#print axioms parser34
theorem field34 : FIn_Primitives.field (JFw_Frames.window 8007 2048) 34#usize=ok value34 :=
  JGo_TX2_FieldRead.source _ _ bytes34 record34
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    selected34 parser34
#print axioms field34
theorem native_parser34 : FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes34)=ok (some (FIo_Install.toE value34)) := by
  with_unfolding_all rfl
#print axioms native_parser34
theorem native_field34 : FIo_Native.weights.field (JFw_Frames.window 8007 2048) 34#usize=
    ok (FIo_Install.toE value34) :=
  JGo_TX2_MessageRead.native _ 34#usize 1088#usize 35#usize 1120#usize bytes34 _
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 34#usize 32#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 34#usize 1#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 35#usize 32#usize (by decide)))
    (JGo_TX2_MessageRead.range _ _ _ bytes34 (by decide)
      (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
      (by decide) selected34) native_parser34
#print axioms native_field34
theorem canonical34 : Port4C_QueryArithmetic.CanonE value34 := by
  change (127090766<2147483647 ∧ 660309850<2147483647 ∧ 740823635<2147483647 ∧ 1993332303<2147483647) ∧
    (573853959<2147483647 ∧ 1503389365<2147483647 ∧ 1794350121<2147483647 ∧ 900802407<2147483647)
  omega
#print axioms canonical34
def bytes35 : Array U8 32#usize := ⟨JGe_Window31.c35,by rfl⟩
def value35 : AspisR1Stage2.Stage2Finish.E := ⟨⟨⟨311863527#u32,889281535#u32⟩,⟨150948436#u32,2032656089#u32⟩⟩,⟨⟨1584789128#u32,799879033#u32⟩,⟨80390186#u32,1847437787#u32⟩⟩⟩
def record35 : AspisR1RecordParser.field.wide_exact.WideExact := ⟨⟨⟨311863527#u32,889281535#u32⟩,⟨150948436#u32,2032656089#u32⟩⟩,⟨⟨1584789128#u32,799879033#u32⟩,⟨80390186#u32,1847437787#u32⟩⟩⟩
theorem selected35 : ((JFw_Frames.window 8007 2048).val.drop (32*35)).take 32=bytes35.val := by
  rw [JGo_TX2_MessageRead.cell 35 (by decide)]
  exact JGe_Window31.selected35
#print axioms selected35
theorem parser35 : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes35)=ok (some record35) := by
  apply (AspisR1.ExtractedRecordByteCanonicality.fixed_success_iff bytes35 record35).mpr
  constructor
  · intro j
    fin_cases j <;> decide
  · rfl
#print axioms parser35
theorem field35 : FIn_Primitives.field (JFw_Frames.window 8007 2048) 35#usize=ok value35 :=
  JGo_TX2_FieldRead.source _ _ bytes35 record35
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    selected35 parser35
#print axioms field35
theorem native_parser35 : FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes35)=ok (some (FIo_Install.toE value35)) := by
  with_unfolding_all rfl
#print axioms native_parser35
theorem native_field35 : FIo_Native.weights.field (JFw_Frames.window 8007 2048) 35#usize=
    ok (FIo_Install.toE value35) :=
  JGo_TX2_MessageRead.native _ 35#usize 1120#usize 36#usize 1152#usize bytes35 _
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 35#usize 32#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 35#usize 1#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 36#usize 32#usize (by decide)))
    (JGo_TX2_MessageRead.range _ _ _ bytes35 (by decide)
      (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
      (by decide) selected35) native_parser35
#print axioms native_field35
theorem canonical35 : Port4C_QueryArithmetic.CanonE value35 := by
  change (311863527<2147483647 ∧ 889281535<2147483647 ∧ 150948436<2147483647 ∧ 2032656089<2147483647) ∧
    (1584789128<2147483647 ∧ 799879033<2147483647 ∧ 80390186<2147483647 ∧ 1847437787<2147483647)
  omega
#print axioms canonical35
def bytes36 : Array U8 32#usize := ⟨JGe_Window31.c36,by rfl⟩
def value36 : AspisR1Stage2.Stage2Finish.E := ⟨⟨⟨985706752#u32,459525093#u32⟩,⟨1966131644#u32,317968496#u32⟩⟩,⟨⟨104069276#u32,1333020198#u32⟩,⟨417483720#u32,1118033548#u32⟩⟩⟩
def record36 : AspisR1RecordParser.field.wide_exact.WideExact := ⟨⟨⟨985706752#u32,459525093#u32⟩,⟨1966131644#u32,317968496#u32⟩⟩,⟨⟨104069276#u32,1333020198#u32⟩,⟨417483720#u32,1118033548#u32⟩⟩⟩
theorem selected36 : ((JFw_Frames.window 8007 2048).val.drop (32*36)).take 32=bytes36.val := by
  rw [JGo_TX2_MessageRead.cell 36 (by decide)]
  exact JGe_Window31.selected36
#print axioms selected36
theorem parser36 : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes36)=ok (some record36) := by
  apply (AspisR1.ExtractedRecordByteCanonicality.fixed_success_iff bytes36 record36).mpr
  constructor
  · intro j
    fin_cases j <;> decide
  · rfl
#print axioms parser36
theorem field36 : FIn_Primitives.field (JFw_Frames.window 8007 2048) 36#usize=ok value36 :=
  JGo_TX2_FieldRead.source _ _ bytes36 record36
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    selected36 parser36
#print axioms field36
theorem native_parser36 : FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes36)=ok (some (FIo_Install.toE value36)) := by
  with_unfolding_all rfl
#print axioms native_parser36
theorem native_field36 : FIo_Native.weights.field (JFw_Frames.window 8007 2048) 36#usize=
    ok (FIo_Install.toE value36) :=
  JGo_TX2_MessageRead.native _ 36#usize 1152#usize 37#usize 1184#usize bytes36 _
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 36#usize 32#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 36#usize 1#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 37#usize 32#usize (by decide)))
    (JGo_TX2_MessageRead.range _ _ _ bytes36 (by decide)
      (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
      (by decide) selected36) native_parser36
#print axioms native_field36
theorem canonical36 : Port4C_QueryArithmetic.CanonE value36 := by
  change (985706752<2147483647 ∧ 459525093<2147483647 ∧ 1966131644<2147483647 ∧ 317968496<2147483647) ∧
    (104069276<2147483647 ∧ 1333020198<2147483647 ∧ 417483720<2147483647 ∧ 1118033548<2147483647)
  omega
#print axioms canonical36
def bytes37 : Array U8 32#usize := ⟨JGe_Window31.c37,by rfl⟩
def value37 : AspisR1Stage2.Stage2Finish.E := ⟨⟨⟨30768685#u32,1509750673#u32⟩,⟨1552480815#u32,2099497618#u32⟩⟩,⟨⟨207828955#u32,177450495#u32⟩,⟨1877030952#u32,2142717732#u32⟩⟩⟩
def record37 : AspisR1RecordParser.field.wide_exact.WideExact := ⟨⟨⟨30768685#u32,1509750673#u32⟩,⟨1552480815#u32,2099497618#u32⟩⟩,⟨⟨207828955#u32,177450495#u32⟩,⟨1877030952#u32,2142717732#u32⟩⟩⟩
theorem selected37 : ((JFw_Frames.window 8007 2048).val.drop (32*37)).take 32=bytes37.val := by
  rw [JGo_TX2_MessageRead.cell 37 (by decide)]
  exact JGe_Window31.selected37
#print axioms selected37
theorem parser37 : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes37)=ok (some record37) := by
  apply (AspisR1.ExtractedRecordByteCanonicality.fixed_success_iff bytes37 record37).mpr
  constructor
  · intro j
    fin_cases j <;> decide
  · rfl
#print axioms parser37
theorem field37 : FIn_Primitives.field (JFw_Frames.window 8007 2048) 37#usize=ok value37 :=
  JGo_TX2_FieldRead.source _ _ bytes37 record37
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    selected37 parser37
#print axioms field37
theorem native_parser37 : FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes37)=ok (some (FIo_Install.toE value37)) := by
  with_unfolding_all rfl
#print axioms native_parser37
theorem native_field37 : FIo_Native.weights.field (JFw_Frames.window 8007 2048) 37#usize=
    ok (FIo_Install.toE value37) :=
  JGo_TX2_MessageRead.native _ 37#usize 1184#usize 38#usize 1216#usize bytes37 _
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 37#usize 32#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 37#usize 1#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 38#usize 32#usize (by decide)))
    (JGo_TX2_MessageRead.range _ _ _ bytes37 (by decide)
      (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
      (by decide) selected37) native_parser37
#print axioms native_field37
theorem canonical37 : Port4C_QueryArithmetic.CanonE value37 := by
  change (30768685<2147483647 ∧ 1509750673<2147483647 ∧ 1552480815<2147483647 ∧ 2099497618<2147483647) ∧
    (207828955<2147483647 ∧ 177450495<2147483647 ∧ 1877030952<2147483647 ∧ 2142717732<2147483647)
  omega
#print axioms canonical37
def bytes38 : Array U8 32#usize := ⟨JGe_Window31.c38,by rfl⟩
def value38 : AspisR1Stage2.Stage2Finish.E := ⟨⟨⟨124828473#u32,36646635#u32⟩,⟨309751808#u32,1824390508#u32⟩⟩,⟨⟨1532442837#u32,1104974718#u32⟩,⟨1548679918#u32,735925287#u32⟩⟩⟩
def record38 : AspisR1RecordParser.field.wide_exact.WideExact := ⟨⟨⟨124828473#u32,36646635#u32⟩,⟨309751808#u32,1824390508#u32⟩⟩,⟨⟨1532442837#u32,1104974718#u32⟩,⟨1548679918#u32,735925287#u32⟩⟩⟩
theorem selected38 : ((JFw_Frames.window 8007 2048).val.drop (32*38)).take 32=bytes38.val := by
  rw [JGo_TX2_MessageRead.cell 38 (by decide)]
  exact JGe_Window31.selected38
#print axioms selected38
theorem parser38 : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes38)=ok (some record38) := by
  apply (AspisR1.ExtractedRecordByteCanonicality.fixed_success_iff bytes38 record38).mpr
  constructor
  · intro j
    fin_cases j <;> decide
  · rfl
#print axioms parser38
theorem field38 : FIn_Primitives.field (JFw_Frames.window 8007 2048) 38#usize=ok value38 :=
  JGo_TX2_FieldRead.source _ _ bytes38 record38
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    selected38 parser38
#print axioms field38
theorem native_parser38 : FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes38)=ok (some (FIo_Install.toE value38)) := by
  with_unfolding_all rfl
#print axioms native_parser38
theorem native_field38 : FIo_Native.weights.field (JFw_Frames.window 8007 2048) 38#usize=
    ok (FIo_Install.toE value38) :=
  JGo_TX2_MessageRead.native _ 38#usize 1216#usize 39#usize 1248#usize bytes38 _
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 38#usize 32#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 38#usize 1#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 39#usize 32#usize (by decide)))
    (JGo_TX2_MessageRead.range _ _ _ bytes38 (by decide)
      (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
      (by decide) selected38) native_parser38
#print axioms native_field38
theorem canonical38 : Port4C_QueryArithmetic.CanonE value38 := by
  change (124828473<2147483647 ∧ 36646635<2147483647 ∧ 309751808<2147483647 ∧ 1824390508<2147483647) ∧
    (1532442837<2147483647 ∧ 1104974718<2147483647 ∧ 1548679918<2147483647 ∧ 735925287<2147483647)
  omega
#print axioms canonical38
def bytes39 : Array U8 32#usize := ⟨JGe_Window31.c39,by rfl⟩
def value39 : AspisR1Stage2.Stage2Finish.E := ⟨⟨⟨1156865602#u32,1769322940#u32⟩,⟨1463491584#u32,692969160#u32⟩⟩,⟨⟨698816780#u32,1347977684#u32⟩,⟨733440319#u32,1362220699#u32⟩⟩⟩
def record39 : AspisR1RecordParser.field.wide_exact.WideExact := ⟨⟨⟨1156865602#u32,1769322940#u32⟩,⟨1463491584#u32,692969160#u32⟩⟩,⟨⟨698816780#u32,1347977684#u32⟩,⟨733440319#u32,1362220699#u32⟩⟩⟩
theorem selected39 : ((JFw_Frames.window 8007 2048).val.drop (32*39)).take 32=bytes39.val := by
  rw [JGo_TX2_MessageRead.cell 39 (by decide)]
  exact JGe_Window31.selected39
#print axioms selected39
theorem parser39 : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes39)=ok (some record39) := by
  apply (AspisR1.ExtractedRecordByteCanonicality.fixed_success_iff bytes39 record39).mpr
  constructor
  · intro j
    fin_cases j <;> decide
  · rfl
#print axioms parser39
theorem field39 : FIn_Primitives.field (JFw_Frames.window 8007 2048) 39#usize=ok value39 :=
  JGo_TX2_FieldRead.source _ _ bytes39 record39
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    selected39 parser39
#print axioms field39
theorem native_parser39 : FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes39)=ok (some (FIo_Install.toE value39)) := by
  with_unfolding_all rfl
#print axioms native_parser39
theorem native_field39 : FIo_Native.weights.field (JFw_Frames.window 8007 2048) 39#usize=
    ok (FIo_Install.toE value39) :=
  JGo_TX2_MessageRead.native _ 39#usize 1248#usize 40#usize 1280#usize bytes39 _
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 39#usize 32#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 39#usize 1#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 40#usize 32#usize (by decide)))
    (JGo_TX2_MessageRead.range _ _ _ bytes39 (by decide)
      (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
      (by decide) selected39) native_parser39
#print axioms native_field39
theorem canonical39 : Port4C_QueryArithmetic.CanonE value39 := by
  change (1156865602<2147483647 ∧ 1769322940<2147483647 ∧ 1463491584<2147483647 ∧ 692969160<2147483647) ∧
    (698816780<2147483647 ∧ 1347977684<2147483647 ∧ 733440319<2147483647 ∧ 1362220699<2147483647)
  omega
#print axioms canonical39
end AspisR1.JGo_TX2_Message32
end
