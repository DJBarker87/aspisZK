import NDO_JGo_TX2_MessageRead
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGo_TX2_Message24
open Aeneas Aeneas.Std Result
attribute [local irreducible] JFx_NativeBytes.proof JFw_Frames.window
def bytes24 : Array U8 32#usize := ⟨JGe_Window31.c24,by rfl⟩
def value24 : AspisR1Stage2.Stage2Finish.E := ⟨⟨⟨1311481370#u32,2069613618#u32⟩,⟨2042627375#u32,1592104934#u32⟩⟩,⟨⟨1185733575#u32,1806665834#u32⟩,⟨408474239#u32,2044148807#u32⟩⟩⟩
def record24 : AspisR1RecordParser.field.wide_exact.WideExact := ⟨⟨⟨1311481370#u32,2069613618#u32⟩,⟨2042627375#u32,1592104934#u32⟩⟩,⟨⟨1185733575#u32,1806665834#u32⟩,⟨408474239#u32,2044148807#u32⟩⟩⟩
theorem selected24 : ((JFw_Frames.window 8007 2048).val.drop (32*24)).take 32=bytes24.val := by
  rw [JGo_TX2_MessageRead.cell 24 (by decide)]
  exact JGe_Window31.selected24
#print axioms selected24
theorem parser24 : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes24)=ok (some record24) := by
  apply (AspisR1.ExtractedRecordByteCanonicality.fixed_success_iff bytes24 record24).mpr
  constructor
  · intro j
    fin_cases j <;> decide
  · rfl
#print axioms parser24
theorem field24 : FIn_Primitives.field (JFw_Frames.window 8007 2048) 24#usize=ok value24 :=
  JGo_TX2_FieldRead.source _ _ bytes24 record24
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    selected24 parser24
#print axioms field24
theorem native_parser24 : FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes24)=ok (some (FIo_Install.toE value24)) := by
  with_unfolding_all rfl
#print axioms native_parser24
theorem native_field24 : FIo_Native.weights.field (JFw_Frames.window 8007 2048) 24#usize=
    ok (FIo_Install.toE value24) :=
  JGo_TX2_MessageRead.native _ 24#usize 768#usize 25#usize 800#usize bytes24 _
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 24#usize 32#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 24#usize 1#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 25#usize 32#usize (by decide)))
    (JGo_TX2_MessageRead.range _ _ _ bytes24 (by decide)
      (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
      (by decide) selected24) native_parser24
#print axioms native_field24
theorem canonical24 : Port4C_QueryArithmetic.CanonE value24 := by
  change (1311481370<2147483647 ∧ 2069613618<2147483647 ∧ 2042627375<2147483647 ∧ 1592104934<2147483647) ∧
    (1185733575<2147483647 ∧ 1806665834<2147483647 ∧ 408474239<2147483647 ∧ 2044148807<2147483647)
  omega
#print axioms canonical24
def bytes25 : Array U8 32#usize := ⟨JGe_Window31.c25,by rfl⟩
def value25 : AspisR1Stage2.Stage2Finish.E := ⟨⟨⟨829798172#u32,1854489486#u32⟩,⟨99165051#u32,2062627392#u32⟩⟩,⟨⟨1674253890#u32,720311883#u32⟩,⟨768955156#u32,744659665#u32⟩⟩⟩
def record25 : AspisR1RecordParser.field.wide_exact.WideExact := ⟨⟨⟨829798172#u32,1854489486#u32⟩,⟨99165051#u32,2062627392#u32⟩⟩,⟨⟨1674253890#u32,720311883#u32⟩,⟨768955156#u32,744659665#u32⟩⟩⟩
theorem selected25 : ((JFw_Frames.window 8007 2048).val.drop (32*25)).take 32=bytes25.val := by
  rw [JGo_TX2_MessageRead.cell 25 (by decide)]
  exact JGe_Window31.selected25
#print axioms selected25
theorem parser25 : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes25)=ok (some record25) := by
  apply (AspisR1.ExtractedRecordByteCanonicality.fixed_success_iff bytes25 record25).mpr
  constructor
  · intro j
    fin_cases j <;> decide
  · rfl
#print axioms parser25
theorem field25 : FIn_Primitives.field (JFw_Frames.window 8007 2048) 25#usize=ok value25 :=
  JGo_TX2_FieldRead.source _ _ bytes25 record25
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    selected25 parser25
#print axioms field25
theorem native_parser25 : FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes25)=ok (some (FIo_Install.toE value25)) := by
  with_unfolding_all rfl
#print axioms native_parser25
theorem native_field25 : FIo_Native.weights.field (JFw_Frames.window 8007 2048) 25#usize=
    ok (FIo_Install.toE value25) :=
  JGo_TX2_MessageRead.native _ 25#usize 800#usize 26#usize 832#usize bytes25 _
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 25#usize 32#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 25#usize 1#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 26#usize 32#usize (by decide)))
    (JGo_TX2_MessageRead.range _ _ _ bytes25 (by decide)
      (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
      (by decide) selected25) native_parser25
#print axioms native_field25
theorem canonical25 : Port4C_QueryArithmetic.CanonE value25 := by
  change (829798172<2147483647 ∧ 1854489486<2147483647 ∧ 99165051<2147483647 ∧ 2062627392<2147483647) ∧
    (1674253890<2147483647 ∧ 720311883<2147483647 ∧ 768955156<2147483647 ∧ 744659665<2147483647)
  omega
#print axioms canonical25
def bytes26 : Array U8 32#usize := ⟨JGe_Window31.c26,by rfl⟩
def value26 : AspisR1Stage2.Stage2Finish.E := ⟨⟨⟨1908082517#u32,1848488323#u32⟩,⟨1474986388#u32,1512390276#u32⟩⟩,⟨⟨586078147#u32,1397523931#u32⟩,⟨301215486#u32,1862092698#u32⟩⟩⟩
def record26 : AspisR1RecordParser.field.wide_exact.WideExact := ⟨⟨⟨1908082517#u32,1848488323#u32⟩,⟨1474986388#u32,1512390276#u32⟩⟩,⟨⟨586078147#u32,1397523931#u32⟩,⟨301215486#u32,1862092698#u32⟩⟩⟩
theorem selected26 : ((JFw_Frames.window 8007 2048).val.drop (32*26)).take 32=bytes26.val := by
  rw [JGo_TX2_MessageRead.cell 26 (by decide)]
  exact JGe_Window31.selected26
#print axioms selected26
theorem parser26 : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes26)=ok (some record26) := by
  apply (AspisR1.ExtractedRecordByteCanonicality.fixed_success_iff bytes26 record26).mpr
  constructor
  · intro j
    fin_cases j <;> decide
  · rfl
#print axioms parser26
theorem field26 : FIn_Primitives.field (JFw_Frames.window 8007 2048) 26#usize=ok value26 :=
  JGo_TX2_FieldRead.source _ _ bytes26 record26
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    selected26 parser26
#print axioms field26
theorem native_parser26 : FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes26)=ok (some (FIo_Install.toE value26)) := by
  with_unfolding_all rfl
#print axioms native_parser26
theorem native_field26 : FIo_Native.weights.field (JFw_Frames.window 8007 2048) 26#usize=
    ok (FIo_Install.toE value26) :=
  JGo_TX2_MessageRead.native _ 26#usize 832#usize 27#usize 864#usize bytes26 _
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 26#usize 32#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 26#usize 1#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 27#usize 32#usize (by decide)))
    (JGo_TX2_MessageRead.range _ _ _ bytes26 (by decide)
      (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
      (by decide) selected26) native_parser26
#print axioms native_field26
theorem canonical26 : Port4C_QueryArithmetic.CanonE value26 := by
  change (1908082517<2147483647 ∧ 1848488323<2147483647 ∧ 1474986388<2147483647 ∧ 1512390276<2147483647) ∧
    (586078147<2147483647 ∧ 1397523931<2147483647 ∧ 301215486<2147483647 ∧ 1862092698<2147483647)
  omega
#print axioms canonical26
def bytes27 : Array U8 32#usize := ⟨JGe_Window31.c27,by rfl⟩
def value27 : AspisR1Stage2.Stage2Finish.E := ⟨⟨⟨1681396350#u32,827859169#u32⟩,⟨1316920386#u32,1732499072#u32⟩⟩,⟨⟨403038793#u32,1797150296#u32⟩,⟨1862674455#u32,627327186#u32⟩⟩⟩
def record27 : AspisR1RecordParser.field.wide_exact.WideExact := ⟨⟨⟨1681396350#u32,827859169#u32⟩,⟨1316920386#u32,1732499072#u32⟩⟩,⟨⟨403038793#u32,1797150296#u32⟩,⟨1862674455#u32,627327186#u32⟩⟩⟩
theorem selected27 : ((JFw_Frames.window 8007 2048).val.drop (32*27)).take 32=bytes27.val := by
  rw [JGo_TX2_MessageRead.cell 27 (by decide)]
  exact JGe_Window31.selected27
#print axioms selected27
theorem parser27 : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes27)=ok (some record27) := by
  apply (AspisR1.ExtractedRecordByteCanonicality.fixed_success_iff bytes27 record27).mpr
  constructor
  · intro j
    fin_cases j <;> decide
  · rfl
#print axioms parser27
theorem field27 : FIn_Primitives.field (JFw_Frames.window 8007 2048) 27#usize=ok value27 :=
  JGo_TX2_FieldRead.source _ _ bytes27 record27
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    selected27 parser27
#print axioms field27
theorem native_parser27 : FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes27)=ok (some (FIo_Install.toE value27)) := by
  with_unfolding_all rfl
#print axioms native_parser27
theorem native_field27 : FIo_Native.weights.field (JFw_Frames.window 8007 2048) 27#usize=
    ok (FIo_Install.toE value27) :=
  JGo_TX2_MessageRead.native _ 27#usize 864#usize 28#usize 896#usize bytes27 _
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 27#usize 32#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 27#usize 1#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 28#usize 32#usize (by decide)))
    (JGo_TX2_MessageRead.range _ _ _ bytes27 (by decide)
      (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
      (by decide) selected27) native_parser27
#print axioms native_field27
theorem canonical27 : Port4C_QueryArithmetic.CanonE value27 := by
  change (1681396350<2147483647 ∧ 827859169<2147483647 ∧ 1316920386<2147483647 ∧ 1732499072<2147483647) ∧
    (403038793<2147483647 ∧ 1797150296<2147483647 ∧ 1862674455<2147483647 ∧ 627327186<2147483647)
  omega
#print axioms canonical27
def bytes28 : Array U8 32#usize := ⟨JGe_Window31.c28,by rfl⟩
def value28 : AspisR1Stage2.Stage2Finish.E := ⟨⟨⟨791864332#u32,375725047#u32⟩,⟨841265838#u32,1242624264#u32⟩⟩,⟨⟨1320093200#u32,1597531999#u32⟩,⟨1136595503#u32,1408868563#u32⟩⟩⟩
def record28 : AspisR1RecordParser.field.wide_exact.WideExact := ⟨⟨⟨791864332#u32,375725047#u32⟩,⟨841265838#u32,1242624264#u32⟩⟩,⟨⟨1320093200#u32,1597531999#u32⟩,⟨1136595503#u32,1408868563#u32⟩⟩⟩
theorem selected28 : ((JFw_Frames.window 8007 2048).val.drop (32*28)).take 32=bytes28.val := by
  rw [JGo_TX2_MessageRead.cell 28 (by decide)]
  exact JGe_Window31.selected28
#print axioms selected28
theorem parser28 : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes28)=ok (some record28) := by
  apply (AspisR1.ExtractedRecordByteCanonicality.fixed_success_iff bytes28 record28).mpr
  constructor
  · intro j
    fin_cases j <;> decide
  · rfl
#print axioms parser28
theorem field28 : FIn_Primitives.field (JFw_Frames.window 8007 2048) 28#usize=ok value28 :=
  JGo_TX2_FieldRead.source _ _ bytes28 record28
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    selected28 parser28
#print axioms field28
theorem native_parser28 : FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes28)=ok (some (FIo_Install.toE value28)) := by
  with_unfolding_all rfl
#print axioms native_parser28
theorem native_field28 : FIo_Native.weights.field (JFw_Frames.window 8007 2048) 28#usize=
    ok (FIo_Install.toE value28) :=
  JGo_TX2_MessageRead.native _ 28#usize 896#usize 29#usize 928#usize bytes28 _
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 28#usize 32#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 28#usize 1#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 29#usize 32#usize (by decide)))
    (JGo_TX2_MessageRead.range _ _ _ bytes28 (by decide)
      (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
      (by decide) selected28) native_parser28
#print axioms native_field28
theorem canonical28 : Port4C_QueryArithmetic.CanonE value28 := by
  change (791864332<2147483647 ∧ 375725047<2147483647 ∧ 841265838<2147483647 ∧ 1242624264<2147483647) ∧
    (1320093200<2147483647 ∧ 1597531999<2147483647 ∧ 1136595503<2147483647 ∧ 1408868563<2147483647)
  omega
#print axioms canonical28
def bytes29 : Array U8 32#usize := ⟨JGe_Window31.c29,by rfl⟩
def value29 : AspisR1Stage2.Stage2Finish.E := ⟨⟨⟨1679134396#u32,1089644797#u32⟩,⟨803851468#u32,964621769#u32⟩⟩,⟨⟨999523784#u32,1659864748#u32⟩,⟨232970902#u32,1137111336#u32⟩⟩⟩
def record29 : AspisR1RecordParser.field.wide_exact.WideExact := ⟨⟨⟨1679134396#u32,1089644797#u32⟩,⟨803851468#u32,964621769#u32⟩⟩,⟨⟨999523784#u32,1659864748#u32⟩,⟨232970902#u32,1137111336#u32⟩⟩⟩
theorem selected29 : ((JFw_Frames.window 8007 2048).val.drop (32*29)).take 32=bytes29.val := by
  rw [JGo_TX2_MessageRead.cell 29 (by decide)]
  exact JGe_Window31.selected29
#print axioms selected29
theorem parser29 : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes29)=ok (some record29) := by
  apply (AspisR1.ExtractedRecordByteCanonicality.fixed_success_iff bytes29 record29).mpr
  constructor
  · intro j
    fin_cases j <;> decide
  · rfl
#print axioms parser29
theorem field29 : FIn_Primitives.field (JFw_Frames.window 8007 2048) 29#usize=ok value29 :=
  JGo_TX2_FieldRead.source _ _ bytes29 record29
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    selected29 parser29
#print axioms field29
theorem native_parser29 : FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes29)=ok (some (FIo_Install.toE value29)) := by
  with_unfolding_all rfl
#print axioms native_parser29
theorem native_field29 : FIo_Native.weights.field (JFw_Frames.window 8007 2048) 29#usize=
    ok (FIo_Install.toE value29) :=
  JGo_TX2_MessageRead.native _ 29#usize 928#usize 30#usize 960#usize bytes29 _
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 29#usize 32#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 29#usize 1#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 30#usize 32#usize (by decide)))
    (JGo_TX2_MessageRead.range _ _ _ bytes29 (by decide)
      (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
      (by decide) selected29) native_parser29
#print axioms native_field29
theorem canonical29 : Port4C_QueryArithmetic.CanonE value29 := by
  change (1679134396<2147483647 ∧ 1089644797<2147483647 ∧ 803851468<2147483647 ∧ 964621769<2147483647) ∧
    (999523784<2147483647 ∧ 1659864748<2147483647 ∧ 232970902<2147483647 ∧ 1137111336<2147483647)
  omega
#print axioms canonical29
def bytes30 : Array U8 32#usize := ⟨JGe_Window31.c30,by rfl⟩
def value30 : AspisR1Stage2.Stage2Finish.E := ⟨⟨⟨1312581398#u32,719143028#u32⟩,⟨1840127480#u32,1897291607#u32⟩⟩,⟨⟨1670146241#u32,1096788354#u32⟩,⟨1159164740#u32,1768575889#u32⟩⟩⟩
def record30 : AspisR1RecordParser.field.wide_exact.WideExact := ⟨⟨⟨1312581398#u32,719143028#u32⟩,⟨1840127480#u32,1897291607#u32⟩⟩,⟨⟨1670146241#u32,1096788354#u32⟩,⟨1159164740#u32,1768575889#u32⟩⟩⟩
theorem selected30 : ((JFw_Frames.window 8007 2048).val.drop (32*30)).take 32=bytes30.val := by
  rw [JGo_TX2_MessageRead.cell 30 (by decide)]
  exact JGe_Window31.selected30
#print axioms selected30
theorem parser30 : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes30)=ok (some record30) := by
  apply (AspisR1.ExtractedRecordByteCanonicality.fixed_success_iff bytes30 record30).mpr
  constructor
  · intro j
    fin_cases j <;> decide
  · rfl
#print axioms parser30
theorem field30 : FIn_Primitives.field (JFw_Frames.window 8007 2048) 30#usize=ok value30 :=
  JGo_TX2_FieldRead.source _ _ bytes30 record30
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    selected30 parser30
#print axioms field30
theorem native_parser30 : FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes30)=ok (some (FIo_Install.toE value30)) := by
  with_unfolding_all rfl
#print axioms native_parser30
theorem native_field30 : FIo_Native.weights.field (JFw_Frames.window 8007 2048) 30#usize=
    ok (FIo_Install.toE value30) :=
  JGo_TX2_MessageRead.native _ 30#usize 960#usize 31#usize 992#usize bytes30 _
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 30#usize 32#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 30#usize 1#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 31#usize 32#usize (by decide)))
    (JGo_TX2_MessageRead.range _ _ _ bytes30 (by decide)
      (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
      (by decide) selected30) native_parser30
#print axioms native_field30
theorem canonical30 : Port4C_QueryArithmetic.CanonE value30 := by
  change (1312581398<2147483647 ∧ 719143028<2147483647 ∧ 1840127480<2147483647 ∧ 1897291607<2147483647) ∧
    (1670146241<2147483647 ∧ 1096788354<2147483647 ∧ 1159164740<2147483647 ∧ 1768575889<2147483647)
  omega
#print axioms canonical30
def bytes31 : Array U8 32#usize := ⟨JGe_Window31.c31,by rfl⟩
def value31 : AspisR1Stage2.Stage2Finish.E := ⟨⟨⟨1890268993#u32,1935214336#u32⟩,⟨554301836#u32,1581243861#u32⟩⟩,⟨⟨643028429#u32,668789405#u32⟩,⟨48764784#u32,86299928#u32⟩⟩⟩
def record31 : AspisR1RecordParser.field.wide_exact.WideExact := ⟨⟨⟨1890268993#u32,1935214336#u32⟩,⟨554301836#u32,1581243861#u32⟩⟩,⟨⟨643028429#u32,668789405#u32⟩,⟨48764784#u32,86299928#u32⟩⟩⟩
theorem selected31 : ((JFw_Frames.window 8007 2048).val.drop (32*31)).take 32=bytes31.val := by
  rw [JGo_TX2_MessageRead.cell 31 (by decide)]
  exact JGe_Window31.selected31
#print axioms selected31
theorem parser31 : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes31)=ok (some record31) := by
  apply (AspisR1.ExtractedRecordByteCanonicality.fixed_success_iff bytes31 record31).mpr
  constructor
  · intro j
    fin_cases j <;> decide
  · rfl
#print axioms parser31
theorem field31 : FIn_Primitives.field (JFw_Frames.window 8007 2048) 31#usize=ok value31 :=
  JGo_TX2_FieldRead.source _ _ bytes31 record31
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    selected31 parser31
#print axioms field31
theorem native_parser31 : FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes31)=ok (some (FIo_Install.toE value31)) := by
  with_unfolding_all rfl
#print axioms native_parser31
theorem native_field31 : FIo_Native.weights.field (JFw_Frames.window 8007 2048) 31#usize=
    ok (FIo_Install.toE value31) :=
  JGo_TX2_MessageRead.native _ 31#usize 992#usize 32#usize 1024#usize bytes31 _
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 31#usize 32#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 31#usize 1#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 32#usize 32#usize (by decide)))
    (JGo_TX2_MessageRead.range _ _ _ bytes31 (by decide)
      (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
      (by decide) selected31) native_parser31
#print axioms native_field31
theorem canonical31 : Port4C_QueryArithmetic.CanonE value31 := by
  change (1890268993<2147483647 ∧ 1935214336<2147483647 ∧ 554301836<2147483647 ∧ 1581243861<2147483647) ∧
    (643028429<2147483647 ∧ 668789405<2147483647 ∧ 48764784<2147483647 ∧ 86299928<2147483647)
  omega
#print axioms canonical31
end AspisR1.JGo_TX2_Message24
end
