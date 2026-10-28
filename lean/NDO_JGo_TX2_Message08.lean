import NDO_JGo_TX2_MessageRead
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGo_TX2_Message08
open Aeneas Aeneas.Std Result
attribute [local irreducible] JFx_NativeBytes.proof JFw_Frames.window
def bytes08 : Array U8 32#usize := ⟨JGe_Window31.c08,by rfl⟩
def value08 : AspisR1Stage2.Stage2Finish.E := ⟨⟨⟨198201272#u32,1496991052#u32⟩,⟨1641891296#u32,1526002988#u32⟩⟩,⟨⟨1352034305#u32,117324299#u32⟩,⟨115158021#u32,2099103899#u32⟩⟩⟩
def record08 : AspisR1RecordParser.field.wide_exact.WideExact := ⟨⟨⟨198201272#u32,1496991052#u32⟩,⟨1641891296#u32,1526002988#u32⟩⟩,⟨⟨1352034305#u32,117324299#u32⟩,⟨115158021#u32,2099103899#u32⟩⟩⟩
theorem selected08 : ((JFw_Frames.window 8007 2048).val.drop (32*8)).take 32=bytes08.val := by
  rw [JGo_TX2_MessageRead.cell 8 (by decide)]
  exact JGe_Window31.selected08
#print axioms selected08
theorem parser08 : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes08)=ok (some record08) := by
  apply (AspisR1.ExtractedRecordByteCanonicality.fixed_success_iff bytes08 record08).mpr
  constructor
  · intro j
    fin_cases j <;> decide
  · rfl
#print axioms parser08
theorem field08 : FIn_Primitives.field (JFw_Frames.window 8007 2048) 8#usize=ok value08 :=
  JGo_TX2_FieldRead.source _ _ bytes08 record08
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    selected08 parser08
#print axioms field08
theorem native_parser08 : FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes08)=ok (some (FIo_Install.toE value08)) := by
  with_unfolding_all rfl
#print axioms native_parser08
theorem native_field08 : FIo_Native.weights.field (JFw_Frames.window 8007 2048) 8#usize=
    ok (FIo_Install.toE value08) :=
  JGo_TX2_MessageRead.native _ 8#usize 256#usize 9#usize 288#usize bytes08 _
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 8#usize 32#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 8#usize 1#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 9#usize 32#usize (by decide)))
    (JGo_TX2_MessageRead.range _ _ _ bytes08 (by decide)
      (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
      (by decide) selected08) native_parser08
#print axioms native_field08
theorem canonical08 : Port4C_QueryArithmetic.CanonE value08 := by
  change (198201272<2147483647 ∧ 1496991052<2147483647 ∧ 1641891296<2147483647 ∧ 1526002988<2147483647) ∧
    (1352034305<2147483647 ∧ 117324299<2147483647 ∧ 115158021<2147483647 ∧ 2099103899<2147483647)
  omega
#print axioms canonical08
def bytes09 : Array U8 32#usize := ⟨JGe_Window31.c09,by rfl⟩
def value09 : AspisR1Stage2.Stage2Finish.E := ⟨⟨⟨464896655#u32,1537979725#u32⟩,⟨1087173625#u32,1705544685#u32⟩⟩,⟨⟨1061895777#u32,726300725#u32⟩,⟨337170773#u32,662128948#u32⟩⟩⟩
def record09 : AspisR1RecordParser.field.wide_exact.WideExact := ⟨⟨⟨464896655#u32,1537979725#u32⟩,⟨1087173625#u32,1705544685#u32⟩⟩,⟨⟨1061895777#u32,726300725#u32⟩,⟨337170773#u32,662128948#u32⟩⟩⟩
theorem selected09 : ((JFw_Frames.window 8007 2048).val.drop (32*9)).take 32=bytes09.val := by
  rw [JGo_TX2_MessageRead.cell 9 (by decide)]
  exact JGe_Window31.selected09
#print axioms selected09
theorem parser09 : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes09)=ok (some record09) := by
  apply (AspisR1.ExtractedRecordByteCanonicality.fixed_success_iff bytes09 record09).mpr
  constructor
  · intro j
    fin_cases j <;> decide
  · rfl
#print axioms parser09
theorem field09 : FIn_Primitives.field (JFw_Frames.window 8007 2048) 9#usize=ok value09 :=
  JGo_TX2_FieldRead.source _ _ bytes09 record09
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    selected09 parser09
#print axioms field09
theorem native_parser09 : FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes09)=ok (some (FIo_Install.toE value09)) := by
  with_unfolding_all rfl
#print axioms native_parser09
theorem native_field09 : FIo_Native.weights.field (JFw_Frames.window 8007 2048) 9#usize=
    ok (FIo_Install.toE value09) :=
  JGo_TX2_MessageRead.native _ 9#usize 288#usize 10#usize 320#usize bytes09 _
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 9#usize 32#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 9#usize 1#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 10#usize 32#usize (by decide)))
    (JGo_TX2_MessageRead.range _ _ _ bytes09 (by decide)
      (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
      (by decide) selected09) native_parser09
#print axioms native_field09
theorem canonical09 : Port4C_QueryArithmetic.CanonE value09 := by
  change (464896655<2147483647 ∧ 1537979725<2147483647 ∧ 1087173625<2147483647 ∧ 1705544685<2147483647) ∧
    (1061895777<2147483647 ∧ 726300725<2147483647 ∧ 337170773<2147483647 ∧ 662128948<2147483647)
  omega
#print axioms canonical09
def bytes10 : Array U8 32#usize := ⟨JGe_Window31.c10,by rfl⟩
def value10 : AspisR1Stage2.Stage2Finish.E := ⟨⟨⟨17480762#u32,1764034418#u32⟩,⟨332009738#u32,227816618#u32⟩⟩,⟨⟨1083145966#u32,356651741#u32⟩,⟨571490475#u32,72273651#u32⟩⟩⟩
def record10 : AspisR1RecordParser.field.wide_exact.WideExact := ⟨⟨⟨17480762#u32,1764034418#u32⟩,⟨332009738#u32,227816618#u32⟩⟩,⟨⟨1083145966#u32,356651741#u32⟩,⟨571490475#u32,72273651#u32⟩⟩⟩
theorem selected10 : ((JFw_Frames.window 8007 2048).val.drop (32*10)).take 32=bytes10.val := by
  rw [JGo_TX2_MessageRead.cell 10 (by decide)]
  exact JGe_Window31.selected10
#print axioms selected10
theorem parser10 : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes10)=ok (some record10) := by
  apply (AspisR1.ExtractedRecordByteCanonicality.fixed_success_iff bytes10 record10).mpr
  constructor
  · intro j
    fin_cases j <;> decide
  · rfl
#print axioms parser10
theorem field10 : FIn_Primitives.field (JFw_Frames.window 8007 2048) 10#usize=ok value10 :=
  JGo_TX2_FieldRead.source _ _ bytes10 record10
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    selected10 parser10
#print axioms field10
theorem native_parser10 : FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes10)=ok (some (FIo_Install.toE value10)) := by
  with_unfolding_all rfl
#print axioms native_parser10
theorem native_field10 : FIo_Native.weights.field (JFw_Frames.window 8007 2048) 10#usize=
    ok (FIo_Install.toE value10) :=
  JGo_TX2_MessageRead.native _ 10#usize 320#usize 11#usize 352#usize bytes10 _
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 10#usize 32#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 10#usize 1#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 11#usize 32#usize (by decide)))
    (JGo_TX2_MessageRead.range _ _ _ bytes10 (by decide)
      (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
      (by decide) selected10) native_parser10
#print axioms native_field10
theorem canonical10 : Port4C_QueryArithmetic.CanonE value10 := by
  change (17480762<2147483647 ∧ 1764034418<2147483647 ∧ 332009738<2147483647 ∧ 227816618<2147483647) ∧
    (1083145966<2147483647 ∧ 356651741<2147483647 ∧ 571490475<2147483647 ∧ 72273651<2147483647)
  omega
#print axioms canonical10
def bytes11 : Array U8 32#usize := ⟨JGe_Window31.c11,by rfl⟩
def value11 : AspisR1Stage2.Stage2Finish.E := ⟨⟨⟨2059882055#u32,1616102549#u32⟩,⟨970582289#u32,272406826#u32⟩⟩,⟨⟨468272396#u32,760509300#u32⟩,⟨1576770494#u32,1375161446#u32⟩⟩⟩
def record11 : AspisR1RecordParser.field.wide_exact.WideExact := ⟨⟨⟨2059882055#u32,1616102549#u32⟩,⟨970582289#u32,272406826#u32⟩⟩,⟨⟨468272396#u32,760509300#u32⟩,⟨1576770494#u32,1375161446#u32⟩⟩⟩
theorem selected11 : ((JFw_Frames.window 8007 2048).val.drop (32*11)).take 32=bytes11.val := by
  rw [JGo_TX2_MessageRead.cell 11 (by decide)]
  exact JGe_Window31.selected11
#print axioms selected11
theorem parser11 : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes11)=ok (some record11) := by
  apply (AspisR1.ExtractedRecordByteCanonicality.fixed_success_iff bytes11 record11).mpr
  constructor
  · intro j
    fin_cases j <;> decide
  · rfl
#print axioms parser11
theorem field11 : FIn_Primitives.field (JFw_Frames.window 8007 2048) 11#usize=ok value11 :=
  JGo_TX2_FieldRead.source _ _ bytes11 record11
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    selected11 parser11
#print axioms field11
theorem native_parser11 : FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes11)=ok (some (FIo_Install.toE value11)) := by
  with_unfolding_all rfl
#print axioms native_parser11
theorem native_field11 : FIo_Native.weights.field (JFw_Frames.window 8007 2048) 11#usize=
    ok (FIo_Install.toE value11) :=
  JGo_TX2_MessageRead.native _ 11#usize 352#usize 12#usize 384#usize bytes11 _
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 11#usize 32#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 11#usize 1#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 12#usize 32#usize (by decide)))
    (JGo_TX2_MessageRead.range _ _ _ bytes11 (by decide)
      (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
      (by decide) selected11) native_parser11
#print axioms native_field11
theorem canonical11 : Port4C_QueryArithmetic.CanonE value11 := by
  change (2059882055<2147483647 ∧ 1616102549<2147483647 ∧ 970582289<2147483647 ∧ 272406826<2147483647) ∧
    (468272396<2147483647 ∧ 760509300<2147483647 ∧ 1576770494<2147483647 ∧ 1375161446<2147483647)
  omega
#print axioms canonical11
def bytes12 : Array U8 32#usize := ⟨JGe_Window31.c12,by rfl⟩
def value12 : AspisR1Stage2.Stage2Finish.E := ⟨⟨⟨355967590#u32,1590147608#u32⟩,⟨320616902#u32,1451536764#u32⟩⟩,⟨⟨1433344255#u32,1950661462#u32⟩,⟨1188273208#u32,1053938940#u32⟩⟩⟩
def record12 : AspisR1RecordParser.field.wide_exact.WideExact := ⟨⟨⟨355967590#u32,1590147608#u32⟩,⟨320616902#u32,1451536764#u32⟩⟩,⟨⟨1433344255#u32,1950661462#u32⟩,⟨1188273208#u32,1053938940#u32⟩⟩⟩
theorem selected12 : ((JFw_Frames.window 8007 2048).val.drop (32*12)).take 32=bytes12.val := by
  rw [JGo_TX2_MessageRead.cell 12 (by decide)]
  exact JGe_Window31.selected12
#print axioms selected12
theorem parser12 : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes12)=ok (some record12) := by
  apply (AspisR1.ExtractedRecordByteCanonicality.fixed_success_iff bytes12 record12).mpr
  constructor
  · intro j
    fin_cases j <;> decide
  · rfl
#print axioms parser12
theorem field12 : FIn_Primitives.field (JFw_Frames.window 8007 2048) 12#usize=ok value12 :=
  JGo_TX2_FieldRead.source _ _ bytes12 record12
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    selected12 parser12
#print axioms field12
theorem native_parser12 : FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes12)=ok (some (FIo_Install.toE value12)) := by
  with_unfolding_all rfl
#print axioms native_parser12
theorem native_field12 : FIo_Native.weights.field (JFw_Frames.window 8007 2048) 12#usize=
    ok (FIo_Install.toE value12) :=
  JGo_TX2_MessageRead.native _ 12#usize 384#usize 13#usize 416#usize bytes12 _
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 12#usize 32#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 12#usize 1#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 13#usize 32#usize (by decide)))
    (JGo_TX2_MessageRead.range _ _ _ bytes12 (by decide)
      (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
      (by decide) selected12) native_parser12
#print axioms native_field12
theorem canonical12 : Port4C_QueryArithmetic.CanonE value12 := by
  change (355967590<2147483647 ∧ 1590147608<2147483647 ∧ 320616902<2147483647 ∧ 1451536764<2147483647) ∧
    (1433344255<2147483647 ∧ 1950661462<2147483647 ∧ 1188273208<2147483647 ∧ 1053938940<2147483647)
  omega
#print axioms canonical12
def bytes13 : Array U8 32#usize := ⟨JGe_Window31.c13,by rfl⟩
def value13 : AspisR1Stage2.Stage2Finish.E := ⟨⟨⟨1964573553#u32,1423788458#u32⟩,⟨1954866546#u32,1671451930#u32⟩⟩,⟨⟨1509574454#u32,1937116904#u32⟩,⟨538093460#u32,619898564#u32⟩⟩⟩
def record13 : AspisR1RecordParser.field.wide_exact.WideExact := ⟨⟨⟨1964573553#u32,1423788458#u32⟩,⟨1954866546#u32,1671451930#u32⟩⟩,⟨⟨1509574454#u32,1937116904#u32⟩,⟨538093460#u32,619898564#u32⟩⟩⟩
theorem selected13 : ((JFw_Frames.window 8007 2048).val.drop (32*13)).take 32=bytes13.val := by
  rw [JGo_TX2_MessageRead.cell 13 (by decide)]
  exact JGe_Window31.selected13
#print axioms selected13
theorem parser13 : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes13)=ok (some record13) := by
  apply (AspisR1.ExtractedRecordByteCanonicality.fixed_success_iff bytes13 record13).mpr
  constructor
  · intro j
    fin_cases j <;> decide
  · rfl
#print axioms parser13
theorem field13 : FIn_Primitives.field (JFw_Frames.window 8007 2048) 13#usize=ok value13 :=
  JGo_TX2_FieldRead.source _ _ bytes13 record13
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    selected13 parser13
#print axioms field13
theorem native_parser13 : FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes13)=ok (some (FIo_Install.toE value13)) := by
  with_unfolding_all rfl
#print axioms native_parser13
theorem native_field13 : FIo_Native.weights.field (JFw_Frames.window 8007 2048) 13#usize=
    ok (FIo_Install.toE value13) :=
  JGo_TX2_MessageRead.native _ 13#usize 416#usize 14#usize 448#usize bytes13 _
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 13#usize 32#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 13#usize 1#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 14#usize 32#usize (by decide)))
    (JGo_TX2_MessageRead.range _ _ _ bytes13 (by decide)
      (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
      (by decide) selected13) native_parser13
#print axioms native_field13
theorem canonical13 : Port4C_QueryArithmetic.CanonE value13 := by
  change (1964573553<2147483647 ∧ 1423788458<2147483647 ∧ 1954866546<2147483647 ∧ 1671451930<2147483647) ∧
    (1509574454<2147483647 ∧ 1937116904<2147483647 ∧ 538093460<2147483647 ∧ 619898564<2147483647)
  omega
#print axioms canonical13
def bytes14 : Array U8 32#usize := ⟨JGe_Window31.c14,by rfl⟩
def value14 : AspisR1Stage2.Stage2Finish.E := ⟨⟨⟨1169891952#u32,1891655272#u32⟩,⟨2065417536#u32,489341837#u32⟩⟩,⟨⟨951661286#u32,917774746#u32⟩,⟨463604155#u32,1591078459#u32⟩⟩⟩
def record14 : AspisR1RecordParser.field.wide_exact.WideExact := ⟨⟨⟨1169891952#u32,1891655272#u32⟩,⟨2065417536#u32,489341837#u32⟩⟩,⟨⟨951661286#u32,917774746#u32⟩,⟨463604155#u32,1591078459#u32⟩⟩⟩
theorem selected14 : ((JFw_Frames.window 8007 2048).val.drop (32*14)).take 32=bytes14.val := by
  rw [JGo_TX2_MessageRead.cell 14 (by decide)]
  exact JGe_Window31.selected14
#print axioms selected14
theorem parser14 : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes14)=ok (some record14) := by
  apply (AspisR1.ExtractedRecordByteCanonicality.fixed_success_iff bytes14 record14).mpr
  constructor
  · intro j
    fin_cases j <;> decide
  · rfl
#print axioms parser14
theorem field14 : FIn_Primitives.field (JFw_Frames.window 8007 2048) 14#usize=ok value14 :=
  JGo_TX2_FieldRead.source _ _ bytes14 record14
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    selected14 parser14
#print axioms field14
theorem native_parser14 : FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes14)=ok (some (FIo_Install.toE value14)) := by
  with_unfolding_all rfl
#print axioms native_parser14
theorem native_field14 : FIo_Native.weights.field (JFw_Frames.window 8007 2048) 14#usize=
    ok (FIo_Install.toE value14) :=
  JGo_TX2_MessageRead.native _ 14#usize 448#usize 15#usize 480#usize bytes14 _
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 14#usize 32#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 14#usize 1#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 15#usize 32#usize (by decide)))
    (JGo_TX2_MessageRead.range _ _ _ bytes14 (by decide)
      (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
      (by decide) selected14) native_parser14
#print axioms native_field14
theorem canonical14 : Port4C_QueryArithmetic.CanonE value14 := by
  change (1169891952<2147483647 ∧ 1891655272<2147483647 ∧ 2065417536<2147483647 ∧ 489341837<2147483647) ∧
    (951661286<2147483647 ∧ 917774746<2147483647 ∧ 463604155<2147483647 ∧ 1591078459<2147483647)
  omega
#print axioms canonical14
def bytes15 : Array U8 32#usize := ⟨JGe_Window31.c15,by rfl⟩
def value15 : AspisR1Stage2.Stage2Finish.E := ⟨⟨⟨1459601597#u32,364594365#u32⟩,⟨1665193839#u32,1680674526#u32⟩⟩,⟨⟨861167088#u32,1700712768#u32⟩,⟨101529880#u32,2013169173#u32⟩⟩⟩
def record15 : AspisR1RecordParser.field.wide_exact.WideExact := ⟨⟨⟨1459601597#u32,364594365#u32⟩,⟨1665193839#u32,1680674526#u32⟩⟩,⟨⟨861167088#u32,1700712768#u32⟩,⟨101529880#u32,2013169173#u32⟩⟩⟩
theorem selected15 : ((JFw_Frames.window 8007 2048).val.drop (32*15)).take 32=bytes15.val := by
  rw [JGo_TX2_MessageRead.cell 15 (by decide)]
  exact JGe_Window31.selected15
#print axioms selected15
theorem parser15 : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes15)=ok (some record15) := by
  apply (AspisR1.ExtractedRecordByteCanonicality.fixed_success_iff bytes15 record15).mpr
  constructor
  · intro j
    fin_cases j <;> decide
  · rfl
#print axioms parser15
theorem field15 : FIn_Primitives.field (JFw_Frames.window 8007 2048) 15#usize=ok value15 :=
  JGo_TX2_FieldRead.source _ _ bytes15 record15
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    selected15 parser15
#print axioms field15
theorem native_parser15 : FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes15)=ok (some (FIo_Install.toE value15)) := by
  with_unfolding_all rfl
#print axioms native_parser15
theorem native_field15 : FIo_Native.weights.field (JFw_Frames.window 8007 2048) 15#usize=
    ok (FIo_Install.toE value15) :=
  JGo_TX2_MessageRead.native _ 15#usize 480#usize 16#usize 512#usize bytes15 _
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 15#usize 32#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 15#usize 1#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 16#usize 32#usize (by decide)))
    (JGo_TX2_MessageRead.range _ _ _ bytes15 (by decide)
      (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
      (by decide) selected15) native_parser15
#print axioms native_field15
theorem canonical15 : Port4C_QueryArithmetic.CanonE value15 := by
  change (1459601597<2147483647 ∧ 364594365<2147483647 ∧ 1665193839<2147483647 ∧ 1680674526<2147483647) ∧
    (861167088<2147483647 ∧ 1700712768<2147483647 ∧ 101529880<2147483647 ∧ 2013169173<2147483647)
  omega
#print axioms canonical15
end AspisR1.JGo_TX2_Message08
end
