import NDO_JGo_TX2_MessageRead
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGo_TX2_Message56
open Aeneas Aeneas.Std Result
attribute [local irreducible] JFx_NativeBytes.proof JFw_Frames.window
def bytes56 : Array U8 32#usize := ⟨JGe_Window31.c56,by rfl⟩
def value56 : AspisR1Stage2.Stage2Finish.E := ⟨⟨⟨2084010296#u32,1290230917#u32⟩,⟨206654067#u32,1690543565#u32⟩⟩,⟨⟨921079385#u32,1347410075#u32⟩,⟨1478055333#u32,88543573#u32⟩⟩⟩
def record56 : AspisR1RecordParser.field.wide_exact.WideExact := ⟨⟨⟨2084010296#u32,1290230917#u32⟩,⟨206654067#u32,1690543565#u32⟩⟩,⟨⟨921079385#u32,1347410075#u32⟩,⟨1478055333#u32,88543573#u32⟩⟩⟩
theorem selected56 : ((JFw_Frames.window 8007 2048).val.drop (32*56)).take 32=bytes56.val := by
  rw [JGo_TX2_MessageRead.cell 56 (by decide)]
  exact JGe_Window31.selected56
#print axioms selected56
theorem parser56 : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes56)=ok (some record56) := by
  apply (AspisR1.ExtractedRecordByteCanonicality.fixed_success_iff bytes56 record56).mpr
  constructor
  · intro j
    fin_cases j <;> decide
  · rfl
#print axioms parser56
theorem field56 : FIn_Primitives.field (JFw_Frames.window 8007 2048) 56#usize=ok value56 :=
  JGo_TX2_FieldRead.source _ _ bytes56 record56
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    selected56 parser56
#print axioms field56
theorem native_parser56 : FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes56)=ok (some (FIo_Install.toE value56)) := by
  with_unfolding_all rfl
#print axioms native_parser56
theorem native_field56 : FIo_Native.weights.field (JFw_Frames.window 8007 2048) 56#usize=
    ok (FIo_Install.toE value56) :=
  JGo_TX2_MessageRead.native _ 56#usize 1792#usize 57#usize 1824#usize bytes56 _
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 56#usize 32#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 56#usize 1#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 57#usize 32#usize (by decide)))
    (JGo_TX2_MessageRead.range _ _ _ bytes56 (by decide)
      (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
      (by decide) selected56) native_parser56
#print axioms native_field56
theorem canonical56 : Port4C_QueryArithmetic.CanonE value56 := by
  change (2084010296<2147483647 ∧ 1290230917<2147483647 ∧ 206654067<2147483647 ∧ 1690543565<2147483647) ∧
    (921079385<2147483647 ∧ 1347410075<2147483647 ∧ 1478055333<2147483647 ∧ 88543573<2147483647)
  omega
#print axioms canonical56
def bytes57 : Array U8 32#usize := ⟨JGe_Window31.c57,by rfl⟩
def value57 : AspisR1Stage2.Stage2Finish.E := ⟨⟨⟨1065623334#u32,835265977#u32⟩,⟨1026621096#u32,474049857#u32⟩⟩,⟨⟨1172145980#u32,554081829#u32⟩,⟨46013768#u32,1524611267#u32⟩⟩⟩
def record57 : AspisR1RecordParser.field.wide_exact.WideExact := ⟨⟨⟨1065623334#u32,835265977#u32⟩,⟨1026621096#u32,474049857#u32⟩⟩,⟨⟨1172145980#u32,554081829#u32⟩,⟨46013768#u32,1524611267#u32⟩⟩⟩
theorem selected57 : ((JFw_Frames.window 8007 2048).val.drop (32*57)).take 32=bytes57.val := by
  rw [JGo_TX2_MessageRead.cell 57 (by decide)]
  exact JGe_Window31.selected57
#print axioms selected57
theorem parser57 : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes57)=ok (some record57) := by
  apply (AspisR1.ExtractedRecordByteCanonicality.fixed_success_iff bytes57 record57).mpr
  constructor
  · intro j
    fin_cases j <;> decide
  · rfl
#print axioms parser57
theorem field57 : FIn_Primitives.field (JFw_Frames.window 8007 2048) 57#usize=ok value57 :=
  JGo_TX2_FieldRead.source _ _ bytes57 record57
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    selected57 parser57
#print axioms field57
theorem native_parser57 : FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes57)=ok (some (FIo_Install.toE value57)) := by
  with_unfolding_all rfl
#print axioms native_parser57
theorem native_field57 : FIo_Native.weights.field (JFw_Frames.window 8007 2048) 57#usize=
    ok (FIo_Install.toE value57) :=
  JGo_TX2_MessageRead.native _ 57#usize 1824#usize 58#usize 1856#usize bytes57 _
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 57#usize 32#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 57#usize 1#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 58#usize 32#usize (by decide)))
    (JGo_TX2_MessageRead.range _ _ _ bytes57 (by decide)
      (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
      (by decide) selected57) native_parser57
#print axioms native_field57
theorem canonical57 : Port4C_QueryArithmetic.CanonE value57 := by
  change (1065623334<2147483647 ∧ 835265977<2147483647 ∧ 1026621096<2147483647 ∧ 474049857<2147483647) ∧
    (1172145980<2147483647 ∧ 554081829<2147483647 ∧ 46013768<2147483647 ∧ 1524611267<2147483647)
  omega
#print axioms canonical57
def bytes58 : Array U8 32#usize := ⟨JGe_Window31.c58,by rfl⟩
def value58 : AspisR1Stage2.Stage2Finish.E := ⟨⟨⟨767387596#u32,1050682836#u32⟩,⟨1252311754#u32,226416815#u32⟩⟩,⟨⟨138186223#u32,271360141#u32⟩,⟨889510621#u32,2073224838#u32⟩⟩⟩
def record58 : AspisR1RecordParser.field.wide_exact.WideExact := ⟨⟨⟨767387596#u32,1050682836#u32⟩,⟨1252311754#u32,226416815#u32⟩⟩,⟨⟨138186223#u32,271360141#u32⟩,⟨889510621#u32,2073224838#u32⟩⟩⟩
theorem selected58 : ((JFw_Frames.window 8007 2048).val.drop (32*58)).take 32=bytes58.val := by
  rw [JGo_TX2_MessageRead.cell 58 (by decide)]
  exact JGe_Window31.selected58
#print axioms selected58
theorem parser58 : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes58)=ok (some record58) := by
  apply (AspisR1.ExtractedRecordByteCanonicality.fixed_success_iff bytes58 record58).mpr
  constructor
  · intro j
    fin_cases j <;> decide
  · rfl
#print axioms parser58
theorem field58 : FIn_Primitives.field (JFw_Frames.window 8007 2048) 58#usize=ok value58 :=
  JGo_TX2_FieldRead.source _ _ bytes58 record58
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    selected58 parser58
#print axioms field58
theorem native_parser58 : FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes58)=ok (some (FIo_Install.toE value58)) := by
  with_unfolding_all rfl
#print axioms native_parser58
theorem native_field58 : FIo_Native.weights.field (JFw_Frames.window 8007 2048) 58#usize=
    ok (FIo_Install.toE value58) :=
  JGo_TX2_MessageRead.native _ 58#usize 1856#usize 59#usize 1888#usize bytes58 _
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 58#usize 32#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 58#usize 1#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 59#usize 32#usize (by decide)))
    (JGo_TX2_MessageRead.range _ _ _ bytes58 (by decide)
      (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
      (by decide) selected58) native_parser58
#print axioms native_field58
theorem canonical58 : Port4C_QueryArithmetic.CanonE value58 := by
  change (767387596<2147483647 ∧ 1050682836<2147483647 ∧ 1252311754<2147483647 ∧ 226416815<2147483647) ∧
    (138186223<2147483647 ∧ 271360141<2147483647 ∧ 889510621<2147483647 ∧ 2073224838<2147483647)
  omega
#print axioms canonical58
def bytes59 : Array U8 32#usize := ⟨JGe_Window31.c59,by rfl⟩
def value59 : AspisR1Stage2.Stage2Finish.E := ⟨⟨⟨1034745658#u32,1137417767#u32⟩,⟨2013951489#u32,1848145943#u32⟩⟩,⟨⟨311288937#u32,1225076336#u32⟩,⟨90994186#u32,1796243602#u32⟩⟩⟩
def record59 : AspisR1RecordParser.field.wide_exact.WideExact := ⟨⟨⟨1034745658#u32,1137417767#u32⟩,⟨2013951489#u32,1848145943#u32⟩⟩,⟨⟨311288937#u32,1225076336#u32⟩,⟨90994186#u32,1796243602#u32⟩⟩⟩
theorem selected59 : ((JFw_Frames.window 8007 2048).val.drop (32*59)).take 32=bytes59.val := by
  rw [JGo_TX2_MessageRead.cell 59 (by decide)]
  exact JGe_Window31.selected59
#print axioms selected59
theorem parser59 : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes59)=ok (some record59) := by
  apply (AspisR1.ExtractedRecordByteCanonicality.fixed_success_iff bytes59 record59).mpr
  constructor
  · intro j
    fin_cases j <;> decide
  · rfl
#print axioms parser59
theorem field59 : FIn_Primitives.field (JFw_Frames.window 8007 2048) 59#usize=ok value59 :=
  JGo_TX2_FieldRead.source _ _ bytes59 record59
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    selected59 parser59
#print axioms field59
theorem native_parser59 : FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes59)=ok (some (FIo_Install.toE value59)) := by
  with_unfolding_all rfl
#print axioms native_parser59
theorem native_field59 : FIo_Native.weights.field (JFw_Frames.window 8007 2048) 59#usize=
    ok (FIo_Install.toE value59) :=
  JGo_TX2_MessageRead.native _ 59#usize 1888#usize 60#usize 1920#usize bytes59 _
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 59#usize 32#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 59#usize 1#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 60#usize 32#usize (by decide)))
    (JGo_TX2_MessageRead.range _ _ _ bytes59 (by decide)
      (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
      (by decide) selected59) native_parser59
#print axioms native_field59
theorem canonical59 : Port4C_QueryArithmetic.CanonE value59 := by
  change (1034745658<2147483647 ∧ 1137417767<2147483647 ∧ 2013951489<2147483647 ∧ 1848145943<2147483647) ∧
    (311288937<2147483647 ∧ 1225076336<2147483647 ∧ 90994186<2147483647 ∧ 1796243602<2147483647)
  omega
#print axioms canonical59
def bytes60 : Array U8 32#usize := ⟨JGe_Window31.c60,by rfl⟩
def value60 : AspisR1Stage2.Stage2Finish.E := ⟨⟨⟨1252528856#u32,2088926438#u32⟩,⟨2030579456#u32,176548900#u32⟩⟩,⟨⟨1508444276#u32,1489722908#u32⟩,⟨1556620679#u32,1278824345#u32⟩⟩⟩
def record60 : AspisR1RecordParser.field.wide_exact.WideExact := ⟨⟨⟨1252528856#u32,2088926438#u32⟩,⟨2030579456#u32,176548900#u32⟩⟩,⟨⟨1508444276#u32,1489722908#u32⟩,⟨1556620679#u32,1278824345#u32⟩⟩⟩
theorem selected60 : ((JFw_Frames.window 8007 2048).val.drop (32*60)).take 32=bytes60.val := by
  rw [JGo_TX2_MessageRead.cell 60 (by decide)]
  exact JGe_Window31.selected60
#print axioms selected60
theorem parser60 : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes60)=ok (some record60) := by
  apply (AspisR1.ExtractedRecordByteCanonicality.fixed_success_iff bytes60 record60).mpr
  constructor
  · intro j
    fin_cases j <;> decide
  · rfl
#print axioms parser60
theorem field60 : FIn_Primitives.field (JFw_Frames.window 8007 2048) 60#usize=ok value60 :=
  JGo_TX2_FieldRead.source _ _ bytes60 record60
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    selected60 parser60
#print axioms field60
theorem native_parser60 : FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes60)=ok (some (FIo_Install.toE value60)) := by
  with_unfolding_all rfl
#print axioms native_parser60
theorem native_field60 : FIo_Native.weights.field (JFw_Frames.window 8007 2048) 60#usize=
    ok (FIo_Install.toE value60) :=
  JGo_TX2_MessageRead.native _ 60#usize 1920#usize 61#usize 1952#usize bytes60 _
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 60#usize 32#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 60#usize 1#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 61#usize 32#usize (by decide)))
    (JGo_TX2_MessageRead.range _ _ _ bytes60 (by decide)
      (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
      (by decide) selected60) native_parser60
#print axioms native_field60
theorem canonical60 : Port4C_QueryArithmetic.CanonE value60 := by
  change (1252528856<2147483647 ∧ 2088926438<2147483647 ∧ 2030579456<2147483647 ∧ 176548900<2147483647) ∧
    (1508444276<2147483647 ∧ 1489722908<2147483647 ∧ 1556620679<2147483647 ∧ 1278824345<2147483647)
  omega
#print axioms canonical60
def bytes61 : Array U8 32#usize := ⟨JGe_Window31.c61,by rfl⟩
def value61 : AspisR1Stage2.Stage2Finish.E := ⟨⟨⟨499686835#u32,1261097404#u32⟩,⟨318767526#u32,1595063259#u32⟩⟩,⟨⟨1511640846#u32,571992658#u32⟩,⟨1656205880#u32,832316434#u32⟩⟩⟩
def record61 : AspisR1RecordParser.field.wide_exact.WideExact := ⟨⟨⟨499686835#u32,1261097404#u32⟩,⟨318767526#u32,1595063259#u32⟩⟩,⟨⟨1511640846#u32,571992658#u32⟩,⟨1656205880#u32,832316434#u32⟩⟩⟩
theorem selected61 : ((JFw_Frames.window 8007 2048).val.drop (32*61)).take 32=bytes61.val := by
  rw [JGo_TX2_MessageRead.cell 61 (by decide)]
  exact JGe_Window31.selected61
#print axioms selected61
theorem parser61 : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes61)=ok (some record61) := by
  apply (AspisR1.ExtractedRecordByteCanonicality.fixed_success_iff bytes61 record61).mpr
  constructor
  · intro j
    fin_cases j <;> decide
  · rfl
#print axioms parser61
theorem field61 : FIn_Primitives.field (JFw_Frames.window 8007 2048) 61#usize=ok value61 :=
  JGo_TX2_FieldRead.source _ _ bytes61 record61
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    selected61 parser61
#print axioms field61
theorem native_parser61 : FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes61)=ok (some (FIo_Install.toE value61)) := by
  with_unfolding_all rfl
#print axioms native_parser61
theorem native_field61 : FIo_Native.weights.field (JFw_Frames.window 8007 2048) 61#usize=
    ok (FIo_Install.toE value61) :=
  JGo_TX2_MessageRead.native _ 61#usize 1952#usize 62#usize 1984#usize bytes61 _
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 61#usize 32#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 61#usize 1#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 62#usize 32#usize (by decide)))
    (JGo_TX2_MessageRead.range _ _ _ bytes61 (by decide)
      (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
      (by decide) selected61) native_parser61
#print axioms native_field61
theorem canonical61 : Port4C_QueryArithmetic.CanonE value61 := by
  change (499686835<2147483647 ∧ 1261097404<2147483647 ∧ 318767526<2147483647 ∧ 1595063259<2147483647) ∧
    (1511640846<2147483647 ∧ 571992658<2147483647 ∧ 1656205880<2147483647 ∧ 832316434<2147483647)
  omega
#print axioms canonical61
def bytes62 : Array U8 32#usize := ⟨JGe_Window31.c62,by rfl⟩
def value62 : AspisR1Stage2.Stage2Finish.E := ⟨⟨⟨1948242685#u32,208249549#u32⟩,⟨1029099444#u32,1510670935#u32⟩⟩,⟨⟨1854560775#u32,1888659294#u32⟩,⟨216630966#u32,752431274#u32⟩⟩⟩
def record62 : AspisR1RecordParser.field.wide_exact.WideExact := ⟨⟨⟨1948242685#u32,208249549#u32⟩,⟨1029099444#u32,1510670935#u32⟩⟩,⟨⟨1854560775#u32,1888659294#u32⟩,⟨216630966#u32,752431274#u32⟩⟩⟩
theorem selected62 : ((JFw_Frames.window 8007 2048).val.drop (32*62)).take 32=bytes62.val := by
  rw [JGo_TX2_MessageRead.cell 62 (by decide)]
  exact JGe_Window31.selected62
#print axioms selected62
theorem parser62 : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes62)=ok (some record62) := by
  apply (AspisR1.ExtractedRecordByteCanonicality.fixed_success_iff bytes62 record62).mpr
  constructor
  · intro j
    fin_cases j <;> decide
  · rfl
#print axioms parser62
theorem field62 : FIn_Primitives.field (JFw_Frames.window 8007 2048) 62#usize=ok value62 :=
  JGo_TX2_FieldRead.source _ _ bytes62 record62
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    selected62 parser62
#print axioms field62
theorem native_parser62 : FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes62)=ok (some (FIo_Install.toE value62)) := by
  with_unfolding_all rfl
#print axioms native_parser62
theorem native_field62 : FIo_Native.weights.field (JFw_Frames.window 8007 2048) 62#usize=
    ok (FIo_Install.toE value62) :=
  JGo_TX2_MessageRead.native _ 62#usize 1984#usize 63#usize 2016#usize bytes62 _
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 62#usize 32#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 62#usize 1#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 63#usize 32#usize (by decide)))
    (JGo_TX2_MessageRead.range _ _ _ bytes62 (by decide)
      (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
      (by decide) selected62) native_parser62
#print axioms native_field62
theorem canonical62 : Port4C_QueryArithmetic.CanonE value62 := by
  change (1948242685<2147483647 ∧ 208249549<2147483647 ∧ 1029099444<2147483647 ∧ 1510670935<2147483647) ∧
    (1854560775<2147483647 ∧ 1888659294<2147483647 ∧ 216630966<2147483647 ∧ 752431274<2147483647)
  omega
#print axioms canonical62
def bytes63 : Array U8 32#usize := ⟨JGe_Window31.c63,by rfl⟩
def value63 : AspisR1Stage2.Stage2Finish.E := ⟨⟨⟨1623638215#u32,107262183#u32⟩,⟨2058749145#u32,593924823#u32⟩⟩,⟨⟨599190902#u32,807350687#u32⟩,⟨745771250#u32,1100901523#u32⟩⟩⟩
def record63 : AspisR1RecordParser.field.wide_exact.WideExact := ⟨⟨⟨1623638215#u32,107262183#u32⟩,⟨2058749145#u32,593924823#u32⟩⟩,⟨⟨599190902#u32,807350687#u32⟩,⟨745771250#u32,1100901523#u32⟩⟩⟩
theorem selected63 : ((JFw_Frames.window 8007 2048).val.drop (32*63)).take 32=bytes63.val := by
  rw [JGo_TX2_MessageRead.cell 63 (by decide)]
  exact JGe_Window31.selected63
#print axioms selected63
theorem parser63 : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes63)=ok (some record63) := by
  apply (AspisR1.ExtractedRecordByteCanonicality.fixed_success_iff bytes63 record63).mpr
  constructor
  · intro j
    fin_cases j <;> decide
  · rfl
#print axioms parser63
theorem field63 : FIn_Primitives.field (JFw_Frames.window 8007 2048) 63#usize=ok value63 :=
  JGo_TX2_FieldRead.source _ _ bytes63 record63
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    selected63 parser63
#print axioms field63
theorem native_parser63 : FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes63)=ok (some (FIo_Install.toE value63)) := by
  with_unfolding_all rfl
#print axioms native_parser63
theorem native_field63 : FIo_Native.weights.field (JFw_Frames.window 8007 2048) 63#usize=
    ok (FIo_Install.toE value63) :=
  JGo_TX2_MessageRead.native _ 63#usize 2016#usize 64#usize 2048#usize bytes63 _
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 63#usize 32#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 63#usize 1#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 64#usize 32#usize (by decide)))
    (JGo_TX2_MessageRead.range _ _ _ bytes63 (by decide)
      (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
      (by decide) selected63) native_parser63
#print axioms native_field63
theorem canonical63 : Port4C_QueryArithmetic.CanonE value63 := by
  change (1623638215<2147483647 ∧ 107262183<2147483647 ∧ 2058749145<2147483647 ∧ 593924823<2147483647) ∧
    (599190902<2147483647 ∧ 807350687<2147483647 ∧ 745771250<2147483647 ∧ 1100901523<2147483647)
  omega
#print axioms canonical63
end AspisR1.JGo_TX2_Message56
end
