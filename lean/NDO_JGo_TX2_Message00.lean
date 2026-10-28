import NDO_JGo_TX2_MessageRead
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGo_TX2_Message00
open Aeneas Aeneas.Std Result
attribute [local irreducible] JFx_NativeBytes.proof JFw_Frames.window
def bytes00 : Array U8 32#usize := ⟨JGe_Window31.c00,by rfl⟩
def value00 : AspisR1Stage2.Stage2Finish.E := ⟨⟨⟨1768393945#u32,1488333389#u32⟩,⟨1503170404#u32,1567512050#u32⟩⟩,⟨⟨1419395624#u32,435735133#u32⟩,⟨1364031307#u32,1659625415#u32⟩⟩⟩
def record00 : AspisR1RecordParser.field.wide_exact.WideExact := ⟨⟨⟨1768393945#u32,1488333389#u32⟩,⟨1503170404#u32,1567512050#u32⟩⟩,⟨⟨1419395624#u32,435735133#u32⟩,⟨1364031307#u32,1659625415#u32⟩⟩⟩
theorem selected00 : ((JFw_Frames.window 8007 2048).val.drop (32*0)).take 32=bytes00.val := by
  rw [JGo_TX2_MessageRead.cell 0 (by decide)]
  exact JGe_Window31.selected00
#print axioms selected00
theorem parser00 : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes00)=ok (some record00) := by
  apply (AspisR1.ExtractedRecordByteCanonicality.fixed_success_iff bytes00 record00).mpr
  constructor
  · intro j
    fin_cases j <;> decide
  · rfl
#print axioms parser00
theorem field00 : FIn_Primitives.field (JFw_Frames.window 8007 2048) 0#usize=ok value00 :=
  JGo_TX2_FieldRead.source _ _ bytes00 record00
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    selected00 parser00
#print axioms field00
theorem native_parser00 : FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes00)=ok (some (FIo_Install.toE value00)) := by
  with_unfolding_all rfl
#print axioms native_parser00
theorem native_field00 : FIo_Native.weights.field (JFw_Frames.window 8007 2048) 0#usize=
    ok (FIo_Install.toE value00) :=
  JGo_TX2_MessageRead.native _ 0#usize 0#usize 1#usize 32#usize bytes00 _
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 0#usize 32#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 0#usize 1#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 1#usize 32#usize (by decide)))
    (JGo_TX2_MessageRead.range _ _ _ bytes00 (by decide)
      (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
      (by decide) selected00) native_parser00
#print axioms native_field00
theorem canonical00 : Port4C_QueryArithmetic.CanonE value00 := by
  change (1768393945<2147483647 ∧ 1488333389<2147483647 ∧ 1503170404<2147483647 ∧ 1567512050<2147483647) ∧
    (1419395624<2147483647 ∧ 435735133<2147483647 ∧ 1364031307<2147483647 ∧ 1659625415<2147483647)
  omega
#print axioms canonical00
def bytes01 : Array U8 32#usize := ⟨JGe_Window31.c01,by rfl⟩
def value01 : AspisR1Stage2.Stage2Finish.E := ⟨⟨⟨224877681#u32,1521020287#u32⟩,⟨398517914#u32,1031173231#u32⟩⟩,⟨⟨703884486#u32,72695332#u32⟩,⟨1310399171#u32,1127850411#u32⟩⟩⟩
def record01 : AspisR1RecordParser.field.wide_exact.WideExact := ⟨⟨⟨224877681#u32,1521020287#u32⟩,⟨398517914#u32,1031173231#u32⟩⟩,⟨⟨703884486#u32,72695332#u32⟩,⟨1310399171#u32,1127850411#u32⟩⟩⟩
theorem selected01 : ((JFw_Frames.window 8007 2048).val.drop (32*1)).take 32=bytes01.val := by
  rw [JGo_TX2_MessageRead.cell 1 (by decide)]
  exact JGe_Window31.selected01
#print axioms selected01
theorem parser01 : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes01)=ok (some record01) := by
  apply (AspisR1.ExtractedRecordByteCanonicality.fixed_success_iff bytes01 record01).mpr
  constructor
  · intro j
    fin_cases j <;> decide
  · rfl
#print axioms parser01
theorem field01 : FIn_Primitives.field (JFw_Frames.window 8007 2048) 1#usize=ok value01 :=
  JGo_TX2_FieldRead.source _ _ bytes01 record01
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    selected01 parser01
#print axioms field01
theorem native_parser01 : FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes01)=ok (some (FIo_Install.toE value01)) := by
  with_unfolding_all rfl
#print axioms native_parser01
theorem native_field01 : FIo_Native.weights.field (JFw_Frames.window 8007 2048) 1#usize=
    ok (FIo_Install.toE value01) :=
  JGo_TX2_MessageRead.native _ 1#usize 32#usize 2#usize 64#usize bytes01 _
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 1#usize 32#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 1#usize 1#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 2#usize 32#usize (by decide)))
    (JGo_TX2_MessageRead.range _ _ _ bytes01 (by decide)
      (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
      (by decide) selected01) native_parser01
#print axioms native_field01
theorem canonical01 : Port4C_QueryArithmetic.CanonE value01 := by
  change (224877681<2147483647 ∧ 1521020287<2147483647 ∧ 398517914<2147483647 ∧ 1031173231<2147483647) ∧
    (703884486<2147483647 ∧ 72695332<2147483647 ∧ 1310399171<2147483647 ∧ 1127850411<2147483647)
  omega
#print axioms canonical01
def bytes02 : Array U8 32#usize := ⟨JGe_Window31.c02,by rfl⟩
def value02 : AspisR1Stage2.Stage2Finish.E := ⟨⟨⟨1754601432#u32,1956476198#u32⟩,⟨1401883008#u32,805224137#u32⟩⟩,⟨⟨117033247#u32,794800903#u32⟩,⟨588785133#u32,253636777#u32⟩⟩⟩
def record02 : AspisR1RecordParser.field.wide_exact.WideExact := ⟨⟨⟨1754601432#u32,1956476198#u32⟩,⟨1401883008#u32,805224137#u32⟩⟩,⟨⟨117033247#u32,794800903#u32⟩,⟨588785133#u32,253636777#u32⟩⟩⟩
theorem selected02 : ((JFw_Frames.window 8007 2048).val.drop (32*2)).take 32=bytes02.val := by
  rw [JGo_TX2_MessageRead.cell 2 (by decide)]
  exact JGe_Window31.selected02
#print axioms selected02
theorem parser02 : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes02)=ok (some record02) := by
  apply (AspisR1.ExtractedRecordByteCanonicality.fixed_success_iff bytes02 record02).mpr
  constructor
  · intro j
    fin_cases j <;> decide
  · rfl
#print axioms parser02
theorem field02 : FIn_Primitives.field (JFw_Frames.window 8007 2048) 2#usize=ok value02 :=
  JGo_TX2_FieldRead.source _ _ bytes02 record02
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    selected02 parser02
#print axioms field02
theorem native_parser02 : FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes02)=ok (some (FIo_Install.toE value02)) := by
  with_unfolding_all rfl
#print axioms native_parser02
theorem native_field02 : FIo_Native.weights.field (JFw_Frames.window 8007 2048) 2#usize=
    ok (FIo_Install.toE value02) :=
  JGo_TX2_MessageRead.native _ 2#usize 64#usize 3#usize 96#usize bytes02 _
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 2#usize 32#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 2#usize 1#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 3#usize 32#usize (by decide)))
    (JGo_TX2_MessageRead.range _ _ _ bytes02 (by decide)
      (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
      (by decide) selected02) native_parser02
#print axioms native_field02
theorem canonical02 : Port4C_QueryArithmetic.CanonE value02 := by
  change (1754601432<2147483647 ∧ 1956476198<2147483647 ∧ 1401883008<2147483647 ∧ 805224137<2147483647) ∧
    (117033247<2147483647 ∧ 794800903<2147483647 ∧ 588785133<2147483647 ∧ 253636777<2147483647)
  omega
#print axioms canonical02
def bytes03 : Array U8 32#usize := ⟨JGe_Window31.c03,by rfl⟩
def value03 : AspisR1Stage2.Stage2Finish.E := ⟨⟨⟨1722370993#u32,1485906699#u32⟩,⟨916894452#u32,863561856#u32⟩⟩,⟨⟨1553260334#u32,702583039#u32⟩,⟨98010632#u32,2070576577#u32⟩⟩⟩
def record03 : AspisR1RecordParser.field.wide_exact.WideExact := ⟨⟨⟨1722370993#u32,1485906699#u32⟩,⟨916894452#u32,863561856#u32⟩⟩,⟨⟨1553260334#u32,702583039#u32⟩,⟨98010632#u32,2070576577#u32⟩⟩⟩
theorem selected03 : ((JFw_Frames.window 8007 2048).val.drop (32*3)).take 32=bytes03.val := by
  rw [JGo_TX2_MessageRead.cell 3 (by decide)]
  exact JGe_Window31.selected03
#print axioms selected03
theorem parser03 : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes03)=ok (some record03) := by
  apply (AspisR1.ExtractedRecordByteCanonicality.fixed_success_iff bytes03 record03).mpr
  constructor
  · intro j
    fin_cases j <;> decide
  · rfl
#print axioms parser03
theorem field03 : FIn_Primitives.field (JFw_Frames.window 8007 2048) 3#usize=ok value03 :=
  JGo_TX2_FieldRead.source _ _ bytes03 record03
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    selected03 parser03
#print axioms field03
theorem native_parser03 : FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes03)=ok (some (FIo_Install.toE value03)) := by
  with_unfolding_all rfl
#print axioms native_parser03
theorem native_field03 : FIo_Native.weights.field (JFw_Frames.window 8007 2048) 3#usize=
    ok (FIo_Install.toE value03) :=
  JGo_TX2_MessageRead.native _ 3#usize 96#usize 4#usize 128#usize bytes03 _
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 3#usize 32#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 3#usize 1#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 4#usize 32#usize (by decide)))
    (JGo_TX2_MessageRead.range _ _ _ bytes03 (by decide)
      (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
      (by decide) selected03) native_parser03
#print axioms native_field03
theorem canonical03 : Port4C_QueryArithmetic.CanonE value03 := by
  change (1722370993<2147483647 ∧ 1485906699<2147483647 ∧ 916894452<2147483647 ∧ 863561856<2147483647) ∧
    (1553260334<2147483647 ∧ 702583039<2147483647 ∧ 98010632<2147483647 ∧ 2070576577<2147483647)
  omega
#print axioms canonical03
def bytes04 : Array U8 32#usize := ⟨JGe_Window31.c04,by rfl⟩
def value04 : AspisR1Stage2.Stage2Finish.E := ⟨⟨⟨2072128621#u32,1064428063#u32⟩,⟨1661829704#u32,994150077#u32⟩⟩,⟨⟨1269068291#u32,306305045#u32⟩,⟨255265448#u32,693068399#u32⟩⟩⟩
def record04 : AspisR1RecordParser.field.wide_exact.WideExact := ⟨⟨⟨2072128621#u32,1064428063#u32⟩,⟨1661829704#u32,994150077#u32⟩⟩,⟨⟨1269068291#u32,306305045#u32⟩,⟨255265448#u32,693068399#u32⟩⟩⟩
theorem selected04 : ((JFw_Frames.window 8007 2048).val.drop (32*4)).take 32=bytes04.val := by
  rw [JGo_TX2_MessageRead.cell 4 (by decide)]
  exact JGe_Window31.selected04
#print axioms selected04
theorem parser04 : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes04)=ok (some record04) := by
  apply (AspisR1.ExtractedRecordByteCanonicality.fixed_success_iff bytes04 record04).mpr
  constructor
  · intro j
    fin_cases j <;> decide
  · rfl
#print axioms parser04
theorem field04 : FIn_Primitives.field (JFw_Frames.window 8007 2048) 4#usize=ok value04 :=
  JGo_TX2_FieldRead.source _ _ bytes04 record04
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    selected04 parser04
#print axioms field04
theorem native_parser04 : FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes04)=ok (some (FIo_Install.toE value04)) := by
  with_unfolding_all rfl
#print axioms native_parser04
theorem native_field04 : FIo_Native.weights.field (JFw_Frames.window 8007 2048) 4#usize=
    ok (FIo_Install.toE value04) :=
  JGo_TX2_MessageRead.native _ 4#usize 128#usize 5#usize 160#usize bytes04 _
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 4#usize 32#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 4#usize 1#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 5#usize 32#usize (by decide)))
    (JGo_TX2_MessageRead.range _ _ _ bytes04 (by decide)
      (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
      (by decide) selected04) native_parser04
#print axioms native_field04
theorem canonical04 : Port4C_QueryArithmetic.CanonE value04 := by
  change (2072128621<2147483647 ∧ 1064428063<2147483647 ∧ 1661829704<2147483647 ∧ 994150077<2147483647) ∧
    (1269068291<2147483647 ∧ 306305045<2147483647 ∧ 255265448<2147483647 ∧ 693068399<2147483647)
  omega
#print axioms canonical04
def bytes05 : Array U8 32#usize := ⟨JGe_Window31.c05,by rfl⟩
def value05 : AspisR1Stage2.Stage2Finish.E := ⟨⟨⟨524150554#u32,1372413728#u32⟩,⟨1523014368#u32,708500215#u32⟩⟩,⟨⟨331295891#u32,1149802308#u32⟩,⟨1261892231#u32,291778985#u32⟩⟩⟩
def record05 : AspisR1RecordParser.field.wide_exact.WideExact := ⟨⟨⟨524150554#u32,1372413728#u32⟩,⟨1523014368#u32,708500215#u32⟩⟩,⟨⟨331295891#u32,1149802308#u32⟩,⟨1261892231#u32,291778985#u32⟩⟩⟩
theorem selected05 : ((JFw_Frames.window 8007 2048).val.drop (32*5)).take 32=bytes05.val := by
  rw [JGo_TX2_MessageRead.cell 5 (by decide)]
  exact JGe_Window31.selected05
#print axioms selected05
theorem parser05 : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes05)=ok (some record05) := by
  apply (AspisR1.ExtractedRecordByteCanonicality.fixed_success_iff bytes05 record05).mpr
  constructor
  · intro j
    fin_cases j <;> decide
  · rfl
#print axioms parser05
theorem field05 : FIn_Primitives.field (JFw_Frames.window 8007 2048) 5#usize=ok value05 :=
  JGo_TX2_FieldRead.source _ _ bytes05 record05
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    selected05 parser05
#print axioms field05
theorem native_parser05 : FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes05)=ok (some (FIo_Install.toE value05)) := by
  with_unfolding_all rfl
#print axioms native_parser05
theorem native_field05 : FIo_Native.weights.field (JFw_Frames.window 8007 2048) 5#usize=
    ok (FIo_Install.toE value05) :=
  JGo_TX2_MessageRead.native _ 5#usize 160#usize 6#usize 192#usize bytes05 _
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 5#usize 32#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 5#usize 1#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 6#usize 32#usize (by decide)))
    (JGo_TX2_MessageRead.range _ _ _ bytes05 (by decide)
      (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
      (by decide) selected05) native_parser05
#print axioms native_field05
theorem canonical05 : Port4C_QueryArithmetic.CanonE value05 := by
  change (524150554<2147483647 ∧ 1372413728<2147483647 ∧ 1523014368<2147483647 ∧ 708500215<2147483647) ∧
    (331295891<2147483647 ∧ 1149802308<2147483647 ∧ 1261892231<2147483647 ∧ 291778985<2147483647)
  omega
#print axioms canonical05
def bytes06 : Array U8 32#usize := ⟨JGe_Window31.c06,by rfl⟩
def value06 : AspisR1Stage2.Stage2Finish.E := ⟨⟨⟨1009192178#u32,550423224#u32⟩,⟨236511928#u32,882038573#u32⟩⟩,⟨⟨225224228#u32,1836486627#u32⟩,⟨310226060#u32,1333672817#u32⟩⟩⟩
def record06 : AspisR1RecordParser.field.wide_exact.WideExact := ⟨⟨⟨1009192178#u32,550423224#u32⟩,⟨236511928#u32,882038573#u32⟩⟩,⟨⟨225224228#u32,1836486627#u32⟩,⟨310226060#u32,1333672817#u32⟩⟩⟩
theorem selected06 : ((JFw_Frames.window 8007 2048).val.drop (32*6)).take 32=bytes06.val := by
  rw [JGo_TX2_MessageRead.cell 6 (by decide)]
  exact JGe_Window31.selected06
#print axioms selected06
theorem parser06 : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes06)=ok (some record06) := by
  apply (AspisR1.ExtractedRecordByteCanonicality.fixed_success_iff bytes06 record06).mpr
  constructor
  · intro j
    fin_cases j <;> decide
  · rfl
#print axioms parser06
theorem field06 : FIn_Primitives.field (JFw_Frames.window 8007 2048) 6#usize=ok value06 :=
  JGo_TX2_FieldRead.source _ _ bytes06 record06
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    selected06 parser06
#print axioms field06
theorem native_parser06 : FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes06)=ok (some (FIo_Install.toE value06)) := by
  with_unfolding_all rfl
#print axioms native_parser06
theorem native_field06 : FIo_Native.weights.field (JFw_Frames.window 8007 2048) 6#usize=
    ok (FIo_Install.toE value06) :=
  JGo_TX2_MessageRead.native _ 6#usize 192#usize 7#usize 224#usize bytes06 _
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 6#usize 32#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 6#usize 1#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 7#usize 32#usize (by decide)))
    (JGo_TX2_MessageRead.range _ _ _ bytes06 (by decide)
      (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
      (by decide) selected06) native_parser06
#print axioms native_field06
theorem canonical06 : Port4C_QueryArithmetic.CanonE value06 := by
  change (1009192178<2147483647 ∧ 550423224<2147483647 ∧ 236511928<2147483647 ∧ 882038573<2147483647) ∧
    (225224228<2147483647 ∧ 1836486627<2147483647 ∧ 310226060<2147483647 ∧ 1333672817<2147483647)
  omega
#print axioms canonical06
def bytes07 : Array U8 32#usize := ⟨JGe_Window31.c07,by rfl⟩
def value07 : AspisR1Stage2.Stage2Finish.E := ⟨⟨⟨1885796849#u32,2043387770#u32⟩,⟨1452188917#u32,2128993025#u32⟩⟩,⟨⟨1289552700#u32,1179460303#u32⟩,⟨1596985050#u32,363862881#u32⟩⟩⟩
def record07 : AspisR1RecordParser.field.wide_exact.WideExact := ⟨⟨⟨1885796849#u32,2043387770#u32⟩,⟨1452188917#u32,2128993025#u32⟩⟩,⟨⟨1289552700#u32,1179460303#u32⟩,⟨1596985050#u32,363862881#u32⟩⟩⟩
theorem selected07 : ((JFw_Frames.window 8007 2048).val.drop (32*7)).take 32=bytes07.val := by
  rw [JGo_TX2_MessageRead.cell 7 (by decide)]
  exact JGe_Window31.selected07
#print axioms selected07
theorem parser07 : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes07)=ok (some record07) := by
  apply (AspisR1.ExtractedRecordByteCanonicality.fixed_success_iff bytes07 record07).mpr
  constructor
  · intro j
    fin_cases j <;> decide
  · rfl
#print axioms parser07
theorem field07 : FIn_Primitives.field (JFw_Frames.window 8007 2048) 7#usize=ok value07 :=
  JGo_TX2_FieldRead.source _ _ bytes07 record07
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    selected07 parser07
#print axioms field07
theorem native_parser07 : FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes07)=ok (some (FIo_Install.toE value07)) := by
  with_unfolding_all rfl
#print axioms native_parser07
theorem native_field07 : FIo_Native.weights.field (JFw_Frames.window 8007 2048) 7#usize=
    ok (FIo_Install.toE value07) :=
  JGo_TX2_MessageRead.native _ 7#usize 224#usize 8#usize 256#usize bytes07 _
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 7#usize 32#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 7#usize 1#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 8#usize 32#usize (by decide)))
    (JGo_TX2_MessageRead.range _ _ _ bytes07 (by decide)
      (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
      (by decide) selected07) native_parser07
#print axioms native_field07
theorem canonical07 : Port4C_QueryArithmetic.CanonE value07 := by
  change (1885796849<2147483647 ∧ 2043387770<2147483647 ∧ 1452188917<2147483647 ∧ 2128993025<2147483647) ∧
    (1289552700<2147483647 ∧ 1179460303<2147483647 ∧ 1596985050<2147483647 ∧ 363862881<2147483647)
  omega
#print axioms canonical07
end AspisR1.JGo_TX2_Message00
end
