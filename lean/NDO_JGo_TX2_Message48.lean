import NDO_JGo_TX2_MessageRead
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGo_TX2_Message48
open Aeneas Aeneas.Std Result
attribute [local irreducible] JFx_NativeBytes.proof JFw_Frames.window
def bytes48 : Array U8 32#usize := ⟨JGe_Window31.c48,by rfl⟩
def value48 : AspisR1Stage2.Stage2Finish.E := ⟨⟨⟨1592444808#u32,1616233393#u32⟩,⟨303581578#u32,588364506#u32⟩⟩,⟨⟨1472938484#u32,1688272458#u32⟩,⟨56036177#u32,869751590#u32⟩⟩⟩
def record48 : AspisR1RecordParser.field.wide_exact.WideExact := ⟨⟨⟨1592444808#u32,1616233393#u32⟩,⟨303581578#u32,588364506#u32⟩⟩,⟨⟨1472938484#u32,1688272458#u32⟩,⟨56036177#u32,869751590#u32⟩⟩⟩
theorem selected48 : ((JFw_Frames.window 8007 2048).val.drop (32*48)).take 32=bytes48.val := by
  rw [JGo_TX2_MessageRead.cell 48 (by decide)]
  exact JGe_Window31.selected48
#print axioms selected48
theorem parser48 : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes48)=ok (some record48) := by
  apply (AspisR1.ExtractedRecordByteCanonicality.fixed_success_iff bytes48 record48).mpr
  constructor
  · intro j
    fin_cases j <;> decide
  · rfl
#print axioms parser48
theorem field48 : FIn_Primitives.field (JFw_Frames.window 8007 2048) 48#usize=ok value48 :=
  JGo_TX2_FieldRead.source _ _ bytes48 record48
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    selected48 parser48
#print axioms field48
theorem native_parser48 : FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes48)=ok (some (FIo_Install.toE value48)) := by
  with_unfolding_all rfl
#print axioms native_parser48
theorem native_field48 : FIo_Native.weights.field (JFw_Frames.window 8007 2048) 48#usize=
    ok (FIo_Install.toE value48) :=
  JGo_TX2_MessageRead.native _ 48#usize 1536#usize 49#usize 1568#usize bytes48 _
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 48#usize 32#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 48#usize 1#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 49#usize 32#usize (by decide)))
    (JGo_TX2_MessageRead.range _ _ _ bytes48 (by decide)
      (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
      (by decide) selected48) native_parser48
#print axioms native_field48
theorem canonical48 : Port4C_QueryArithmetic.CanonE value48 := by
  change (1592444808<2147483647 ∧ 1616233393<2147483647 ∧ 303581578<2147483647 ∧ 588364506<2147483647) ∧
    (1472938484<2147483647 ∧ 1688272458<2147483647 ∧ 56036177<2147483647 ∧ 869751590<2147483647)
  omega
#print axioms canonical48
def bytes49 : Array U8 32#usize := ⟨JGe_Window31.c49,by rfl⟩
def value49 : AspisR1Stage2.Stage2Finish.E := ⟨⟨⟨1331352015#u32,88995874#u32⟩,⟨107410886#u32,1098573201#u32⟩⟩,⟨⟨221291746#u32,1664469540#u32⟩,⟨529000327#u32,1768805886#u32⟩⟩⟩
def record49 : AspisR1RecordParser.field.wide_exact.WideExact := ⟨⟨⟨1331352015#u32,88995874#u32⟩,⟨107410886#u32,1098573201#u32⟩⟩,⟨⟨221291746#u32,1664469540#u32⟩,⟨529000327#u32,1768805886#u32⟩⟩⟩
theorem selected49 : ((JFw_Frames.window 8007 2048).val.drop (32*49)).take 32=bytes49.val := by
  rw [JGo_TX2_MessageRead.cell 49 (by decide)]
  exact JGe_Window31.selected49
#print axioms selected49
theorem parser49 : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes49)=ok (some record49) := by
  apply (AspisR1.ExtractedRecordByteCanonicality.fixed_success_iff bytes49 record49).mpr
  constructor
  · intro j
    fin_cases j <;> decide
  · rfl
#print axioms parser49
theorem field49 : FIn_Primitives.field (JFw_Frames.window 8007 2048) 49#usize=ok value49 :=
  JGo_TX2_FieldRead.source _ _ bytes49 record49
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    selected49 parser49
#print axioms field49
theorem native_parser49 : FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes49)=ok (some (FIo_Install.toE value49)) := by
  with_unfolding_all rfl
#print axioms native_parser49
theorem native_field49 : FIo_Native.weights.field (JFw_Frames.window 8007 2048) 49#usize=
    ok (FIo_Install.toE value49) :=
  JGo_TX2_MessageRead.native _ 49#usize 1568#usize 50#usize 1600#usize bytes49 _
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 49#usize 32#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 49#usize 1#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 50#usize 32#usize (by decide)))
    (JGo_TX2_MessageRead.range _ _ _ bytes49 (by decide)
      (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
      (by decide) selected49) native_parser49
#print axioms native_field49
theorem canonical49 : Port4C_QueryArithmetic.CanonE value49 := by
  change (1331352015<2147483647 ∧ 88995874<2147483647 ∧ 107410886<2147483647 ∧ 1098573201<2147483647) ∧
    (221291746<2147483647 ∧ 1664469540<2147483647 ∧ 529000327<2147483647 ∧ 1768805886<2147483647)
  omega
#print axioms canonical49
def bytes50 : Array U8 32#usize := ⟨JGe_Window31.c50,by rfl⟩
def value50 : AspisR1Stage2.Stage2Finish.E := ⟨⟨⟨491787508#u32,1606086463#u32⟩,⟨1492454344#u32,1864969791#u32⟩⟩,⟨⟨185138736#u32,1716018090#u32⟩,⟨2047625691#u32,29142495#u32⟩⟩⟩
def record50 : AspisR1RecordParser.field.wide_exact.WideExact := ⟨⟨⟨491787508#u32,1606086463#u32⟩,⟨1492454344#u32,1864969791#u32⟩⟩,⟨⟨185138736#u32,1716018090#u32⟩,⟨2047625691#u32,29142495#u32⟩⟩⟩
theorem selected50 : ((JFw_Frames.window 8007 2048).val.drop (32*50)).take 32=bytes50.val := by
  rw [JGo_TX2_MessageRead.cell 50 (by decide)]
  exact JGe_Window31.selected50
#print axioms selected50
theorem parser50 : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes50)=ok (some record50) := by
  apply (AspisR1.ExtractedRecordByteCanonicality.fixed_success_iff bytes50 record50).mpr
  constructor
  · intro j
    fin_cases j <;> decide
  · rfl
#print axioms parser50
theorem field50 : FIn_Primitives.field (JFw_Frames.window 8007 2048) 50#usize=ok value50 :=
  JGo_TX2_FieldRead.source _ _ bytes50 record50
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    selected50 parser50
#print axioms field50
theorem native_parser50 : FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes50)=ok (some (FIo_Install.toE value50)) := by
  with_unfolding_all rfl
#print axioms native_parser50
theorem native_field50 : FIo_Native.weights.field (JFw_Frames.window 8007 2048) 50#usize=
    ok (FIo_Install.toE value50) :=
  JGo_TX2_MessageRead.native _ 50#usize 1600#usize 51#usize 1632#usize bytes50 _
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 50#usize 32#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 50#usize 1#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 51#usize 32#usize (by decide)))
    (JGo_TX2_MessageRead.range _ _ _ bytes50 (by decide)
      (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
      (by decide) selected50) native_parser50
#print axioms native_field50
theorem canonical50 : Port4C_QueryArithmetic.CanonE value50 := by
  change (491787508<2147483647 ∧ 1606086463<2147483647 ∧ 1492454344<2147483647 ∧ 1864969791<2147483647) ∧
    (185138736<2147483647 ∧ 1716018090<2147483647 ∧ 2047625691<2147483647 ∧ 29142495<2147483647)
  omega
#print axioms canonical50
def bytes51 : Array U8 32#usize := ⟨JGe_Window31.c51,by rfl⟩
def value51 : AspisR1Stage2.Stage2Finish.E := ⟨⟨⟨342461162#u32,52508543#u32⟩,⟨1617583948#u32,1438720280#u32⟩⟩,⟨⟨737938603#u32,1775251747#u32⟩,⟨573188763#u32,1241048442#u32⟩⟩⟩
def record51 : AspisR1RecordParser.field.wide_exact.WideExact := ⟨⟨⟨342461162#u32,52508543#u32⟩,⟨1617583948#u32,1438720280#u32⟩⟩,⟨⟨737938603#u32,1775251747#u32⟩,⟨573188763#u32,1241048442#u32⟩⟩⟩
theorem selected51 : ((JFw_Frames.window 8007 2048).val.drop (32*51)).take 32=bytes51.val := by
  rw [JGo_TX2_MessageRead.cell 51 (by decide)]
  exact JGe_Window31.selected51
#print axioms selected51
theorem parser51 : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes51)=ok (some record51) := by
  apply (AspisR1.ExtractedRecordByteCanonicality.fixed_success_iff bytes51 record51).mpr
  constructor
  · intro j
    fin_cases j <;> decide
  · rfl
#print axioms parser51
theorem field51 : FIn_Primitives.field (JFw_Frames.window 8007 2048) 51#usize=ok value51 :=
  JGo_TX2_FieldRead.source _ _ bytes51 record51
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    selected51 parser51
#print axioms field51
theorem native_parser51 : FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes51)=ok (some (FIo_Install.toE value51)) := by
  with_unfolding_all rfl
#print axioms native_parser51
theorem native_field51 : FIo_Native.weights.field (JFw_Frames.window 8007 2048) 51#usize=
    ok (FIo_Install.toE value51) :=
  JGo_TX2_MessageRead.native _ 51#usize 1632#usize 52#usize 1664#usize bytes51 _
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 51#usize 32#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 51#usize 1#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 52#usize 32#usize (by decide)))
    (JGo_TX2_MessageRead.range _ _ _ bytes51 (by decide)
      (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
      (by decide) selected51) native_parser51
#print axioms native_field51
theorem canonical51 : Port4C_QueryArithmetic.CanonE value51 := by
  change (342461162<2147483647 ∧ 52508543<2147483647 ∧ 1617583948<2147483647 ∧ 1438720280<2147483647) ∧
    (737938603<2147483647 ∧ 1775251747<2147483647 ∧ 573188763<2147483647 ∧ 1241048442<2147483647)
  omega
#print axioms canonical51
def bytes52 : Array U8 32#usize := ⟨JGe_Window31.c52,by rfl⟩
def value52 : AspisR1Stage2.Stage2Finish.E := ⟨⟨⟨666452909#u32,272507665#u32⟩,⟨220513222#u32,1636974922#u32⟩⟩,⟨⟨813992610#u32,1483813073#u32⟩,⟨1270873909#u32,123243228#u32⟩⟩⟩
def record52 : AspisR1RecordParser.field.wide_exact.WideExact := ⟨⟨⟨666452909#u32,272507665#u32⟩,⟨220513222#u32,1636974922#u32⟩⟩,⟨⟨813992610#u32,1483813073#u32⟩,⟨1270873909#u32,123243228#u32⟩⟩⟩
theorem selected52 : ((JFw_Frames.window 8007 2048).val.drop (32*52)).take 32=bytes52.val := by
  rw [JGo_TX2_MessageRead.cell 52 (by decide)]
  exact JGe_Window31.selected52
#print axioms selected52
theorem parser52 : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes52)=ok (some record52) := by
  apply (AspisR1.ExtractedRecordByteCanonicality.fixed_success_iff bytes52 record52).mpr
  constructor
  · intro j
    fin_cases j <;> decide
  · rfl
#print axioms parser52
theorem field52 : FIn_Primitives.field (JFw_Frames.window 8007 2048) 52#usize=ok value52 :=
  JGo_TX2_FieldRead.source _ _ bytes52 record52
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    selected52 parser52
#print axioms field52
theorem native_parser52 : FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes52)=ok (some (FIo_Install.toE value52)) := by
  with_unfolding_all rfl
#print axioms native_parser52
theorem native_field52 : FIo_Native.weights.field (JFw_Frames.window 8007 2048) 52#usize=
    ok (FIo_Install.toE value52) :=
  JGo_TX2_MessageRead.native _ 52#usize 1664#usize 53#usize 1696#usize bytes52 _
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 52#usize 32#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 52#usize 1#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 53#usize 32#usize (by decide)))
    (JGo_TX2_MessageRead.range _ _ _ bytes52 (by decide)
      (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
      (by decide) selected52) native_parser52
#print axioms native_field52
theorem canonical52 : Port4C_QueryArithmetic.CanonE value52 := by
  change (666452909<2147483647 ∧ 272507665<2147483647 ∧ 220513222<2147483647 ∧ 1636974922<2147483647) ∧
    (813992610<2147483647 ∧ 1483813073<2147483647 ∧ 1270873909<2147483647 ∧ 123243228<2147483647)
  omega
#print axioms canonical52
def bytes53 : Array U8 32#usize := ⟨JGe_Window31.c53,by rfl⟩
def value53 : AspisR1Stage2.Stage2Finish.E := ⟨⟨⟨559404803#u32,2031515979#u32⟩,⟨1436005354#u32,172593288#u32⟩⟩,⟨⟨2073730825#u32,2025225714#u32⟩,⟨1281679941#u32,219695768#u32⟩⟩⟩
def record53 : AspisR1RecordParser.field.wide_exact.WideExact := ⟨⟨⟨559404803#u32,2031515979#u32⟩,⟨1436005354#u32,172593288#u32⟩⟩,⟨⟨2073730825#u32,2025225714#u32⟩,⟨1281679941#u32,219695768#u32⟩⟩⟩
theorem selected53 : ((JFw_Frames.window 8007 2048).val.drop (32*53)).take 32=bytes53.val := by
  rw [JGo_TX2_MessageRead.cell 53 (by decide)]
  exact JGe_Window31.selected53
#print axioms selected53
theorem parser53 : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes53)=ok (some record53) := by
  apply (AspisR1.ExtractedRecordByteCanonicality.fixed_success_iff bytes53 record53).mpr
  constructor
  · intro j
    fin_cases j <;> decide
  · rfl
#print axioms parser53
theorem field53 : FIn_Primitives.field (JFw_Frames.window 8007 2048) 53#usize=ok value53 :=
  JGo_TX2_FieldRead.source _ _ bytes53 record53
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    selected53 parser53
#print axioms field53
theorem native_parser53 : FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes53)=ok (some (FIo_Install.toE value53)) := by
  with_unfolding_all rfl
#print axioms native_parser53
theorem native_field53 : FIo_Native.weights.field (JFw_Frames.window 8007 2048) 53#usize=
    ok (FIo_Install.toE value53) :=
  JGo_TX2_MessageRead.native _ 53#usize 1696#usize 54#usize 1728#usize bytes53 _
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 53#usize 32#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 53#usize 1#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 54#usize 32#usize (by decide)))
    (JGo_TX2_MessageRead.range _ _ _ bytes53 (by decide)
      (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
      (by decide) selected53) native_parser53
#print axioms native_field53
theorem canonical53 : Port4C_QueryArithmetic.CanonE value53 := by
  change (559404803<2147483647 ∧ 2031515979<2147483647 ∧ 1436005354<2147483647 ∧ 172593288<2147483647) ∧
    (2073730825<2147483647 ∧ 2025225714<2147483647 ∧ 1281679941<2147483647 ∧ 219695768<2147483647)
  omega
#print axioms canonical53
def bytes54 : Array U8 32#usize := ⟨JGe_Window31.c54,by rfl⟩
def value54 : AspisR1Stage2.Stage2Finish.E := ⟨⟨⟨785483966#u32,1304522432#u32⟩,⟨2060026665#u32,323975975#u32⟩⟩,⟨⟨973204756#u32,1110678174#u32⟩,⟨889140861#u32,75362730#u32⟩⟩⟩
def record54 : AspisR1RecordParser.field.wide_exact.WideExact := ⟨⟨⟨785483966#u32,1304522432#u32⟩,⟨2060026665#u32,323975975#u32⟩⟩,⟨⟨973204756#u32,1110678174#u32⟩,⟨889140861#u32,75362730#u32⟩⟩⟩
theorem selected54 : ((JFw_Frames.window 8007 2048).val.drop (32*54)).take 32=bytes54.val := by
  rw [JGo_TX2_MessageRead.cell 54 (by decide)]
  exact JGe_Window31.selected54
#print axioms selected54
theorem parser54 : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes54)=ok (some record54) := by
  apply (AspisR1.ExtractedRecordByteCanonicality.fixed_success_iff bytes54 record54).mpr
  constructor
  · intro j
    fin_cases j <;> decide
  · rfl
#print axioms parser54
theorem field54 : FIn_Primitives.field (JFw_Frames.window 8007 2048) 54#usize=ok value54 :=
  JGo_TX2_FieldRead.source _ _ bytes54 record54
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    selected54 parser54
#print axioms field54
theorem native_parser54 : FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes54)=ok (some (FIo_Install.toE value54)) := by
  with_unfolding_all rfl
#print axioms native_parser54
theorem native_field54 : FIo_Native.weights.field (JFw_Frames.window 8007 2048) 54#usize=
    ok (FIo_Install.toE value54) :=
  JGo_TX2_MessageRead.native _ 54#usize 1728#usize 55#usize 1760#usize bytes54 _
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 54#usize 32#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 54#usize 1#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 55#usize 32#usize (by decide)))
    (JGo_TX2_MessageRead.range _ _ _ bytes54 (by decide)
      (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
      (by decide) selected54) native_parser54
#print axioms native_field54
theorem canonical54 : Port4C_QueryArithmetic.CanonE value54 := by
  change (785483966<2147483647 ∧ 1304522432<2147483647 ∧ 2060026665<2147483647 ∧ 323975975<2147483647) ∧
    (973204756<2147483647 ∧ 1110678174<2147483647 ∧ 889140861<2147483647 ∧ 75362730<2147483647)
  omega
#print axioms canonical54
def bytes55 : Array U8 32#usize := ⟨JGe_Window31.c55,by rfl⟩
def value55 : AspisR1Stage2.Stage2Finish.E := ⟨⟨⟨951535709#u32,1860270958#u32⟩,⟨952737453#u32,516693692#u32⟩⟩,⟨⟨773862924#u32,1112125816#u32⟩,⟨1752194245#u32,1738765483#u32⟩⟩⟩
def record55 : AspisR1RecordParser.field.wide_exact.WideExact := ⟨⟨⟨951535709#u32,1860270958#u32⟩,⟨952737453#u32,516693692#u32⟩⟩,⟨⟨773862924#u32,1112125816#u32⟩,⟨1752194245#u32,1738765483#u32⟩⟩⟩
theorem selected55 : ((JFw_Frames.window 8007 2048).val.drop (32*55)).take 32=bytes55.val := by
  rw [JGo_TX2_MessageRead.cell 55 (by decide)]
  exact JGe_Window31.selected55
#print axioms selected55
theorem parser55 : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes55)=ok (some record55) := by
  apply (AspisR1.ExtractedRecordByteCanonicality.fixed_success_iff bytes55 record55).mpr
  constructor
  · intro j
    fin_cases j <;> decide
  · rfl
#print axioms parser55
theorem field55 : FIn_Primitives.field (JFw_Frames.window 8007 2048) 55#usize=ok value55 :=
  JGo_TX2_FieldRead.source _ _ bytes55 record55
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    selected55 parser55
#print axioms field55
theorem native_parser55 : FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes55)=ok (some (FIo_Install.toE value55)) := by
  with_unfolding_all rfl
#print axioms native_parser55
theorem native_field55 : FIo_Native.weights.field (JFw_Frames.window 8007 2048) 55#usize=
    ok (FIo_Install.toE value55) :=
  JGo_TX2_MessageRead.native _ 55#usize 1760#usize 56#usize 1792#usize bytes55 _
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 55#usize 32#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 55#usize 1#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 56#usize 32#usize (by decide)))
    (JGo_TX2_MessageRead.range _ _ _ bytes55 (by decide)
      (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
      (by decide) selected55) native_parser55
#print axioms native_field55
theorem canonical55 : Port4C_QueryArithmetic.CanonE value55 := by
  change (951535709<2147483647 ∧ 1860270958<2147483647 ∧ 952737453<2147483647 ∧ 516693692<2147483647) ∧
    (773862924<2147483647 ∧ 1112125816<2147483647 ∧ 1752194245<2147483647 ∧ 1738765483<2147483647)
  omega
#print axioms canonical55
end AspisR1.JGo_TX2_Message48
end
