import NDO_JGo_TX2_MessageRead
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGo_TX2_Message40
open Aeneas Aeneas.Std Result
attribute [local irreducible] JFx_NativeBytes.proof JFw_Frames.window
def bytes40 : Array U8 32#usize := ⟨JGe_Window31.c40,by rfl⟩
def value40 : AspisR1Stage2.Stage2Finish.E := ⟨⟨⟨790570480#u32,219200768#u32⟩,⟨462561962#u32,1843619953#u32⟩⟩,⟨⟨2107244903#u32,514216042#u32⟩,⟨1100525665#u32,1812021696#u32⟩⟩⟩
def record40 : AspisR1RecordParser.field.wide_exact.WideExact := ⟨⟨⟨790570480#u32,219200768#u32⟩,⟨462561962#u32,1843619953#u32⟩⟩,⟨⟨2107244903#u32,514216042#u32⟩,⟨1100525665#u32,1812021696#u32⟩⟩⟩
theorem selected40 : ((JFw_Frames.window 8007 2048).val.drop (32*40)).take 32=bytes40.val := by
  rw [JGo_TX2_MessageRead.cell 40 (by decide)]
  exact JGe_Window31.selected40
#print axioms selected40
theorem parser40 : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes40)=ok (some record40) := by
  apply (AspisR1.ExtractedRecordByteCanonicality.fixed_success_iff bytes40 record40).mpr
  constructor
  · intro j
    fin_cases j <;> decide
  · rfl
#print axioms parser40
theorem field40 : FIn_Primitives.field (JFw_Frames.window 8007 2048) 40#usize=ok value40 :=
  JGo_TX2_FieldRead.source _ _ bytes40 record40
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    selected40 parser40
#print axioms field40
theorem native_parser40 : FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes40)=ok (some (FIo_Install.toE value40)) := by
  with_unfolding_all rfl
#print axioms native_parser40
theorem native_field40 : FIo_Native.weights.field (JFw_Frames.window 8007 2048) 40#usize=
    ok (FIo_Install.toE value40) :=
  JGo_TX2_MessageRead.native _ 40#usize 1280#usize 41#usize 1312#usize bytes40 _
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 40#usize 32#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 40#usize 1#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 41#usize 32#usize (by decide)))
    (JGo_TX2_MessageRead.range _ _ _ bytes40 (by decide)
      (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
      (by decide) selected40) native_parser40
#print axioms native_field40
theorem canonical40 : Port4C_QueryArithmetic.CanonE value40 := by
  change (790570480<2147483647 ∧ 219200768<2147483647 ∧ 462561962<2147483647 ∧ 1843619953<2147483647) ∧
    (2107244903<2147483647 ∧ 514216042<2147483647 ∧ 1100525665<2147483647 ∧ 1812021696<2147483647)
  omega
#print axioms canonical40
def bytes41 : Array U8 32#usize := ⟨JGe_Window31.c41,by rfl⟩
def value41 : AspisR1Stage2.Stage2Finish.E := ⟨⟨⟨919011927#u32,1871771471#u32⟩,⟨1099254261#u32,909778935#u32⟩⟩,⟨⟨1922870376#u32,147361513#u32⟩,⟨363884687#u32,349877308#u32⟩⟩⟩
def record41 : AspisR1RecordParser.field.wide_exact.WideExact := ⟨⟨⟨919011927#u32,1871771471#u32⟩,⟨1099254261#u32,909778935#u32⟩⟩,⟨⟨1922870376#u32,147361513#u32⟩,⟨363884687#u32,349877308#u32⟩⟩⟩
theorem selected41 : ((JFw_Frames.window 8007 2048).val.drop (32*41)).take 32=bytes41.val := by
  rw [JGo_TX2_MessageRead.cell 41 (by decide)]
  exact JGe_Window31.selected41
#print axioms selected41
theorem parser41 : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes41)=ok (some record41) := by
  apply (AspisR1.ExtractedRecordByteCanonicality.fixed_success_iff bytes41 record41).mpr
  constructor
  · intro j
    fin_cases j <;> decide
  · rfl
#print axioms parser41
theorem field41 : FIn_Primitives.field (JFw_Frames.window 8007 2048) 41#usize=ok value41 :=
  JGo_TX2_FieldRead.source _ _ bytes41 record41
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    selected41 parser41
#print axioms field41
theorem native_parser41 : FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes41)=ok (some (FIo_Install.toE value41)) := by
  with_unfolding_all rfl
#print axioms native_parser41
theorem native_field41 : FIo_Native.weights.field (JFw_Frames.window 8007 2048) 41#usize=
    ok (FIo_Install.toE value41) :=
  JGo_TX2_MessageRead.native _ 41#usize 1312#usize 42#usize 1344#usize bytes41 _
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 41#usize 32#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 41#usize 1#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 42#usize 32#usize (by decide)))
    (JGo_TX2_MessageRead.range _ _ _ bytes41 (by decide)
      (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
      (by decide) selected41) native_parser41
#print axioms native_field41
theorem canonical41 : Port4C_QueryArithmetic.CanonE value41 := by
  change (919011927<2147483647 ∧ 1871771471<2147483647 ∧ 1099254261<2147483647 ∧ 909778935<2147483647) ∧
    (1922870376<2147483647 ∧ 147361513<2147483647 ∧ 363884687<2147483647 ∧ 349877308<2147483647)
  omega
#print axioms canonical41
def bytes42 : Array U8 32#usize := ⟨JGe_Window31.c42,by rfl⟩
def value42 : AspisR1Stage2.Stage2Finish.E := ⟨⟨⟨1372616450#u32,529700050#u32⟩,⟨114882864#u32,1670362872#u32⟩⟩,⟨⟨239256126#u32,1063211063#u32⟩,⟨697274631#u32,1874316071#u32⟩⟩⟩
def record42 : AspisR1RecordParser.field.wide_exact.WideExact := ⟨⟨⟨1372616450#u32,529700050#u32⟩,⟨114882864#u32,1670362872#u32⟩⟩,⟨⟨239256126#u32,1063211063#u32⟩,⟨697274631#u32,1874316071#u32⟩⟩⟩
theorem selected42 : ((JFw_Frames.window 8007 2048).val.drop (32*42)).take 32=bytes42.val := by
  rw [JGo_TX2_MessageRead.cell 42 (by decide)]
  exact JGe_Window31.selected42
#print axioms selected42
theorem parser42 : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes42)=ok (some record42) := by
  apply (AspisR1.ExtractedRecordByteCanonicality.fixed_success_iff bytes42 record42).mpr
  constructor
  · intro j
    fin_cases j <;> decide
  · rfl
#print axioms parser42
theorem field42 : FIn_Primitives.field (JFw_Frames.window 8007 2048) 42#usize=ok value42 :=
  JGo_TX2_FieldRead.source _ _ bytes42 record42
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    selected42 parser42
#print axioms field42
theorem native_parser42 : FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes42)=ok (some (FIo_Install.toE value42)) := by
  with_unfolding_all rfl
#print axioms native_parser42
theorem native_field42 : FIo_Native.weights.field (JFw_Frames.window 8007 2048) 42#usize=
    ok (FIo_Install.toE value42) :=
  JGo_TX2_MessageRead.native _ 42#usize 1344#usize 43#usize 1376#usize bytes42 _
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 42#usize 32#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 42#usize 1#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 43#usize 32#usize (by decide)))
    (JGo_TX2_MessageRead.range _ _ _ bytes42 (by decide)
      (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
      (by decide) selected42) native_parser42
#print axioms native_field42
theorem canonical42 : Port4C_QueryArithmetic.CanonE value42 := by
  change (1372616450<2147483647 ∧ 529700050<2147483647 ∧ 114882864<2147483647 ∧ 1670362872<2147483647) ∧
    (239256126<2147483647 ∧ 1063211063<2147483647 ∧ 697274631<2147483647 ∧ 1874316071<2147483647)
  omega
#print axioms canonical42
def bytes43 : Array U8 32#usize := ⟨JGe_Window31.c43,by rfl⟩
def value43 : AspisR1Stage2.Stage2Finish.E := ⟨⟨⟨446891492#u32,1731087542#u32⟩,⟨378956134#u32,1533275608#u32⟩⟩,⟨⟨1644276913#u32,1900033751#u32⟩,⟨1670251036#u32,405415897#u32⟩⟩⟩
def record43 : AspisR1RecordParser.field.wide_exact.WideExact := ⟨⟨⟨446891492#u32,1731087542#u32⟩,⟨378956134#u32,1533275608#u32⟩⟩,⟨⟨1644276913#u32,1900033751#u32⟩,⟨1670251036#u32,405415897#u32⟩⟩⟩
theorem selected43 : ((JFw_Frames.window 8007 2048).val.drop (32*43)).take 32=bytes43.val := by
  rw [JGo_TX2_MessageRead.cell 43 (by decide)]
  exact JGe_Window31.selected43
#print axioms selected43
theorem parser43 : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes43)=ok (some record43) := by
  apply (AspisR1.ExtractedRecordByteCanonicality.fixed_success_iff bytes43 record43).mpr
  constructor
  · intro j
    fin_cases j <;> decide
  · rfl
#print axioms parser43
theorem field43 : FIn_Primitives.field (JFw_Frames.window 8007 2048) 43#usize=ok value43 :=
  JGo_TX2_FieldRead.source _ _ bytes43 record43
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    selected43 parser43
#print axioms field43
theorem native_parser43 : FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes43)=ok (some (FIo_Install.toE value43)) := by
  with_unfolding_all rfl
#print axioms native_parser43
theorem native_field43 : FIo_Native.weights.field (JFw_Frames.window 8007 2048) 43#usize=
    ok (FIo_Install.toE value43) :=
  JGo_TX2_MessageRead.native _ 43#usize 1376#usize 44#usize 1408#usize bytes43 _
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 43#usize 32#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 43#usize 1#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 44#usize 32#usize (by decide)))
    (JGo_TX2_MessageRead.range _ _ _ bytes43 (by decide)
      (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
      (by decide) selected43) native_parser43
#print axioms native_field43
theorem canonical43 : Port4C_QueryArithmetic.CanonE value43 := by
  change (446891492<2147483647 ∧ 1731087542<2147483647 ∧ 378956134<2147483647 ∧ 1533275608<2147483647) ∧
    (1644276913<2147483647 ∧ 1900033751<2147483647 ∧ 1670251036<2147483647 ∧ 405415897<2147483647)
  omega
#print axioms canonical43
def bytes44 : Array U8 32#usize := ⟨JGe_Window31.c44,by rfl⟩
def value44 : AspisR1Stage2.Stage2Finish.E := ⟨⟨⟨1836012335#u32,1906272314#u32⟩,⟨1904484434#u32,1654362153#u32⟩⟩,⟨⟨1839473335#u32,1020050415#u32⟩,⟨1314027932#u32,329265619#u32⟩⟩⟩
def record44 : AspisR1RecordParser.field.wide_exact.WideExact := ⟨⟨⟨1836012335#u32,1906272314#u32⟩,⟨1904484434#u32,1654362153#u32⟩⟩,⟨⟨1839473335#u32,1020050415#u32⟩,⟨1314027932#u32,329265619#u32⟩⟩⟩
theorem selected44 : ((JFw_Frames.window 8007 2048).val.drop (32*44)).take 32=bytes44.val := by
  rw [JGo_TX2_MessageRead.cell 44 (by decide)]
  exact JGe_Window31.selected44
#print axioms selected44
theorem parser44 : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes44)=ok (some record44) := by
  apply (AspisR1.ExtractedRecordByteCanonicality.fixed_success_iff bytes44 record44).mpr
  constructor
  · intro j
    fin_cases j <;> decide
  · rfl
#print axioms parser44
theorem field44 : FIn_Primitives.field (JFw_Frames.window 8007 2048) 44#usize=ok value44 :=
  JGo_TX2_FieldRead.source _ _ bytes44 record44
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    selected44 parser44
#print axioms field44
theorem native_parser44 : FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes44)=ok (some (FIo_Install.toE value44)) := by
  with_unfolding_all rfl
#print axioms native_parser44
theorem native_field44 : FIo_Native.weights.field (JFw_Frames.window 8007 2048) 44#usize=
    ok (FIo_Install.toE value44) :=
  JGo_TX2_MessageRead.native _ 44#usize 1408#usize 45#usize 1440#usize bytes44 _
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 44#usize 32#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 44#usize 1#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 45#usize 32#usize (by decide)))
    (JGo_TX2_MessageRead.range _ _ _ bytes44 (by decide)
      (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
      (by decide) selected44) native_parser44
#print axioms native_field44
theorem canonical44 : Port4C_QueryArithmetic.CanonE value44 := by
  change (1836012335<2147483647 ∧ 1906272314<2147483647 ∧ 1904484434<2147483647 ∧ 1654362153<2147483647) ∧
    (1839473335<2147483647 ∧ 1020050415<2147483647 ∧ 1314027932<2147483647 ∧ 329265619<2147483647)
  omega
#print axioms canonical44
def bytes45 : Array U8 32#usize := ⟨JGe_Window31.c45,by rfl⟩
def value45 : AspisR1Stage2.Stage2Finish.E := ⟨⟨⟨481295334#u32,201055000#u32⟩,⟨704899282#u32,385236334#u32⟩⟩,⟨⟨191433757#u32,520918083#u32⟩,⟨1218731927#u32,1430173338#u32⟩⟩⟩
def record45 : AspisR1RecordParser.field.wide_exact.WideExact := ⟨⟨⟨481295334#u32,201055000#u32⟩,⟨704899282#u32,385236334#u32⟩⟩,⟨⟨191433757#u32,520918083#u32⟩,⟨1218731927#u32,1430173338#u32⟩⟩⟩
theorem selected45 : ((JFw_Frames.window 8007 2048).val.drop (32*45)).take 32=bytes45.val := by
  rw [JGo_TX2_MessageRead.cell 45 (by decide)]
  exact JGe_Window31.selected45
#print axioms selected45
theorem parser45 : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes45)=ok (some record45) := by
  apply (AspisR1.ExtractedRecordByteCanonicality.fixed_success_iff bytes45 record45).mpr
  constructor
  · intro j
    fin_cases j <;> decide
  · rfl
#print axioms parser45
theorem field45 : FIn_Primitives.field (JFw_Frames.window 8007 2048) 45#usize=ok value45 :=
  JGo_TX2_FieldRead.source _ _ bytes45 record45
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    selected45 parser45
#print axioms field45
theorem native_parser45 : FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes45)=ok (some (FIo_Install.toE value45)) := by
  with_unfolding_all rfl
#print axioms native_parser45
theorem native_field45 : FIo_Native.weights.field (JFw_Frames.window 8007 2048) 45#usize=
    ok (FIo_Install.toE value45) :=
  JGo_TX2_MessageRead.native _ 45#usize 1440#usize 46#usize 1472#usize bytes45 _
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 45#usize 32#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 45#usize 1#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 46#usize 32#usize (by decide)))
    (JGo_TX2_MessageRead.range _ _ _ bytes45 (by decide)
      (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
      (by decide) selected45) native_parser45
#print axioms native_field45
theorem canonical45 : Port4C_QueryArithmetic.CanonE value45 := by
  change (481295334<2147483647 ∧ 201055000<2147483647 ∧ 704899282<2147483647 ∧ 385236334<2147483647) ∧
    (191433757<2147483647 ∧ 520918083<2147483647 ∧ 1218731927<2147483647 ∧ 1430173338<2147483647)
  omega
#print axioms canonical45
def bytes46 : Array U8 32#usize := ⟨JGe_Window31.c46,by rfl⟩
def value46 : AspisR1Stage2.Stage2Finish.E := ⟨⟨⟨53596331#u32,893649387#u32⟩,⟨1813445464#u32,1850392263#u32⟩⟩,⟨⟨882889095#u32,138073354#u32⟩,⟨611690320#u32,2037159381#u32⟩⟩⟩
def record46 : AspisR1RecordParser.field.wide_exact.WideExact := ⟨⟨⟨53596331#u32,893649387#u32⟩,⟨1813445464#u32,1850392263#u32⟩⟩,⟨⟨882889095#u32,138073354#u32⟩,⟨611690320#u32,2037159381#u32⟩⟩⟩
theorem selected46 : ((JFw_Frames.window 8007 2048).val.drop (32*46)).take 32=bytes46.val := by
  rw [JGo_TX2_MessageRead.cell 46 (by decide)]
  exact JGe_Window31.selected46
#print axioms selected46
theorem parser46 : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes46)=ok (some record46) := by
  apply (AspisR1.ExtractedRecordByteCanonicality.fixed_success_iff bytes46 record46).mpr
  constructor
  · intro j
    fin_cases j <;> decide
  · rfl
#print axioms parser46
theorem field46 : FIn_Primitives.field (JFw_Frames.window 8007 2048) 46#usize=ok value46 :=
  JGo_TX2_FieldRead.source _ _ bytes46 record46
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    selected46 parser46
#print axioms field46
theorem native_parser46 : FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes46)=ok (some (FIo_Install.toE value46)) := by
  with_unfolding_all rfl
#print axioms native_parser46
theorem native_field46 : FIo_Native.weights.field (JFw_Frames.window 8007 2048) 46#usize=
    ok (FIo_Install.toE value46) :=
  JGo_TX2_MessageRead.native _ 46#usize 1472#usize 47#usize 1504#usize bytes46 _
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 46#usize 32#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 46#usize 1#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 47#usize 32#usize (by decide)))
    (JGo_TX2_MessageRead.range _ _ _ bytes46 (by decide)
      (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
      (by decide) selected46) native_parser46
#print axioms native_field46
theorem canonical46 : Port4C_QueryArithmetic.CanonE value46 := by
  change (53596331<2147483647 ∧ 893649387<2147483647 ∧ 1813445464<2147483647 ∧ 1850392263<2147483647) ∧
    (882889095<2147483647 ∧ 138073354<2147483647 ∧ 611690320<2147483647 ∧ 2037159381<2147483647)
  omega
#print axioms canonical46
def bytes47 : Array U8 32#usize := ⟨JGe_Window31.c47,by rfl⟩
def value47 : AspisR1Stage2.Stage2Finish.E := ⟨⟨⟨853783811#u32,663291036#u32⟩,⟨1602982907#u32,99372094#u32⟩⟩,⟨⟨1611570596#u32,1247076493#u32⟩,⟨1083169497#u32,1834836613#u32⟩⟩⟩
def record47 : AspisR1RecordParser.field.wide_exact.WideExact := ⟨⟨⟨853783811#u32,663291036#u32⟩,⟨1602982907#u32,99372094#u32⟩⟩,⟨⟨1611570596#u32,1247076493#u32⟩,⟨1083169497#u32,1834836613#u32⟩⟩⟩
theorem selected47 : ((JFw_Frames.window 8007 2048).val.drop (32*47)).take 32=bytes47.val := by
  rw [JGo_TX2_MessageRead.cell 47 (by decide)]
  exact JGe_Window31.selected47
#print axioms selected47
theorem parser47 : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes47)=ok (some record47) := by
  apply (AspisR1.ExtractedRecordByteCanonicality.fixed_success_iff bytes47 record47).mpr
  constructor
  · intro j
    fin_cases j <;> decide
  · rfl
#print axioms parser47
theorem field47 : FIn_Primitives.field (JFw_Frames.window 8007 2048) 47#usize=ok value47 :=
  JGo_TX2_FieldRead.source _ _ bytes47 record47
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
    selected47 parser47
#print axioms field47
theorem native_parser47 : FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes
    (Array.to_slice bytes47)=ok (some (FIo_Install.toE value47)) := by
  with_unfolding_all rfl
#print axioms native_parser47
theorem native_field47 : FIo_Native.weights.field (JFw_Frames.window 8007 2048) 47#usize=
    ok (FIo_Install.toE value47) :=
  JGo_TX2_MessageRead.native _ 47#usize 1504#usize 48#usize 1536#usize bytes47 _
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 47#usize 32#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 47#usize 1#usize (by decide)))
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 48#usize 32#usize (by decide)))
    (JGo_TX2_MessageRead.range _ _ _ bytes47 (by decide)
      (by rw [JFw_Frames.window_length 8007 2048 (by decide)];decide)
      (by decide) selected47) native_parser47
#print axioms native_field47
theorem canonical47 : Port4C_QueryArithmetic.CanonE value47 := by
  change (853783811<2147483647 ∧ 663291036<2147483647 ∧ 1602982907<2147483647 ∧ 99372094<2147483647) ∧
    (1611570596<2147483647 ∧ 1247076493<2147483647 ∧ 1083169497<2147483647 ∧ 1834836613<2147483647)
  omega
#print axioms canonical47
end AspisR1.JGo_TX2_Message40
end
