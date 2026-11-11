import NDO_JFr_Data03
import NDO_JFr_EncodedCell
import NDO_JFz_Scan51
set_option autoImplicit false
namespace AspisR1.JFr_Bytes03
open Aeneas Aeneas.Std Result RetainedFieldByteCodec
open AspisR1PublicPreparation
open AspisS1ExtractedRoundChildren
def raw : List U8 := JFz_Scan51.data
theorem rawLength : raw.length=448 := JFz_Scan51.length
#print axioms rawLength
theorem selected : (JFx_NativeBytes.proof.val.drop 1535).take 448=raw := JFz_Scan51.selected
#print axioms selected
def cell00 : Array U8 16#usize := ⟨[2#u8,82#u8,238#u8,68#u8,10#u8,84#u8,218#u8,24#u8,120#u8,108#u8,24#u8,82#u8,180#u8,9#u8,223#u8,33#u8],by rfl⟩
def limbs00 : QM31Limbs := ![⟨1156469250,by change 1156469250<2147483647;omega⟩,⟨416961546,by change 416961546<2147483647;omega⟩,⟨1377332344,by change 1377332344<2147483647;omega⟩,⟨568265140,by change 568265140<2147483647;omega⟩]
theorem rawCell00 : (raw.drop 0).take 16=cell00.val := by
  simp only [raw,JFz_Scan51.data,JFz_Scan51.j00,JFz_Scan51.j01,JFz_Scan51.j02,JFz_Scan51.j03,JFz_Scan51.j04,JFz_Scan51.j05,JFz_Scan51.j06,JFz_Scan51.j07,JFz_Scan51.j08,JFz_Scan51.j09,JFz_Scan51.j10,JFz_Scan51.j11,JFz_Scan51.j12,JFz_Scan51.b00_length,JFz_Scan51.b01_length,JFz_Scan51.b02_length,JFz_Scan51.b03_length,JFz_Scan51.b04_length,JFz_Scan51.b05_length,JFz_Scan51.b06_length,JFz_Scan51.b07_length,JFz_Scan51.b08_length,JFz_Scan51.b09_length,JFz_Scan51.b10_length,JFz_Scan51.b11_length,JFz_Scan51.b12_length,JFz_Scan51.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell00
theorem encoded00 : CandidateParserByteOrder.arrayBytes16 cell00=encodeQM31LE limbs00 := by
  funext i
  fin_cases i <;> rfl
theorem parser00 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell00)=
    ok (some ⟨⟨1156469250#u32,416961546#u32⟩,⟨1377332344#u32,568265140#u32⟩⟩) :=
  JFr_EncodedCell.parser cell00 limbs00 encoded00
#print axioms encoded00
#print axioms parser00
def cell01 : Array U8 16#usize := ⟨[185#u8,82#u8,64#u8,58#u8,153#u8,111#u8,254#u8,67#u8,149#u8,62#u8,181#u8,72#u8,53#u8,58#u8,2#u8,85#u8],by rfl⟩
def limbs01 : QM31Limbs := ![⟨977294009,by change 977294009<2147483647;omega⟩,⟨1140748185,by change 1140748185<2147483647;omega⟩,⟨1219837589,by change 1219837589<2147483647;omega⟩,⟨1426209333,by change 1426209333<2147483647;omega⟩]
theorem rawCell01 : (raw.drop 16).take 16=cell01.val := by
  simp only [raw,JFz_Scan51.data,JFz_Scan51.j00,JFz_Scan51.j01,JFz_Scan51.j02,JFz_Scan51.j03,JFz_Scan51.j04,JFz_Scan51.j05,JFz_Scan51.j06,JFz_Scan51.j07,JFz_Scan51.j08,JFz_Scan51.j09,JFz_Scan51.j10,JFz_Scan51.j11,JFz_Scan51.j12,JFz_Scan51.b00_length,JFz_Scan51.b01_length,JFz_Scan51.b02_length,JFz_Scan51.b03_length,JFz_Scan51.b04_length,JFz_Scan51.b05_length,JFz_Scan51.b06_length,JFz_Scan51.b07_length,JFz_Scan51.b08_length,JFz_Scan51.b09_length,JFz_Scan51.b10_length,JFz_Scan51.b11_length,JFz_Scan51.b12_length,JFz_Scan51.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell01
theorem encoded01 : CandidateParserByteOrder.arrayBytes16 cell01=encodeQM31LE limbs01 := by
  funext i
  fin_cases i <;> rfl
theorem parser01 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell01)=
    ok (some ⟨⟨977294009#u32,1140748185#u32⟩,⟨1219837589#u32,1426209333#u32⟩⟩) :=
  JFr_EncodedCell.parser cell01 limbs01 encoded01
#print axioms encoded01
#print axioms parser01
def cell02 : Array U8 16#usize := ⟨[148#u8,43#u8,49#u8,79#u8,244#u8,119#u8,160#u8,104#u8,114#u8,203#u8,73#u8,30#u8,251#u8,253#u8,35#u8,127#u8],by rfl⟩
def limbs02 : QM31Limbs := ![⟨1328622484,by change 1328622484<2147483647;omega⟩,⟨1755346932,by change 1755346932<2147483647;omega⟩,⟨508152690,by change 508152690<2147483647;omega⟩,⟨2133065211,by change 2133065211<2147483647;omega⟩]
theorem rawCell02 : (raw.drop 32).take 16=cell02.val := by
  simp only [raw,JFz_Scan51.data,JFz_Scan51.j00,JFz_Scan51.j01,JFz_Scan51.j02,JFz_Scan51.j03,JFz_Scan51.j04,JFz_Scan51.j05,JFz_Scan51.j06,JFz_Scan51.j07,JFz_Scan51.j08,JFz_Scan51.j09,JFz_Scan51.j10,JFz_Scan51.j11,JFz_Scan51.j12,JFz_Scan51.b00_length,JFz_Scan51.b01_length,JFz_Scan51.b02_length,JFz_Scan51.b03_length,JFz_Scan51.b04_length,JFz_Scan51.b05_length,JFz_Scan51.b06_length,JFz_Scan51.b07_length,JFz_Scan51.b08_length,JFz_Scan51.b09_length,JFz_Scan51.b10_length,JFz_Scan51.b11_length,JFz_Scan51.b12_length,JFz_Scan51.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell02
theorem encoded02 : CandidateParserByteOrder.arrayBytes16 cell02=encodeQM31LE limbs02 := by
  funext i
  fin_cases i <;> rfl
theorem parser02 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell02)=
    ok (some ⟨⟨1328622484#u32,1755346932#u32⟩,⟨508152690#u32,2133065211#u32⟩⟩) :=
  JFr_EncodedCell.parser cell02 limbs02 encoded02
#print axioms encoded02
#print axioms parser02
def cell03 : Array U8 16#usize := ⟨[117#u8,234#u8,107#u8,105#u8,98#u8,8#u8,114#u8,30#u8,167#u8,162#u8,154#u8,75#u8,162#u8,159#u8,235#u8,18#u8],by rfl⟩
def limbs03 : QM31Limbs := ![⟨1768680053,by change 1768680053<2147483647;omega⟩,⟨510789730,by change 510789730<2147483647;omega⟩,⟨1268425383,by change 1268425383<2147483647;omega⟩,⟨317431714,by change 317431714<2147483647;omega⟩]
theorem rawCell03 : (raw.drop 48).take 16=cell03.val := by
  simp only [raw,JFz_Scan51.data,JFz_Scan51.j00,JFz_Scan51.j01,JFz_Scan51.j02,JFz_Scan51.j03,JFz_Scan51.j04,JFz_Scan51.j05,JFz_Scan51.j06,JFz_Scan51.j07,JFz_Scan51.j08,JFz_Scan51.j09,JFz_Scan51.j10,JFz_Scan51.j11,JFz_Scan51.j12,JFz_Scan51.b00_length,JFz_Scan51.b01_length,JFz_Scan51.b02_length,JFz_Scan51.b03_length,JFz_Scan51.b04_length,JFz_Scan51.b05_length,JFz_Scan51.b06_length,JFz_Scan51.b07_length,JFz_Scan51.b08_length,JFz_Scan51.b09_length,JFz_Scan51.b10_length,JFz_Scan51.b11_length,JFz_Scan51.b12_length,JFz_Scan51.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell03
theorem encoded03 : CandidateParserByteOrder.arrayBytes16 cell03=encodeQM31LE limbs03 := by
  funext i
  fin_cases i <;> rfl
theorem parser03 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell03)=
    ok (some ⟨⟨1768680053#u32,510789730#u32⟩,⟨1268425383#u32,317431714#u32⟩⟩) :=
  JFr_EncodedCell.parser cell03 limbs03 encoded03
#print axioms encoded03
#print axioms parser03
def cell04 : Array U8 16#usize := ⟨[111#u8,172#u8,52#u8,16#u8,27#u8,221#u8,17#u8,96#u8,104#u8,5#u8,158#u8,56#u8,4#u8,236#u8,179#u8,73#u8],by rfl⟩
def limbs04 : QM31Limbs := ![⟨271887471,by change 271887471<2147483647;omega⟩,⟨1611783451,by change 1611783451<2147483647;omega⟩,⟨949880168,by change 949880168<2147483647;omega⟩,⟨1236528132,by change 1236528132<2147483647;omega⟩]
theorem rawCell04 : (raw.drop 64).take 16=cell04.val := by
  simp only [raw,JFz_Scan51.data,JFz_Scan51.j00,JFz_Scan51.j01,JFz_Scan51.j02,JFz_Scan51.j03,JFz_Scan51.j04,JFz_Scan51.j05,JFz_Scan51.j06,JFz_Scan51.j07,JFz_Scan51.j08,JFz_Scan51.j09,JFz_Scan51.j10,JFz_Scan51.j11,JFz_Scan51.j12,JFz_Scan51.b00_length,JFz_Scan51.b01_length,JFz_Scan51.b02_length,JFz_Scan51.b03_length,JFz_Scan51.b04_length,JFz_Scan51.b05_length,JFz_Scan51.b06_length,JFz_Scan51.b07_length,JFz_Scan51.b08_length,JFz_Scan51.b09_length,JFz_Scan51.b10_length,JFz_Scan51.b11_length,JFz_Scan51.b12_length,JFz_Scan51.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell04
theorem encoded04 : CandidateParserByteOrder.arrayBytes16 cell04=encodeQM31LE limbs04 := by
  funext i
  fin_cases i <;> rfl
theorem parser04 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell04)=
    ok (some ⟨⟨271887471#u32,1611783451#u32⟩,⟨949880168#u32,1236528132#u32⟩⟩) :=
  JFr_EncodedCell.parser cell04 limbs04 encoded04
#print axioms encoded04
#print axioms parser04
def cell05 : Array U8 16#usize := ⟨[116#u8,90#u8,91#u8,60#u8,1#u8,24#u8,79#u8,96#u8,45#u8,253#u8,234#u8,43#u8,7#u8,129#u8,27#u8,114#u8],by rfl⟩
def limbs05 : QM31Limbs := ![⟨1012619892,by change 1012619892<2147483647;omega⟩,⟨1615796225,by change 1615796225<2147483647;omega⟩,⟨736820525,by change 736820525<2147483647;omega⟩,⟨1914405127,by change 1914405127<2147483647;omega⟩]
theorem rawCell05 : (raw.drop 80).take 16=cell05.val := by
  simp only [raw,JFz_Scan51.data,JFz_Scan51.j00,JFz_Scan51.j01,JFz_Scan51.j02,JFz_Scan51.j03,JFz_Scan51.j04,JFz_Scan51.j05,JFz_Scan51.j06,JFz_Scan51.j07,JFz_Scan51.j08,JFz_Scan51.j09,JFz_Scan51.j10,JFz_Scan51.j11,JFz_Scan51.j12,JFz_Scan51.b00_length,JFz_Scan51.b01_length,JFz_Scan51.b02_length,JFz_Scan51.b03_length,JFz_Scan51.b04_length,JFz_Scan51.b05_length,JFz_Scan51.b06_length,JFz_Scan51.b07_length,JFz_Scan51.b08_length,JFz_Scan51.b09_length,JFz_Scan51.b10_length,JFz_Scan51.b11_length,JFz_Scan51.b12_length,JFz_Scan51.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell05
theorem encoded05 : CandidateParserByteOrder.arrayBytes16 cell05=encodeQM31LE limbs05 := by
  funext i
  fin_cases i <;> rfl
theorem parser05 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell05)=
    ok (some ⟨⟨1012619892#u32,1615796225#u32⟩,⟨736820525#u32,1914405127#u32⟩⟩) :=
  JFr_EncodedCell.parser cell05 limbs05 encoded05
#print axioms encoded05
#print axioms parser05
def cell06 : Array U8 16#usize := ⟨[90#u8,156#u8,224#u8,91#u8,79#u8,179#u8,247#u8,53#u8,8#u8,138#u8,240#u8,59#u8,153#u8,166#u8,93#u8,27#u8],by rfl⟩
def limbs06 : QM31Limbs := ![⟨1541446746,by change 1541446746<2147483647;omega⟩,⟨905425743,by change 905425743<2147483647;omega⟩,⟨1005619720,by change 1005619720<2147483647;omega⟩,⟨459122329,by change 459122329<2147483647;omega⟩]
theorem rawCell06 : (raw.drop 96).take 16=cell06.val := by
  simp only [raw,JFz_Scan51.data,JFz_Scan51.j00,JFz_Scan51.j01,JFz_Scan51.j02,JFz_Scan51.j03,JFz_Scan51.j04,JFz_Scan51.j05,JFz_Scan51.j06,JFz_Scan51.j07,JFz_Scan51.j08,JFz_Scan51.j09,JFz_Scan51.j10,JFz_Scan51.j11,JFz_Scan51.j12,JFz_Scan51.b00_length,JFz_Scan51.b01_length,JFz_Scan51.b02_length,JFz_Scan51.b03_length,JFz_Scan51.b04_length,JFz_Scan51.b05_length,JFz_Scan51.b06_length,JFz_Scan51.b07_length,JFz_Scan51.b08_length,JFz_Scan51.b09_length,JFz_Scan51.b10_length,JFz_Scan51.b11_length,JFz_Scan51.b12_length,JFz_Scan51.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell06
theorem encoded06 : CandidateParserByteOrder.arrayBytes16 cell06=encodeQM31LE limbs06 := by
  funext i
  fin_cases i <;> rfl
theorem parser06 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell06)=
    ok (some ⟨⟨1541446746#u32,905425743#u32⟩,⟨1005619720#u32,459122329#u32⟩⟩) :=
  JFr_EncodedCell.parser cell06 limbs06 encoded06
#print axioms encoded06
#print axioms parser06
def cell07 : Array U8 16#usize := ⟨[121#u8,14#u8,190#u8,120#u8,34#u8,155#u8,124#u8,56#u8,43#u8,131#u8,208#u8,11#u8,1#u8,18#u8,209#u8,87#u8],by rfl⟩
def limbs07 : QM31Limbs := ![⟨2025721465,by change 2025721465<2147483647;omega⟩,⟨947690274,by change 947690274<2147483647;omega⟩,⟨198214443,by change 198214443<2147483647;omega⟩,⟨1473319425,by change 1473319425<2147483647;omega⟩]
theorem rawCell07 : (raw.drop 112).take 16=cell07.val := by
  simp only [raw,JFz_Scan51.data,JFz_Scan51.j00,JFz_Scan51.j01,JFz_Scan51.j02,JFz_Scan51.j03,JFz_Scan51.j04,JFz_Scan51.j05,JFz_Scan51.j06,JFz_Scan51.j07,JFz_Scan51.j08,JFz_Scan51.j09,JFz_Scan51.j10,JFz_Scan51.j11,JFz_Scan51.j12,JFz_Scan51.b00_length,JFz_Scan51.b01_length,JFz_Scan51.b02_length,JFz_Scan51.b03_length,JFz_Scan51.b04_length,JFz_Scan51.b05_length,JFz_Scan51.b06_length,JFz_Scan51.b07_length,JFz_Scan51.b08_length,JFz_Scan51.b09_length,JFz_Scan51.b10_length,JFz_Scan51.b11_length,JFz_Scan51.b12_length,JFz_Scan51.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell07
theorem encoded07 : CandidateParserByteOrder.arrayBytes16 cell07=encodeQM31LE limbs07 := by
  funext i
  fin_cases i <;> rfl
theorem parser07 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell07)=
    ok (some ⟨⟨2025721465#u32,947690274#u32⟩,⟨198214443#u32,1473319425#u32⟩⟩) :=
  JFr_EncodedCell.parser cell07 limbs07 encoded07
#print axioms encoded07
#print axioms parser07
def cell08 : Array U8 16#usize := ⟨[164#u8,222#u8,182#u8,111#u8,43#u8,233#u8,186#u8,120#u8,228#u8,71#u8,190#u8,34#u8,34#u8,240#u8,26#u8,77#u8],by rfl⟩
def limbs08 : QM31Limbs := ![⟨1874255524,by change 1874255524<2147483647;omega⟩,⟨2025515307,by change 2025515307<2147483647;omega⟩,⟨582895588,by change 582895588<2147483647;omega⟩,⟨1293611042,by change 1293611042<2147483647;omega⟩]
theorem rawCell08 : (raw.drop 128).take 16=cell08.val := by
  simp only [raw,JFz_Scan51.data,JFz_Scan51.j00,JFz_Scan51.j01,JFz_Scan51.j02,JFz_Scan51.j03,JFz_Scan51.j04,JFz_Scan51.j05,JFz_Scan51.j06,JFz_Scan51.j07,JFz_Scan51.j08,JFz_Scan51.j09,JFz_Scan51.j10,JFz_Scan51.j11,JFz_Scan51.j12,JFz_Scan51.b00_length,JFz_Scan51.b01_length,JFz_Scan51.b02_length,JFz_Scan51.b03_length,JFz_Scan51.b04_length,JFz_Scan51.b05_length,JFz_Scan51.b06_length,JFz_Scan51.b07_length,JFz_Scan51.b08_length,JFz_Scan51.b09_length,JFz_Scan51.b10_length,JFz_Scan51.b11_length,JFz_Scan51.b12_length,JFz_Scan51.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell08
theorem encoded08 : CandidateParserByteOrder.arrayBytes16 cell08=encodeQM31LE limbs08 := by
  funext i
  fin_cases i <;> rfl
theorem parser08 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell08)=
    ok (some ⟨⟨1874255524#u32,2025515307#u32⟩,⟨582895588#u32,1293611042#u32⟩⟩) :=
  JFr_EncodedCell.parser cell08 limbs08 encoded08
#print axioms encoded08
#print axioms parser08
def cell09 : Array U8 16#usize := ⟨[4#u8,82#u8,72#u8,26#u8,254#u8,171#u8,128#u8,89#u8,220#u8,182#u8,233#u8,54#u8,41#u8,238#u8,13#u8,46#u8],by rfl⟩
def limbs09 : QM31Limbs := ![⟨440947204,by change 440947204<2147483647;omega⟩,⟨1501604862,by change 1501604862<2147483647;omega⟩,⟨921286364,by change 921286364<2147483647;omega⟩,⟨772664873,by change 772664873<2147483647;omega⟩]
theorem rawCell09 : (raw.drop 144).take 16=cell09.val := by
  simp only [raw,JFz_Scan51.data,JFz_Scan51.j00,JFz_Scan51.j01,JFz_Scan51.j02,JFz_Scan51.j03,JFz_Scan51.j04,JFz_Scan51.j05,JFz_Scan51.j06,JFz_Scan51.j07,JFz_Scan51.j08,JFz_Scan51.j09,JFz_Scan51.j10,JFz_Scan51.j11,JFz_Scan51.j12,JFz_Scan51.b00_length,JFz_Scan51.b01_length,JFz_Scan51.b02_length,JFz_Scan51.b03_length,JFz_Scan51.b04_length,JFz_Scan51.b05_length,JFz_Scan51.b06_length,JFz_Scan51.b07_length,JFz_Scan51.b08_length,JFz_Scan51.b09_length,JFz_Scan51.b10_length,JFz_Scan51.b11_length,JFz_Scan51.b12_length,JFz_Scan51.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell09
theorem encoded09 : CandidateParserByteOrder.arrayBytes16 cell09=encodeQM31LE limbs09 := by
  funext i
  fin_cases i <;> rfl
theorem parser09 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell09)=
    ok (some ⟨⟨440947204#u32,1501604862#u32⟩,⟨921286364#u32,772664873#u32⟩⟩) :=
  JFr_EncodedCell.parser cell09 limbs09 encoded09
#print axioms encoded09
#print axioms parser09
def cell10 : Array U8 16#usize := ⟨[118#u8,208#u8,34#u8,36#u8,23#u8,39#u8,119#u8,107#u8,40#u8,53#u8,128#u8,14#u8,47#u8,38#u8,94#u8,15#u8],by rfl⟩
def limbs10 : QM31Limbs := ![⟨606261366,by change 606261366<2147483647;omega⟩,⟨1802970903,by change 1802970903<2147483647;omega⟩,⟨243283240,by change 243283240<2147483647;omega⟩,⟨257828399,by change 257828399<2147483647;omega⟩]
theorem rawCell10 : (raw.drop 160).take 16=cell10.val := by
  simp only [raw,JFz_Scan51.data,JFz_Scan51.j00,JFz_Scan51.j01,JFz_Scan51.j02,JFz_Scan51.j03,JFz_Scan51.j04,JFz_Scan51.j05,JFz_Scan51.j06,JFz_Scan51.j07,JFz_Scan51.j08,JFz_Scan51.j09,JFz_Scan51.j10,JFz_Scan51.j11,JFz_Scan51.j12,JFz_Scan51.b00_length,JFz_Scan51.b01_length,JFz_Scan51.b02_length,JFz_Scan51.b03_length,JFz_Scan51.b04_length,JFz_Scan51.b05_length,JFz_Scan51.b06_length,JFz_Scan51.b07_length,JFz_Scan51.b08_length,JFz_Scan51.b09_length,JFz_Scan51.b10_length,JFz_Scan51.b11_length,JFz_Scan51.b12_length,JFz_Scan51.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell10
theorem encoded10 : CandidateParserByteOrder.arrayBytes16 cell10=encodeQM31LE limbs10 := by
  funext i
  fin_cases i <;> rfl
theorem parser10 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell10)=
    ok (some ⟨⟨606261366#u32,1802970903#u32⟩,⟨243283240#u32,257828399#u32⟩⟩) :=
  JFr_EncodedCell.parser cell10 limbs10 encoded10
#print axioms encoded10
#print axioms parser10
def cell11 : Array U8 16#usize := ⟨[222#u8,172#u8,229#u8,81#u8,162#u8,210#u8,10#u8,33#u8,219#u8,183#u8,135#u8,30#u8,15#u8,243#u8,214#u8,1#u8],by rfl⟩
def limbs11 : QM31Limbs := ![⟨1374006494,by change 1374006494<2147483647;omega⟩,⟨554357410,by change 554357410<2147483647;omega⟩,⟨512210907,by change 512210907<2147483647;omega⟩,⟨30864143,by change 30864143<2147483647;omega⟩]
theorem rawCell11 : (raw.drop 176).take 16=cell11.val := by
  simp only [raw,JFz_Scan51.data,JFz_Scan51.j00,JFz_Scan51.j01,JFz_Scan51.j02,JFz_Scan51.j03,JFz_Scan51.j04,JFz_Scan51.j05,JFz_Scan51.j06,JFz_Scan51.j07,JFz_Scan51.j08,JFz_Scan51.j09,JFz_Scan51.j10,JFz_Scan51.j11,JFz_Scan51.j12,JFz_Scan51.b00_length,JFz_Scan51.b01_length,JFz_Scan51.b02_length,JFz_Scan51.b03_length,JFz_Scan51.b04_length,JFz_Scan51.b05_length,JFz_Scan51.b06_length,JFz_Scan51.b07_length,JFz_Scan51.b08_length,JFz_Scan51.b09_length,JFz_Scan51.b10_length,JFz_Scan51.b11_length,JFz_Scan51.b12_length,JFz_Scan51.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell11
theorem encoded11 : CandidateParserByteOrder.arrayBytes16 cell11=encodeQM31LE limbs11 := by
  funext i
  fin_cases i <;> rfl
theorem parser11 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell11)=
    ok (some ⟨⟨1374006494#u32,554357410#u32⟩,⟨512210907#u32,30864143#u32⟩⟩) :=
  JFr_EncodedCell.parser cell11 limbs11 encoded11
#print axioms encoded11
#print axioms parser11
def cell12 : Array U8 16#usize := ⟨[102#u8,34#u8,10#u8,82#u8,212#u8,44#u8,214#u8,119#u8,95#u8,20#u8,188#u8,43#u8,227#u8,243#u8,83#u8,96#u8],by rfl⟩
def limbs12 : QM31Limbs := ![⟨1376395878,by change 1376395878<2147483647;omega⟩,⟨2010524884,by change 2010524884<2147483647;omega⟩,⟨733746271,by change 733746271<2147483647;omega⟩,⟨1616114659,by change 1616114659<2147483647;omega⟩]
theorem rawCell12 : (raw.drop 192).take 16=cell12.val := by
  simp only [raw,JFz_Scan51.data,JFz_Scan51.j00,JFz_Scan51.j01,JFz_Scan51.j02,JFz_Scan51.j03,JFz_Scan51.j04,JFz_Scan51.j05,JFz_Scan51.j06,JFz_Scan51.j07,JFz_Scan51.j08,JFz_Scan51.j09,JFz_Scan51.j10,JFz_Scan51.j11,JFz_Scan51.j12,JFz_Scan51.b00_length,JFz_Scan51.b01_length,JFz_Scan51.b02_length,JFz_Scan51.b03_length,JFz_Scan51.b04_length,JFz_Scan51.b05_length,JFz_Scan51.b06_length,JFz_Scan51.b07_length,JFz_Scan51.b08_length,JFz_Scan51.b09_length,JFz_Scan51.b10_length,JFz_Scan51.b11_length,JFz_Scan51.b12_length,JFz_Scan51.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell12
theorem encoded12 : CandidateParserByteOrder.arrayBytes16 cell12=encodeQM31LE limbs12 := by
  funext i
  fin_cases i <;> rfl
theorem parser12 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell12)=
    ok (some ⟨⟨1376395878#u32,2010524884#u32⟩,⟨733746271#u32,1616114659#u32⟩⟩) :=
  JFr_EncodedCell.parser cell12 limbs12 encoded12
#print axioms encoded12
#print axioms parser12
def cell13 : Array U8 16#usize := ⟨[103#u8,144#u8,47#u8,63#u8,99#u8,249#u8,77#u8,95#u8,37#u8,120#u8,99#u8,85#u8,121#u8,1#u8,214#u8,119#u8],by rfl⟩
def limbs13 : QM31Limbs := ![⟨1060081767,by change 1060081767<2147483647;omega⟩,⟨1598945635,by change 1598945635<2147483647;omega⟩,⟨1432582181,by change 1432582181<2147483647;omega⟩,⟨2010513785,by change 2010513785<2147483647;omega⟩]
theorem rawCell13 : (raw.drop 208).take 16=cell13.val := by
  simp only [raw,JFz_Scan51.data,JFz_Scan51.j00,JFz_Scan51.j01,JFz_Scan51.j02,JFz_Scan51.j03,JFz_Scan51.j04,JFz_Scan51.j05,JFz_Scan51.j06,JFz_Scan51.j07,JFz_Scan51.j08,JFz_Scan51.j09,JFz_Scan51.j10,JFz_Scan51.j11,JFz_Scan51.j12,JFz_Scan51.b00_length,JFz_Scan51.b01_length,JFz_Scan51.b02_length,JFz_Scan51.b03_length,JFz_Scan51.b04_length,JFz_Scan51.b05_length,JFz_Scan51.b06_length,JFz_Scan51.b07_length,JFz_Scan51.b08_length,JFz_Scan51.b09_length,JFz_Scan51.b10_length,JFz_Scan51.b11_length,JFz_Scan51.b12_length,JFz_Scan51.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell13
theorem encoded13 : CandidateParserByteOrder.arrayBytes16 cell13=encodeQM31LE limbs13 := by
  funext i
  fin_cases i <;> rfl
theorem parser13 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell13)=
    ok (some ⟨⟨1060081767#u32,1598945635#u32⟩,⟨1432582181#u32,2010513785#u32⟩⟩) :=
  JFr_EncodedCell.parser cell13 limbs13 encoded13
#print axioms encoded13
#print axioms parser13
def cell14 : Array U8 16#usize := ⟨[204#u8,47#u8,156#u8,17#u8,225#u8,92#u8,91#u8,53#u8,166#u8,9#u8,79#u8,2#u8,54#u8,32#u8,41#u8,48#u8],by rfl⟩
def limbs14 : QM31Limbs := ![⟨295448524,by change 295448524<2147483647;omega⟩,⟨895180001,by change 895180001<2147483647;omega⟩,⟨38734246,by change 38734246<2147483647;omega⟩,⟨808001590,by change 808001590<2147483647;omega⟩]
theorem rawCell14 : (raw.drop 224).take 16=cell14.val := by
  simp only [raw,JFz_Scan51.data,JFz_Scan51.j00,JFz_Scan51.j01,JFz_Scan51.j02,JFz_Scan51.j03,JFz_Scan51.j04,JFz_Scan51.j05,JFz_Scan51.j06,JFz_Scan51.j07,JFz_Scan51.j08,JFz_Scan51.j09,JFz_Scan51.j10,JFz_Scan51.j11,JFz_Scan51.j12,JFz_Scan51.b00_length,JFz_Scan51.b01_length,JFz_Scan51.b02_length,JFz_Scan51.b03_length,JFz_Scan51.b04_length,JFz_Scan51.b05_length,JFz_Scan51.b06_length,JFz_Scan51.b07_length,JFz_Scan51.b08_length,JFz_Scan51.b09_length,JFz_Scan51.b10_length,JFz_Scan51.b11_length,JFz_Scan51.b12_length,JFz_Scan51.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell14
theorem encoded14 : CandidateParserByteOrder.arrayBytes16 cell14=encodeQM31LE limbs14 := by
  funext i
  fin_cases i <;> rfl
theorem parser14 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell14)=
    ok (some ⟨⟨295448524#u32,895180001#u32⟩,⟨38734246#u32,808001590#u32⟩⟩) :=
  JFr_EncodedCell.parser cell14 limbs14 encoded14
#print axioms encoded14
#print axioms parser14
def cell15 : Array U8 16#usize := ⟨[217#u8,201#u8,211#u8,42#u8,91#u8,174#u8,202#u8,60#u8,104#u8,191#u8,71#u8,52#u8,114#u8,172#u8,27#u8,85#u8],by rfl⟩
def limbs15 : QM31Limbs := ![⟨718522841,by change 718522841<2147483647;omega⟩,⟨1019915867,by change 1019915867<2147483647;omega⟩,⟨877117288,by change 877117288<2147483647;omega⟩,⟨1427876978,by change 1427876978<2147483647;omega⟩]
theorem rawCell15 : (raw.drop 240).take 16=cell15.val := by
  simp only [raw,JFz_Scan51.data,JFz_Scan51.j00,JFz_Scan51.j01,JFz_Scan51.j02,JFz_Scan51.j03,JFz_Scan51.j04,JFz_Scan51.j05,JFz_Scan51.j06,JFz_Scan51.j07,JFz_Scan51.j08,JFz_Scan51.j09,JFz_Scan51.j10,JFz_Scan51.j11,JFz_Scan51.j12,JFz_Scan51.b00_length,JFz_Scan51.b01_length,JFz_Scan51.b02_length,JFz_Scan51.b03_length,JFz_Scan51.b04_length,JFz_Scan51.b05_length,JFz_Scan51.b06_length,JFz_Scan51.b07_length,JFz_Scan51.b08_length,JFz_Scan51.b09_length,JFz_Scan51.b10_length,JFz_Scan51.b11_length,JFz_Scan51.b12_length,JFz_Scan51.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell15
theorem encoded15 : CandidateParserByteOrder.arrayBytes16 cell15=encodeQM31LE limbs15 := by
  funext i
  fin_cases i <;> rfl
theorem parser15 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell15)=
    ok (some ⟨⟨718522841#u32,1019915867#u32⟩,⟨877117288#u32,1427876978#u32⟩⟩) :=
  JFr_EncodedCell.parser cell15 limbs15 encoded15
#print axioms encoded15
#print axioms parser15
def cell16 : Array U8 16#usize := ⟨[109#u8,48#u8,8#u8,29#u8,18#u8,47#u8,184#u8,7#u8,213#u8,105#u8,36#u8,105#u8,239#u8,117#u8,43#u8,111#u8],by rfl⟩
def limbs16 : QM31Limbs := ![⟨487075949,by change 487075949<2147483647;omega⟩,⟨129511186,by change 129511186<2147483647;omega⟩,⟨1763994069,by change 1763994069<2147483647;omega⟩,⟨1865119215,by change 1865119215<2147483647;omega⟩]
theorem rawCell16 : (raw.drop 256).take 16=cell16.val := by
  simp only [raw,JFz_Scan51.data,JFz_Scan51.j00,JFz_Scan51.j01,JFz_Scan51.j02,JFz_Scan51.j03,JFz_Scan51.j04,JFz_Scan51.j05,JFz_Scan51.j06,JFz_Scan51.j07,JFz_Scan51.j08,JFz_Scan51.j09,JFz_Scan51.j10,JFz_Scan51.j11,JFz_Scan51.j12,JFz_Scan51.b00_length,JFz_Scan51.b01_length,JFz_Scan51.b02_length,JFz_Scan51.b03_length,JFz_Scan51.b04_length,JFz_Scan51.b05_length,JFz_Scan51.b06_length,JFz_Scan51.b07_length,JFz_Scan51.b08_length,JFz_Scan51.b09_length,JFz_Scan51.b10_length,JFz_Scan51.b11_length,JFz_Scan51.b12_length,JFz_Scan51.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell16
theorem encoded16 : CandidateParserByteOrder.arrayBytes16 cell16=encodeQM31LE limbs16 := by
  funext i
  fin_cases i <;> rfl
theorem parser16 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell16)=
    ok (some ⟨⟨487075949#u32,129511186#u32⟩,⟨1763994069#u32,1865119215#u32⟩⟩) :=
  JFr_EncodedCell.parser cell16 limbs16 encoded16
#print axioms encoded16
#print axioms parser16
def cell17 : Array U8 16#usize := ⟨[84#u8,89#u8,22#u8,3#u8,148#u8,159#u8,110#u8,37#u8,141#u8,3#u8,210#u8,105#u8,228#u8,199#u8,144#u8,45#u8],by rfl⟩
def limbs17 : QM31Limbs := ![⟨51796308,by change 51796308<2147483647;omega⟩,⟨628006804,by change 628006804<2147483647;omega⟩,⟨1775371149,by change 1775371149<2147483647;omega⟩,⟨764463076,by change 764463076<2147483647;omega⟩]
theorem rawCell17 : (raw.drop 272).take 16=cell17.val := by
  simp only [raw,JFz_Scan51.data,JFz_Scan51.j00,JFz_Scan51.j01,JFz_Scan51.j02,JFz_Scan51.j03,JFz_Scan51.j04,JFz_Scan51.j05,JFz_Scan51.j06,JFz_Scan51.j07,JFz_Scan51.j08,JFz_Scan51.j09,JFz_Scan51.j10,JFz_Scan51.j11,JFz_Scan51.j12,JFz_Scan51.b00_length,JFz_Scan51.b01_length,JFz_Scan51.b02_length,JFz_Scan51.b03_length,JFz_Scan51.b04_length,JFz_Scan51.b05_length,JFz_Scan51.b06_length,JFz_Scan51.b07_length,JFz_Scan51.b08_length,JFz_Scan51.b09_length,JFz_Scan51.b10_length,JFz_Scan51.b11_length,JFz_Scan51.b12_length,JFz_Scan51.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell17
theorem encoded17 : CandidateParserByteOrder.arrayBytes16 cell17=encodeQM31LE limbs17 := by
  funext i
  fin_cases i <;> rfl
theorem parser17 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell17)=
    ok (some ⟨⟨51796308#u32,628006804#u32⟩,⟨1775371149#u32,764463076#u32⟩⟩) :=
  JFr_EncodedCell.parser cell17 limbs17 encoded17
#print axioms encoded17
#print axioms parser17
def cell18 : Array U8 16#usize := ⟨[73#u8,144#u8,30#u8,3#u8,97#u8,16#u8,46#u8,99#u8,238#u8,163#u8,192#u8,121#u8,122#u8,187#u8,108#u8,0#u8],by rfl⟩
def limbs18 : QM31Limbs := ![⟨52334665,by change 52334665<2147483647;omega⟩,⟨1663963233,by change 1663963233<2147483647;omega⟩,⟨2042668014,by change 2042668014<2147483647;omega⟩,⟨7125882,by change 7125882<2147483647;omega⟩]
theorem rawCell18 : (raw.drop 288).take 16=cell18.val := by
  simp only [raw,JFz_Scan51.data,JFz_Scan51.j00,JFz_Scan51.j01,JFz_Scan51.j02,JFz_Scan51.j03,JFz_Scan51.j04,JFz_Scan51.j05,JFz_Scan51.j06,JFz_Scan51.j07,JFz_Scan51.j08,JFz_Scan51.j09,JFz_Scan51.j10,JFz_Scan51.j11,JFz_Scan51.j12,JFz_Scan51.b00_length,JFz_Scan51.b01_length,JFz_Scan51.b02_length,JFz_Scan51.b03_length,JFz_Scan51.b04_length,JFz_Scan51.b05_length,JFz_Scan51.b06_length,JFz_Scan51.b07_length,JFz_Scan51.b08_length,JFz_Scan51.b09_length,JFz_Scan51.b10_length,JFz_Scan51.b11_length,JFz_Scan51.b12_length,JFz_Scan51.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell18
theorem encoded18 : CandidateParserByteOrder.arrayBytes16 cell18=encodeQM31LE limbs18 := by
  funext i
  fin_cases i <;> rfl
theorem parser18 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell18)=
    ok (some ⟨⟨52334665#u32,1663963233#u32⟩,⟨2042668014#u32,7125882#u32⟩⟩) :=
  JFr_EncodedCell.parser cell18 limbs18 encoded18
#print axioms encoded18
#print axioms parser18
def cell19 : Array U8 16#usize := ⟨[50#u8,186#u8,207#u8,127#u8,144#u8,151#u8,15#u8,96#u8,143#u8,251#u8,105#u8,48#u8,209#u8,226#u8,242#u8,42#u8],by rfl⟩
def limbs19 : QM31Limbs := ![⟨2144320050,by change 2144320050<2147483647;omega⟩,⟨1611634576,by change 1611634576<2147483647;omega⟩,⟨812252047,by change 812252047<2147483647;omega⟩,⟨720560849,by change 720560849<2147483647;omega⟩]
theorem rawCell19 : (raw.drop 304).take 16=cell19.val := by
  simp only [raw,JFz_Scan51.data,JFz_Scan51.j00,JFz_Scan51.j01,JFz_Scan51.j02,JFz_Scan51.j03,JFz_Scan51.j04,JFz_Scan51.j05,JFz_Scan51.j06,JFz_Scan51.j07,JFz_Scan51.j08,JFz_Scan51.j09,JFz_Scan51.j10,JFz_Scan51.j11,JFz_Scan51.j12,JFz_Scan51.b00_length,JFz_Scan51.b01_length,JFz_Scan51.b02_length,JFz_Scan51.b03_length,JFz_Scan51.b04_length,JFz_Scan51.b05_length,JFz_Scan51.b06_length,JFz_Scan51.b07_length,JFz_Scan51.b08_length,JFz_Scan51.b09_length,JFz_Scan51.b10_length,JFz_Scan51.b11_length,JFz_Scan51.b12_length,JFz_Scan51.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell19
theorem encoded19 : CandidateParserByteOrder.arrayBytes16 cell19=encodeQM31LE limbs19 := by
  funext i
  fin_cases i <;> rfl
theorem parser19 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell19)=
    ok (some ⟨⟨2144320050#u32,1611634576#u32⟩,⟨812252047#u32,720560849#u32⟩⟩) :=
  JFr_EncodedCell.parser cell19 limbs19 encoded19
#print axioms encoded19
#print axioms parser19
def cell20 : Array U8 16#usize := ⟨[221#u8,22#u8,149#u8,5#u8,85#u8,189#u8,165#u8,17#u8,140#u8,188#u8,84#u8,57#u8,142#u8,76#u8,120#u8,14#u8],by rfl⟩
def limbs20 : QM31Limbs := ![⟨93656797,by change 93656797<2147483647;omega⟩,⟨296074581,by change 296074581<2147483647;omega⟩,⟨961854604,by change 961854604<2147483647;omega⟩,⟨242764942,by change 242764942<2147483647;omega⟩]
theorem rawCell20 : (raw.drop 320).take 16=cell20.val := by
  simp only [raw,JFz_Scan51.data,JFz_Scan51.j00,JFz_Scan51.j01,JFz_Scan51.j02,JFz_Scan51.j03,JFz_Scan51.j04,JFz_Scan51.j05,JFz_Scan51.j06,JFz_Scan51.j07,JFz_Scan51.j08,JFz_Scan51.j09,JFz_Scan51.j10,JFz_Scan51.j11,JFz_Scan51.j12,JFz_Scan51.b00_length,JFz_Scan51.b01_length,JFz_Scan51.b02_length,JFz_Scan51.b03_length,JFz_Scan51.b04_length,JFz_Scan51.b05_length,JFz_Scan51.b06_length,JFz_Scan51.b07_length,JFz_Scan51.b08_length,JFz_Scan51.b09_length,JFz_Scan51.b10_length,JFz_Scan51.b11_length,JFz_Scan51.b12_length,JFz_Scan51.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell20
theorem encoded20 : CandidateParserByteOrder.arrayBytes16 cell20=encodeQM31LE limbs20 := by
  funext i
  fin_cases i <;> rfl
theorem parser20 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell20)=
    ok (some ⟨⟨93656797#u32,296074581#u32⟩,⟨961854604#u32,242764942#u32⟩⟩) :=
  JFr_EncodedCell.parser cell20 limbs20 encoded20
#print axioms encoded20
#print axioms parser20
def cell21 : Array U8 16#usize := ⟨[7#u8,214#u8,82#u8,19#u8,72#u8,52#u8,173#u8,59#u8,126#u8,90#u8,35#u8,98#u8,172#u8,218#u8,89#u8,44#u8],by rfl⟩
def limbs21 : QM31Limbs := ![⟨324195847,by change 324195847<2147483647;omega⟩,⟨1001206856,by change 1001206856<2147483647;omega⟩,⟨1646484094,by change 1646484094<2147483647;omega⟩,⟨744086188,by change 744086188<2147483647;omega⟩]
theorem rawCell21 : (raw.drop 336).take 16=cell21.val := by
  simp only [raw,JFz_Scan51.data,JFz_Scan51.j00,JFz_Scan51.j01,JFz_Scan51.j02,JFz_Scan51.j03,JFz_Scan51.j04,JFz_Scan51.j05,JFz_Scan51.j06,JFz_Scan51.j07,JFz_Scan51.j08,JFz_Scan51.j09,JFz_Scan51.j10,JFz_Scan51.j11,JFz_Scan51.j12,JFz_Scan51.b00_length,JFz_Scan51.b01_length,JFz_Scan51.b02_length,JFz_Scan51.b03_length,JFz_Scan51.b04_length,JFz_Scan51.b05_length,JFz_Scan51.b06_length,JFz_Scan51.b07_length,JFz_Scan51.b08_length,JFz_Scan51.b09_length,JFz_Scan51.b10_length,JFz_Scan51.b11_length,JFz_Scan51.b12_length,JFz_Scan51.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell21
theorem encoded21 : CandidateParserByteOrder.arrayBytes16 cell21=encodeQM31LE limbs21 := by
  funext i
  fin_cases i <;> rfl
theorem parser21 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell21)=
    ok (some ⟨⟨324195847#u32,1001206856#u32⟩,⟨1646484094#u32,744086188#u32⟩⟩) :=
  JFr_EncodedCell.parser cell21 limbs21 encoded21
#print axioms encoded21
#print axioms parser21
def cell22 : Array U8 16#usize := ⟨[183#u8,53#u8,124#u8,112#u8,252#u8,161#u8,87#u8,65#u8,53#u8,236#u8,9#u8,65#u8,131#u8,57#u8,100#u8,33#u8],by rfl⟩
def limbs22 : QM31Limbs := ![⟨1887188407,by change 1887188407<2147483647;omega⟩,⟨1096262140,by change 1096262140<2147483647;omega⟩,⟨1091169333,by change 1091169333<2147483647;omega⟩,⟨560216451,by change 560216451<2147483647;omega⟩]
theorem rawCell22 : (raw.drop 352).take 16=cell22.val := by
  simp only [raw,JFz_Scan51.data,JFz_Scan51.j00,JFz_Scan51.j01,JFz_Scan51.j02,JFz_Scan51.j03,JFz_Scan51.j04,JFz_Scan51.j05,JFz_Scan51.j06,JFz_Scan51.j07,JFz_Scan51.j08,JFz_Scan51.j09,JFz_Scan51.j10,JFz_Scan51.j11,JFz_Scan51.j12,JFz_Scan51.b00_length,JFz_Scan51.b01_length,JFz_Scan51.b02_length,JFz_Scan51.b03_length,JFz_Scan51.b04_length,JFz_Scan51.b05_length,JFz_Scan51.b06_length,JFz_Scan51.b07_length,JFz_Scan51.b08_length,JFz_Scan51.b09_length,JFz_Scan51.b10_length,JFz_Scan51.b11_length,JFz_Scan51.b12_length,JFz_Scan51.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell22
theorem encoded22 : CandidateParserByteOrder.arrayBytes16 cell22=encodeQM31LE limbs22 := by
  funext i
  fin_cases i <;> rfl
theorem parser22 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell22)=
    ok (some ⟨⟨1887188407#u32,1096262140#u32⟩,⟨1091169333#u32,560216451#u32⟩⟩) :=
  JFr_EncodedCell.parser cell22 limbs22 encoded22
#print axioms encoded22
#print axioms parser22
def cell23 : Array U8 16#usize := ⟨[181#u8,104#u8,85#u8,125#u8,62#u8,224#u8,237#u8,23#u8,183#u8,29#u8,175#u8,69#u8,211#u8,56#u8,247#u8,78#u8],by rfl⟩
def limbs23 : QM31Limbs := ![⟨2102749365,by change 2102749365<2147483647;omega⟩,⟨401465406,by change 401465406<2147483647;omega⟩,⟨1169104311,by change 1169104311<2147483647;omega⟩,⟨1324824787,by change 1324824787<2147483647;omega⟩]
theorem rawCell23 : (raw.drop 368).take 16=cell23.val := by
  simp only [raw,JFz_Scan51.data,JFz_Scan51.j00,JFz_Scan51.j01,JFz_Scan51.j02,JFz_Scan51.j03,JFz_Scan51.j04,JFz_Scan51.j05,JFz_Scan51.j06,JFz_Scan51.j07,JFz_Scan51.j08,JFz_Scan51.j09,JFz_Scan51.j10,JFz_Scan51.j11,JFz_Scan51.j12,JFz_Scan51.b00_length,JFz_Scan51.b01_length,JFz_Scan51.b02_length,JFz_Scan51.b03_length,JFz_Scan51.b04_length,JFz_Scan51.b05_length,JFz_Scan51.b06_length,JFz_Scan51.b07_length,JFz_Scan51.b08_length,JFz_Scan51.b09_length,JFz_Scan51.b10_length,JFz_Scan51.b11_length,JFz_Scan51.b12_length,JFz_Scan51.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell23
theorem encoded23 : CandidateParserByteOrder.arrayBytes16 cell23=encodeQM31LE limbs23 := by
  funext i
  fin_cases i <;> rfl
theorem parser23 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell23)=
    ok (some ⟨⟨2102749365#u32,401465406#u32⟩,⟨1169104311#u32,1324824787#u32⟩⟩) :=
  JFr_EncodedCell.parser cell23 limbs23 encoded23
#print axioms encoded23
#print axioms parser23
def cell24 : Array U8 16#usize := ⟨[173#u8,146#u8,25#u8,94#u8,106#u8,113#u8,125#u8,69#u8,145#u8,218#u8,238#u8,106#u8,115#u8,115#u8,17#u8,94#u8],by rfl⟩
def limbs24 : QM31Limbs := ![⟨1578734253,by change 1578734253<2147483647;omega⟩,⟨1165848938,by change 1165848938<2147483647;omega⟩,⟨1794038417,by change 1794038417<2147483647;omega⟩,⟨1578201971,by change 1578201971<2147483647;omega⟩]
theorem rawCell24 : (raw.drop 384).take 16=cell24.val := by
  simp only [raw,JFz_Scan51.data,JFz_Scan51.j00,JFz_Scan51.j01,JFz_Scan51.j02,JFz_Scan51.j03,JFz_Scan51.j04,JFz_Scan51.j05,JFz_Scan51.j06,JFz_Scan51.j07,JFz_Scan51.j08,JFz_Scan51.j09,JFz_Scan51.j10,JFz_Scan51.j11,JFz_Scan51.j12,JFz_Scan51.b00_length,JFz_Scan51.b01_length,JFz_Scan51.b02_length,JFz_Scan51.b03_length,JFz_Scan51.b04_length,JFz_Scan51.b05_length,JFz_Scan51.b06_length,JFz_Scan51.b07_length,JFz_Scan51.b08_length,JFz_Scan51.b09_length,JFz_Scan51.b10_length,JFz_Scan51.b11_length,JFz_Scan51.b12_length,JFz_Scan51.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell24
theorem encoded24 : CandidateParserByteOrder.arrayBytes16 cell24=encodeQM31LE limbs24 := by
  funext i
  fin_cases i <;> rfl
theorem parser24 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell24)=
    ok (some ⟨⟨1578734253#u32,1165848938#u32⟩,⟨1794038417#u32,1578201971#u32⟩⟩) :=
  JFr_EncodedCell.parser cell24 limbs24 encoded24
#print axioms encoded24
#print axioms parser24
def cell25 : Array U8 16#usize := ⟨[232#u8,30#u8,20#u8,37#u8,174#u8,221#u8,85#u8,7#u8,249#u8,223#u8,243#u8,66#u8,188#u8,201#u8,117#u8,81#u8],by rfl⟩
def limbs25 : QM31Limbs := ![⟨622075624,by change 622075624<2147483647;omega⟩,⟨123067822,by change 123067822<2147483647;omega⟩,⟨1123278841,by change 1123278841<2147483647;omega⟩,⟨1366673852,by change 1366673852<2147483647;omega⟩]
theorem rawCell25 : (raw.drop 400).take 16=cell25.val := by
  simp only [raw,JFz_Scan51.data,JFz_Scan51.j00,JFz_Scan51.j01,JFz_Scan51.j02,JFz_Scan51.j03,JFz_Scan51.j04,JFz_Scan51.j05,JFz_Scan51.j06,JFz_Scan51.j07,JFz_Scan51.j08,JFz_Scan51.j09,JFz_Scan51.j10,JFz_Scan51.j11,JFz_Scan51.j12,JFz_Scan51.b00_length,JFz_Scan51.b01_length,JFz_Scan51.b02_length,JFz_Scan51.b03_length,JFz_Scan51.b04_length,JFz_Scan51.b05_length,JFz_Scan51.b06_length,JFz_Scan51.b07_length,JFz_Scan51.b08_length,JFz_Scan51.b09_length,JFz_Scan51.b10_length,JFz_Scan51.b11_length,JFz_Scan51.b12_length,JFz_Scan51.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell25
theorem encoded25 : CandidateParserByteOrder.arrayBytes16 cell25=encodeQM31LE limbs25 := by
  funext i
  fin_cases i <;> rfl
theorem parser25 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell25)=
    ok (some ⟨⟨622075624#u32,123067822#u32⟩,⟨1123278841#u32,1366673852#u32⟩⟩) :=
  JFr_EncodedCell.parser cell25 limbs25 encoded25
#print axioms encoded25
#print axioms parser25
def cell26 : Array U8 16#usize := ⟨[15#u8,153#u8,164#u8,86#u8,129#u8,223#u8,88#u8,18#u8,91#u8,36#u8,44#u8,7#u8,169#u8,149#u8,191#u8,66#u8],by rfl⟩
def limbs26 : QM31Limbs := ![⟨1453627663,by change 1453627663<2147483647;omega⟩,⟨307814273,by change 307814273<2147483647;omega⟩,⟨120333403,by change 120333403<2147483647;omega⟩,⟨1119851945,by change 1119851945<2147483647;omega⟩]
theorem rawCell26 : (raw.drop 416).take 16=cell26.val := by
  simp only [raw,JFz_Scan51.data,JFz_Scan51.j00,JFz_Scan51.j01,JFz_Scan51.j02,JFz_Scan51.j03,JFz_Scan51.j04,JFz_Scan51.j05,JFz_Scan51.j06,JFz_Scan51.j07,JFz_Scan51.j08,JFz_Scan51.j09,JFz_Scan51.j10,JFz_Scan51.j11,JFz_Scan51.j12,JFz_Scan51.b00_length,JFz_Scan51.b01_length,JFz_Scan51.b02_length,JFz_Scan51.b03_length,JFz_Scan51.b04_length,JFz_Scan51.b05_length,JFz_Scan51.b06_length,JFz_Scan51.b07_length,JFz_Scan51.b08_length,JFz_Scan51.b09_length,JFz_Scan51.b10_length,JFz_Scan51.b11_length,JFz_Scan51.b12_length,JFz_Scan51.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell26
theorem encoded26 : CandidateParserByteOrder.arrayBytes16 cell26=encodeQM31LE limbs26 := by
  funext i
  fin_cases i <;> rfl
theorem parser26 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell26)=
    ok (some ⟨⟨1453627663#u32,307814273#u32⟩,⟨120333403#u32,1119851945#u32⟩⟩) :=
  JFr_EncodedCell.parser cell26 limbs26 encoded26
#print axioms encoded26
#print axioms parser26
def cell27 : Array U8 16#usize := ⟨[33#u8,169#u8,228#u8,100#u8,159#u8,245#u8,133#u8,68#u8,138#u8,76#u8,207#u8,110#u8,60#u8,3#u8,198#u8,96#u8],by rfl⟩
def limbs27 : QM31Limbs := ![⟨1692707105,by change 1692707105<2147483647;omega⟩,⟨1149629855,by change 1149629855<2147483647;omega⟩,⟨1859079306,by change 1859079306<2147483647;omega⟩,⟨1623589692,by change 1623589692<2147483647;omega⟩]
theorem rawCell27 : (raw.drop 432).take 16=cell27.val := by
  simp only [raw,JFz_Scan51.data,JFz_Scan51.j00,JFz_Scan51.j01,JFz_Scan51.j02,JFz_Scan51.j03,JFz_Scan51.j04,JFz_Scan51.j05,JFz_Scan51.j06,JFz_Scan51.j07,JFz_Scan51.j08,JFz_Scan51.j09,JFz_Scan51.j10,JFz_Scan51.j11,JFz_Scan51.j12,JFz_Scan51.b00_length,JFz_Scan51.b01_length,JFz_Scan51.b02_length,JFz_Scan51.b03_length,JFz_Scan51.b04_length,JFz_Scan51.b05_length,JFz_Scan51.b06_length,JFz_Scan51.b07_length,JFz_Scan51.b08_length,JFz_Scan51.b09_length,JFz_Scan51.b10_length,JFz_Scan51.b11_length,JFz_Scan51.b12_length,JFz_Scan51.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell27
theorem encoded27 : CandidateParserByteOrder.arrayBytes16 cell27=encodeQM31LE limbs27 := by
  funext i
  fin_cases i <;> rfl
theorem parser27 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell27)=
    ok (some ⟨⟨1692707105#u32,1149629855#u32⟩,⟨1859079306#u32,1623589692#u32⟩⟩) :=
  JFr_EncodedCell.parser cell27 limbs27 encoded27
#print axioms encoded27
#print axioms parser27
end AspisR1.JFr_Bytes03
