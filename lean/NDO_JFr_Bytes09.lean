import NDO_JFr_Data09
import NDO_JFr_EncodedCell
import NDO_JFz_Scan57
set_option autoImplicit false
namespace AspisR1.JFr_Bytes09
open Aeneas Aeneas.Std Result RetainedFieldByteCodec
open AspisR1PublicPreparation
open AspisS1ExtractedRoundChildren
def raw : List U8 := JFz_Scan57.data
theorem rawLength : raw.length=448 := JFz_Scan57.length
#print axioms rawLength
theorem selected : (JFx_NativeBytes.proof.val.drop 4253).take 448=raw := JFz_Scan57.selected
#print axioms selected
def cell00 : Array U8 16#usize := ⟨[19#u8,42#u8,227#u8,37#u8,22#u8,134#u8,62#u8,17#u8,71#u8,226#u8,20#u8,16#u8,180#u8,15#u8,119#u8,14#u8],by rfl⟩
def limbs00 : QM31Limbs := ![⟨635644435,by change 635644435<2147483647;omega⟩,⟨289310230,by change 289310230<2147483647;omega⟩,⟨269804103,by change 269804103<2147483647;omega⟩,⟨242683828,by change 242683828<2147483647;omega⟩]
theorem rawCell00 : (raw.drop 0).take 16=cell00.val := by
  simp only [raw,JFz_Scan57.data,JFz_Scan57.j00,JFz_Scan57.j01,JFz_Scan57.j02,JFz_Scan57.j03,JFz_Scan57.j04,JFz_Scan57.j05,JFz_Scan57.j06,JFz_Scan57.j07,JFz_Scan57.j08,JFz_Scan57.j09,JFz_Scan57.j10,JFz_Scan57.j11,JFz_Scan57.j12,JFz_Scan57.b00_length,JFz_Scan57.b01_length,JFz_Scan57.b02_length,JFz_Scan57.b03_length,JFz_Scan57.b04_length,JFz_Scan57.b05_length,JFz_Scan57.b06_length,JFz_Scan57.b07_length,JFz_Scan57.b08_length,JFz_Scan57.b09_length,JFz_Scan57.b10_length,JFz_Scan57.b11_length,JFz_Scan57.b12_length,JFz_Scan57.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell00
theorem encoded00 : CandidateParserByteOrder.arrayBytes16 cell00=encodeQM31LE limbs00 := by
  funext i
  fin_cases i <;> rfl
theorem parser00 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell00)=
    ok (some ⟨⟨635644435#u32,289310230#u32⟩,⟨269804103#u32,242683828#u32⟩⟩) :=
  JFr_EncodedCell.parser cell00 limbs00 encoded00
#print axioms encoded00
#print axioms parser00
def cell01 : Array U8 16#usize := ⟨[95#u8,111#u8,87#u8,51#u8,222#u8,210#u8,144#u8,80#u8,60#u8,24#u8,182#u8,35#u8,254#u8,56#u8,4#u8,67#u8],by rfl⟩
def limbs01 : QM31Limbs := ![⟨861368159,by change 861368159<2147483647;omega⟩,⟨1351668446,by change 1351668446<2147483647;omega⟩,⟨599136316,by change 599136316<2147483647;omega⟩,⟨1124350206,by change 1124350206<2147483647;omega⟩]
theorem rawCell01 : (raw.drop 16).take 16=cell01.val := by
  simp only [raw,JFz_Scan57.data,JFz_Scan57.j00,JFz_Scan57.j01,JFz_Scan57.j02,JFz_Scan57.j03,JFz_Scan57.j04,JFz_Scan57.j05,JFz_Scan57.j06,JFz_Scan57.j07,JFz_Scan57.j08,JFz_Scan57.j09,JFz_Scan57.j10,JFz_Scan57.j11,JFz_Scan57.j12,JFz_Scan57.b00_length,JFz_Scan57.b01_length,JFz_Scan57.b02_length,JFz_Scan57.b03_length,JFz_Scan57.b04_length,JFz_Scan57.b05_length,JFz_Scan57.b06_length,JFz_Scan57.b07_length,JFz_Scan57.b08_length,JFz_Scan57.b09_length,JFz_Scan57.b10_length,JFz_Scan57.b11_length,JFz_Scan57.b12_length,JFz_Scan57.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell01
theorem encoded01 : CandidateParserByteOrder.arrayBytes16 cell01=encodeQM31LE limbs01 := by
  funext i
  fin_cases i <;> rfl
theorem parser01 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell01)=
    ok (some ⟨⟨861368159#u32,1351668446#u32⟩,⟨599136316#u32,1124350206#u32⟩⟩) :=
  JFr_EncodedCell.parser cell01 limbs01 encoded01
#print axioms encoded01
#print axioms parser01
def cell02 : Array U8 16#usize := ⟨[226#u8,204#u8,108#u8,21#u8,168#u8,177#u8,182#u8,1#u8,228#u8,161#u8,99#u8,14#u8,204#u8,6#u8,180#u8,17#u8],by rfl⟩
def limbs02 : QM31Limbs := ![⟨359451874,by change 359451874<2147483647;omega⟩,⟨28750248,by change 28750248<2147483647;omega⟩,⟨241410532,by change 241410532<2147483647;omega⟩,⟨297010892,by change 297010892<2147483647;omega⟩]
theorem rawCell02 : (raw.drop 32).take 16=cell02.val := by
  simp only [raw,JFz_Scan57.data,JFz_Scan57.j00,JFz_Scan57.j01,JFz_Scan57.j02,JFz_Scan57.j03,JFz_Scan57.j04,JFz_Scan57.j05,JFz_Scan57.j06,JFz_Scan57.j07,JFz_Scan57.j08,JFz_Scan57.j09,JFz_Scan57.j10,JFz_Scan57.j11,JFz_Scan57.j12,JFz_Scan57.b00_length,JFz_Scan57.b01_length,JFz_Scan57.b02_length,JFz_Scan57.b03_length,JFz_Scan57.b04_length,JFz_Scan57.b05_length,JFz_Scan57.b06_length,JFz_Scan57.b07_length,JFz_Scan57.b08_length,JFz_Scan57.b09_length,JFz_Scan57.b10_length,JFz_Scan57.b11_length,JFz_Scan57.b12_length,JFz_Scan57.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell02
theorem encoded02 : CandidateParserByteOrder.arrayBytes16 cell02=encodeQM31LE limbs02 := by
  funext i
  fin_cases i <;> rfl
theorem parser02 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell02)=
    ok (some ⟨⟨359451874#u32,28750248#u32⟩,⟨241410532#u32,297010892#u32⟩⟩) :=
  JFr_EncodedCell.parser cell02 limbs02 encoded02
#print axioms encoded02
#print axioms parser02
def cell03 : Array U8 16#usize := ⟨[127#u8,174#u8,2#u8,68#u8,130#u8,15#u8,35#u8,24#u8,77#u8,120#u8,253#u8,99#u8,134#u8,111#u8,113#u8,116#u8],by rfl⟩
def limbs03 : QM31Limbs := ![⟨1141026431,by change 1141026431<2147483647;omega⟩,⟨404950914,by change 404950914<2147483647;omega⟩,⟨1677555789,by change 1677555789<2147483647;omega⟩,⟨1953591174,by change 1953591174<2147483647;omega⟩]
theorem rawCell03 : (raw.drop 48).take 16=cell03.val := by
  simp only [raw,JFz_Scan57.data,JFz_Scan57.j00,JFz_Scan57.j01,JFz_Scan57.j02,JFz_Scan57.j03,JFz_Scan57.j04,JFz_Scan57.j05,JFz_Scan57.j06,JFz_Scan57.j07,JFz_Scan57.j08,JFz_Scan57.j09,JFz_Scan57.j10,JFz_Scan57.j11,JFz_Scan57.j12,JFz_Scan57.b00_length,JFz_Scan57.b01_length,JFz_Scan57.b02_length,JFz_Scan57.b03_length,JFz_Scan57.b04_length,JFz_Scan57.b05_length,JFz_Scan57.b06_length,JFz_Scan57.b07_length,JFz_Scan57.b08_length,JFz_Scan57.b09_length,JFz_Scan57.b10_length,JFz_Scan57.b11_length,JFz_Scan57.b12_length,JFz_Scan57.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell03
theorem encoded03 : CandidateParserByteOrder.arrayBytes16 cell03=encodeQM31LE limbs03 := by
  funext i
  fin_cases i <;> rfl
theorem parser03 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell03)=
    ok (some ⟨⟨1141026431#u32,404950914#u32⟩,⟨1677555789#u32,1953591174#u32⟩⟩) :=
  JFr_EncodedCell.parser cell03 limbs03 encoded03
#print axioms encoded03
#print axioms parser03
def cell04 : Array U8 16#usize := ⟨[214#u8,75#u8,52#u8,14#u8,53#u8,60#u8,130#u8,112#u8,71#u8,68#u8,247#u8,100#u8,47#u8,14#u8,17#u8,125#u8],by rfl⟩
def limbs04 : QM31Limbs := ![⟨238308310,by change 238308310<2147483647;omega⟩,⟨1887583285,by change 1887583285<2147483647;omega⟩,⟨1693926471,by change 1693926471<2147483647;omega⟩,⟨2098269743,by change 2098269743<2147483647;omega⟩]
theorem rawCell04 : (raw.drop 64).take 16=cell04.val := by
  simp only [raw,JFz_Scan57.data,JFz_Scan57.j00,JFz_Scan57.j01,JFz_Scan57.j02,JFz_Scan57.j03,JFz_Scan57.j04,JFz_Scan57.j05,JFz_Scan57.j06,JFz_Scan57.j07,JFz_Scan57.j08,JFz_Scan57.j09,JFz_Scan57.j10,JFz_Scan57.j11,JFz_Scan57.j12,JFz_Scan57.b00_length,JFz_Scan57.b01_length,JFz_Scan57.b02_length,JFz_Scan57.b03_length,JFz_Scan57.b04_length,JFz_Scan57.b05_length,JFz_Scan57.b06_length,JFz_Scan57.b07_length,JFz_Scan57.b08_length,JFz_Scan57.b09_length,JFz_Scan57.b10_length,JFz_Scan57.b11_length,JFz_Scan57.b12_length,JFz_Scan57.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell04
theorem encoded04 : CandidateParserByteOrder.arrayBytes16 cell04=encodeQM31LE limbs04 := by
  funext i
  fin_cases i <;> rfl
theorem parser04 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell04)=
    ok (some ⟨⟨238308310#u32,1887583285#u32⟩,⟨1693926471#u32,2098269743#u32⟩⟩) :=
  JFr_EncodedCell.parser cell04 limbs04 encoded04
#print axioms encoded04
#print axioms parser04
def cell05 : Array U8 16#usize := ⟨[228#u8,111#u8,159#u8,65#u8,152#u8,168#u8,219#u8,10#u8,153#u8,166#u8,250#u8,101#u8,30#u8,213#u8,54#u8,82#u8],by rfl⟩
def limbs05 : QM31Limbs := ![⟨1100967908,by change 1100967908<2147483647;omega⟩,⟨182167704,by change 182167704<2147483647;omega⟩,⟨1710925465,by change 1710925465<2147483647;omega⟩,⟨1379325214,by change 1379325214<2147483647;omega⟩]
theorem rawCell05 : (raw.drop 80).take 16=cell05.val := by
  simp only [raw,JFz_Scan57.data,JFz_Scan57.j00,JFz_Scan57.j01,JFz_Scan57.j02,JFz_Scan57.j03,JFz_Scan57.j04,JFz_Scan57.j05,JFz_Scan57.j06,JFz_Scan57.j07,JFz_Scan57.j08,JFz_Scan57.j09,JFz_Scan57.j10,JFz_Scan57.j11,JFz_Scan57.j12,JFz_Scan57.b00_length,JFz_Scan57.b01_length,JFz_Scan57.b02_length,JFz_Scan57.b03_length,JFz_Scan57.b04_length,JFz_Scan57.b05_length,JFz_Scan57.b06_length,JFz_Scan57.b07_length,JFz_Scan57.b08_length,JFz_Scan57.b09_length,JFz_Scan57.b10_length,JFz_Scan57.b11_length,JFz_Scan57.b12_length,JFz_Scan57.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell05
theorem encoded05 : CandidateParserByteOrder.arrayBytes16 cell05=encodeQM31LE limbs05 := by
  funext i
  fin_cases i <;> rfl
theorem parser05 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell05)=
    ok (some ⟨⟨1100967908#u32,182167704#u32⟩,⟨1710925465#u32,1379325214#u32⟩⟩) :=
  JFr_EncodedCell.parser cell05 limbs05 encoded05
#print axioms encoded05
#print axioms parser05
def cell06 : Array U8 16#usize := ⟨[29#u8,29#u8,173#u8,102#u8,156#u8,168#u8,102#u8,82#u8,137#u8,114#u8,56#u8,23#u8,96#u8,147#u8,131#u8,121#u8],by rfl⟩
def limbs06 : QM31Limbs := ![⟨1722621213,by change 1722621213<2147483647;omega⟩,⟨1382459548,by change 1382459548<2147483647;omega⟩,⟨389575305,by change 389575305<2147483647;omega⟩,⟨2038666080,by change 2038666080<2147483647;omega⟩]
theorem rawCell06 : (raw.drop 96).take 16=cell06.val := by
  simp only [raw,JFz_Scan57.data,JFz_Scan57.j00,JFz_Scan57.j01,JFz_Scan57.j02,JFz_Scan57.j03,JFz_Scan57.j04,JFz_Scan57.j05,JFz_Scan57.j06,JFz_Scan57.j07,JFz_Scan57.j08,JFz_Scan57.j09,JFz_Scan57.j10,JFz_Scan57.j11,JFz_Scan57.j12,JFz_Scan57.b00_length,JFz_Scan57.b01_length,JFz_Scan57.b02_length,JFz_Scan57.b03_length,JFz_Scan57.b04_length,JFz_Scan57.b05_length,JFz_Scan57.b06_length,JFz_Scan57.b07_length,JFz_Scan57.b08_length,JFz_Scan57.b09_length,JFz_Scan57.b10_length,JFz_Scan57.b11_length,JFz_Scan57.b12_length,JFz_Scan57.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell06
theorem encoded06 : CandidateParserByteOrder.arrayBytes16 cell06=encodeQM31LE limbs06 := by
  funext i
  fin_cases i <;> rfl
theorem parser06 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell06)=
    ok (some ⟨⟨1722621213#u32,1382459548#u32⟩,⟨389575305#u32,2038666080#u32⟩⟩) :=
  JFr_EncodedCell.parser cell06 limbs06 encoded06
#print axioms encoded06
#print axioms parser06
def cell07 : Array U8 16#usize := ⟨[0#u8,14#u8,93#u8,113#u8,204#u8,30#u8,164#u8,53#u8,46#u8,186#u8,22#u8,85#u8,237#u8,46#u8,19#u8,15#u8],by rfl⟩
def limbs07 : QM31Limbs := ![⟨1901923840,by change 1901923840<2147483647;omega⟩,⟨899948236,by change 899948236<2147483647;omega⟩,⟨1427552814,by change 1427552814<2147483647;omega⟩,⟨252915437,by change 252915437<2147483647;omega⟩]
theorem rawCell07 : (raw.drop 112).take 16=cell07.val := by
  simp only [raw,JFz_Scan57.data,JFz_Scan57.j00,JFz_Scan57.j01,JFz_Scan57.j02,JFz_Scan57.j03,JFz_Scan57.j04,JFz_Scan57.j05,JFz_Scan57.j06,JFz_Scan57.j07,JFz_Scan57.j08,JFz_Scan57.j09,JFz_Scan57.j10,JFz_Scan57.j11,JFz_Scan57.j12,JFz_Scan57.b00_length,JFz_Scan57.b01_length,JFz_Scan57.b02_length,JFz_Scan57.b03_length,JFz_Scan57.b04_length,JFz_Scan57.b05_length,JFz_Scan57.b06_length,JFz_Scan57.b07_length,JFz_Scan57.b08_length,JFz_Scan57.b09_length,JFz_Scan57.b10_length,JFz_Scan57.b11_length,JFz_Scan57.b12_length,JFz_Scan57.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell07
theorem encoded07 : CandidateParserByteOrder.arrayBytes16 cell07=encodeQM31LE limbs07 := by
  funext i
  fin_cases i <;> rfl
theorem parser07 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell07)=
    ok (some ⟨⟨1901923840#u32,899948236#u32⟩,⟨1427552814#u32,252915437#u32⟩⟩) :=
  JFr_EncodedCell.parser cell07 limbs07 encoded07
#print axioms encoded07
#print axioms parser07
def cell08 : Array U8 16#usize := ⟨[81#u8,174#u8,82#u8,29#u8,31#u8,60#u8,92#u8,95#u8,39#u8,217#u8,159#u8,55#u8,187#u8,59#u8,186#u8,39#u8],by rfl⟩
def limbs08 : QM31Limbs := ![⟨491957841,by change 491957841<2147483647;omega⟩,⟨1599880223,by change 1599880223<2147483647;omega⟩,⟨933222695,by change 933222695<2147483647;omega⟩,⟨666516411,by change 666516411<2147483647;omega⟩]
theorem rawCell08 : (raw.drop 128).take 16=cell08.val := by
  simp only [raw,JFz_Scan57.data,JFz_Scan57.j00,JFz_Scan57.j01,JFz_Scan57.j02,JFz_Scan57.j03,JFz_Scan57.j04,JFz_Scan57.j05,JFz_Scan57.j06,JFz_Scan57.j07,JFz_Scan57.j08,JFz_Scan57.j09,JFz_Scan57.j10,JFz_Scan57.j11,JFz_Scan57.j12,JFz_Scan57.b00_length,JFz_Scan57.b01_length,JFz_Scan57.b02_length,JFz_Scan57.b03_length,JFz_Scan57.b04_length,JFz_Scan57.b05_length,JFz_Scan57.b06_length,JFz_Scan57.b07_length,JFz_Scan57.b08_length,JFz_Scan57.b09_length,JFz_Scan57.b10_length,JFz_Scan57.b11_length,JFz_Scan57.b12_length,JFz_Scan57.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell08
theorem encoded08 : CandidateParserByteOrder.arrayBytes16 cell08=encodeQM31LE limbs08 := by
  funext i
  fin_cases i <;> rfl
theorem parser08 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell08)=
    ok (some ⟨⟨491957841#u32,1599880223#u32⟩,⟨933222695#u32,666516411#u32⟩⟩) :=
  JFr_EncodedCell.parser cell08 limbs08 encoded08
#print axioms encoded08
#print axioms parser08
def cell09 : Array U8 16#usize := ⟨[200#u8,185#u8,104#u8,44#u8,221#u8,168#u8,161#u8,13#u8,113#u8,225#u8,122#u8,44#u8,119#u8,153#u8,136#u8,44#u8],by rfl⟩
def limbs09 : QM31Limbs := ![⟨745060808,by change 745060808<2147483647;omega⟩,⟨228698333,by change 228698333<2147483647;omega⟩,⟨746250609,by change 746250609<2147483647;omega⟩,⟨747149687,by change 747149687<2147483647;omega⟩]
theorem rawCell09 : (raw.drop 144).take 16=cell09.val := by
  simp only [raw,JFz_Scan57.data,JFz_Scan57.j00,JFz_Scan57.j01,JFz_Scan57.j02,JFz_Scan57.j03,JFz_Scan57.j04,JFz_Scan57.j05,JFz_Scan57.j06,JFz_Scan57.j07,JFz_Scan57.j08,JFz_Scan57.j09,JFz_Scan57.j10,JFz_Scan57.j11,JFz_Scan57.j12,JFz_Scan57.b00_length,JFz_Scan57.b01_length,JFz_Scan57.b02_length,JFz_Scan57.b03_length,JFz_Scan57.b04_length,JFz_Scan57.b05_length,JFz_Scan57.b06_length,JFz_Scan57.b07_length,JFz_Scan57.b08_length,JFz_Scan57.b09_length,JFz_Scan57.b10_length,JFz_Scan57.b11_length,JFz_Scan57.b12_length,JFz_Scan57.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell09
theorem encoded09 : CandidateParserByteOrder.arrayBytes16 cell09=encodeQM31LE limbs09 := by
  funext i
  fin_cases i <;> rfl
theorem parser09 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell09)=
    ok (some ⟨⟨745060808#u32,228698333#u32⟩,⟨746250609#u32,747149687#u32⟩⟩) :=
  JFr_EncodedCell.parser cell09 limbs09 encoded09
#print axioms encoded09
#print axioms parser09
def cell10 : Array U8 16#usize := ⟨[220#u8,15#u8,103#u8,33#u8,165#u8,87#u8,74#u8,126#u8,139#u8,175#u8,59#u8,38#u8,34#u8,6#u8,223#u8,16#u8],by rfl⟩
def limbs10 : QM31Limbs := ![⟨560402396,by change 560402396<2147483647;omega⟩,⟨2118801317,by change 2118801317<2147483647;omega⟩,⟨641445771,by change 641445771<2147483647;omega⟩,⟨283051554,by change 283051554<2147483647;omega⟩]
theorem rawCell10 : (raw.drop 160).take 16=cell10.val := by
  simp only [raw,JFz_Scan57.data,JFz_Scan57.j00,JFz_Scan57.j01,JFz_Scan57.j02,JFz_Scan57.j03,JFz_Scan57.j04,JFz_Scan57.j05,JFz_Scan57.j06,JFz_Scan57.j07,JFz_Scan57.j08,JFz_Scan57.j09,JFz_Scan57.j10,JFz_Scan57.j11,JFz_Scan57.j12,JFz_Scan57.b00_length,JFz_Scan57.b01_length,JFz_Scan57.b02_length,JFz_Scan57.b03_length,JFz_Scan57.b04_length,JFz_Scan57.b05_length,JFz_Scan57.b06_length,JFz_Scan57.b07_length,JFz_Scan57.b08_length,JFz_Scan57.b09_length,JFz_Scan57.b10_length,JFz_Scan57.b11_length,JFz_Scan57.b12_length,JFz_Scan57.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell10
theorem encoded10 : CandidateParserByteOrder.arrayBytes16 cell10=encodeQM31LE limbs10 := by
  funext i
  fin_cases i <;> rfl
theorem parser10 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell10)=
    ok (some ⟨⟨560402396#u32,2118801317#u32⟩,⟨641445771#u32,283051554#u32⟩⟩) :=
  JFr_EncodedCell.parser cell10 limbs10 encoded10
#print axioms encoded10
#print axioms parser10
def cell11 : Array U8 16#usize := ⟨[172#u8,40#u8,4#u8,71#u8,240#u8,226#u8,125#u8,103#u8,14#u8,34#u8,153#u8,90#u8,18#u8,34#u8,76#u8,94#u8],by rfl⟩
def limbs11 : QM31Limbs := ![⟨1191454892,by change 1191454892<2147483647;omega⟩,⟨1736303344,by change 1736303344<2147483647;omega⟩,⟨1519985166,by change 1519985166<2147483647;omega⟩,⟨1582047762,by change 1582047762<2147483647;omega⟩]
theorem rawCell11 : (raw.drop 176).take 16=cell11.val := by
  simp only [raw,JFz_Scan57.data,JFz_Scan57.j00,JFz_Scan57.j01,JFz_Scan57.j02,JFz_Scan57.j03,JFz_Scan57.j04,JFz_Scan57.j05,JFz_Scan57.j06,JFz_Scan57.j07,JFz_Scan57.j08,JFz_Scan57.j09,JFz_Scan57.j10,JFz_Scan57.j11,JFz_Scan57.j12,JFz_Scan57.b00_length,JFz_Scan57.b01_length,JFz_Scan57.b02_length,JFz_Scan57.b03_length,JFz_Scan57.b04_length,JFz_Scan57.b05_length,JFz_Scan57.b06_length,JFz_Scan57.b07_length,JFz_Scan57.b08_length,JFz_Scan57.b09_length,JFz_Scan57.b10_length,JFz_Scan57.b11_length,JFz_Scan57.b12_length,JFz_Scan57.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell11
theorem encoded11 : CandidateParserByteOrder.arrayBytes16 cell11=encodeQM31LE limbs11 := by
  funext i
  fin_cases i <;> rfl
theorem parser11 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell11)=
    ok (some ⟨⟨1191454892#u32,1736303344#u32⟩,⟨1519985166#u32,1582047762#u32⟩⟩) :=
  JFr_EncodedCell.parser cell11 limbs11 encoded11
#print axioms encoded11
#print axioms parser11
def cell12 : Array U8 16#usize := ⟨[100#u8,143#u8,212#u8,124#u8,234#u8,7#u8,203#u8,70#u8,205#u8,236#u8,233#u8,69#u8,254#u8,218#u8,124#u8,35#u8],by rfl⟩
def limbs12 : QM31Limbs := ![⟨2094305124,by change 2094305124<2147483647;omega⟩,⟨1187710954,by change 1187710954<2147483647;omega⟩,⟨1172958413,by change 1172958413<2147483647;omega⟩,⟨595385086,by change 595385086<2147483647;omega⟩]
theorem rawCell12 : (raw.drop 192).take 16=cell12.val := by
  simp only [raw,JFz_Scan57.data,JFz_Scan57.j00,JFz_Scan57.j01,JFz_Scan57.j02,JFz_Scan57.j03,JFz_Scan57.j04,JFz_Scan57.j05,JFz_Scan57.j06,JFz_Scan57.j07,JFz_Scan57.j08,JFz_Scan57.j09,JFz_Scan57.j10,JFz_Scan57.j11,JFz_Scan57.j12,JFz_Scan57.b00_length,JFz_Scan57.b01_length,JFz_Scan57.b02_length,JFz_Scan57.b03_length,JFz_Scan57.b04_length,JFz_Scan57.b05_length,JFz_Scan57.b06_length,JFz_Scan57.b07_length,JFz_Scan57.b08_length,JFz_Scan57.b09_length,JFz_Scan57.b10_length,JFz_Scan57.b11_length,JFz_Scan57.b12_length,JFz_Scan57.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell12
theorem encoded12 : CandidateParserByteOrder.arrayBytes16 cell12=encodeQM31LE limbs12 := by
  funext i
  fin_cases i <;> rfl
theorem parser12 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell12)=
    ok (some ⟨⟨2094305124#u32,1187710954#u32⟩,⟨1172958413#u32,595385086#u32⟩⟩) :=
  JFr_EncodedCell.parser cell12 limbs12 encoded12
#print axioms encoded12
#print axioms parser12
def cell13 : Array U8 16#usize := ⟨[116#u8,112#u8,30#u8,71#u8,86#u8,42#u8,152#u8,113#u8,76#u8,14#u8,76#u8,11#u8,242#u8,138#u8,225#u8,52#u8],by rfl⟩
def limbs13 : QM31Limbs := ![⟨1193177204,by change 1193177204<2147483647;omega⟩,⟨1905797718,by change 1905797718<2147483647;omega⟩,⟨189533772,by change 189533772<2147483647;omega⟩,⟨887196402,by change 887196402<2147483647;omega⟩]
theorem rawCell13 : (raw.drop 208).take 16=cell13.val := by
  simp only [raw,JFz_Scan57.data,JFz_Scan57.j00,JFz_Scan57.j01,JFz_Scan57.j02,JFz_Scan57.j03,JFz_Scan57.j04,JFz_Scan57.j05,JFz_Scan57.j06,JFz_Scan57.j07,JFz_Scan57.j08,JFz_Scan57.j09,JFz_Scan57.j10,JFz_Scan57.j11,JFz_Scan57.j12,JFz_Scan57.b00_length,JFz_Scan57.b01_length,JFz_Scan57.b02_length,JFz_Scan57.b03_length,JFz_Scan57.b04_length,JFz_Scan57.b05_length,JFz_Scan57.b06_length,JFz_Scan57.b07_length,JFz_Scan57.b08_length,JFz_Scan57.b09_length,JFz_Scan57.b10_length,JFz_Scan57.b11_length,JFz_Scan57.b12_length,JFz_Scan57.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell13
theorem encoded13 : CandidateParserByteOrder.arrayBytes16 cell13=encodeQM31LE limbs13 := by
  funext i
  fin_cases i <;> rfl
theorem parser13 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell13)=
    ok (some ⟨⟨1193177204#u32,1905797718#u32⟩,⟨189533772#u32,887196402#u32⟩⟩) :=
  JFr_EncodedCell.parser cell13 limbs13 encoded13
#print axioms encoded13
#print axioms parser13
def cell14 : Array U8 16#usize := ⟨[233#u8,177#u8,141#u8,32#u8,10#u8,28#u8,183#u8,79#u8,5#u8,231#u8,243#u8,43#u8,184#u8,191#u8,152#u8,78#u8],by rfl⟩
def limbs14 : QM31Limbs := ![⟨546157033,by change 546157033<2147483647;omega⟩,⟨1337400330,by change 1337400330<2147483647;omega⟩,⟨737404677,by change 737404677<2147483647;omega⟩,⟨1318633400,by change 1318633400<2147483647;omega⟩]
theorem rawCell14 : (raw.drop 224).take 16=cell14.val := by
  simp only [raw,JFz_Scan57.data,JFz_Scan57.j00,JFz_Scan57.j01,JFz_Scan57.j02,JFz_Scan57.j03,JFz_Scan57.j04,JFz_Scan57.j05,JFz_Scan57.j06,JFz_Scan57.j07,JFz_Scan57.j08,JFz_Scan57.j09,JFz_Scan57.j10,JFz_Scan57.j11,JFz_Scan57.j12,JFz_Scan57.b00_length,JFz_Scan57.b01_length,JFz_Scan57.b02_length,JFz_Scan57.b03_length,JFz_Scan57.b04_length,JFz_Scan57.b05_length,JFz_Scan57.b06_length,JFz_Scan57.b07_length,JFz_Scan57.b08_length,JFz_Scan57.b09_length,JFz_Scan57.b10_length,JFz_Scan57.b11_length,JFz_Scan57.b12_length,JFz_Scan57.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell14
theorem encoded14 : CandidateParserByteOrder.arrayBytes16 cell14=encodeQM31LE limbs14 := by
  funext i
  fin_cases i <;> rfl
theorem parser14 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell14)=
    ok (some ⟨⟨546157033#u32,1337400330#u32⟩,⟨737404677#u32,1318633400#u32⟩⟩) :=
  JFr_EncodedCell.parser cell14 limbs14 encoded14
#print axioms encoded14
#print axioms parser14
def cell15 : Array U8 16#usize := ⟨[93#u8,208#u8,65#u8,13#u8,70#u8,131#u8,220#u8,113#u8,208#u8,128#u8,253#u8,17#u8,226#u8,226#u8,25#u8,99#u8],by rfl⟩
def limbs15 : QM31Limbs := ![⟨222416989,by change 222416989<2147483647;omega⟩,⟨1910276934,by change 1910276934<2147483647;omega⟩,⟨301826256,by change 301826256<2147483647;omega⟩,⟨1662640866,by change 1662640866<2147483647;omega⟩]
theorem rawCell15 : (raw.drop 240).take 16=cell15.val := by
  simp only [raw,JFz_Scan57.data,JFz_Scan57.j00,JFz_Scan57.j01,JFz_Scan57.j02,JFz_Scan57.j03,JFz_Scan57.j04,JFz_Scan57.j05,JFz_Scan57.j06,JFz_Scan57.j07,JFz_Scan57.j08,JFz_Scan57.j09,JFz_Scan57.j10,JFz_Scan57.j11,JFz_Scan57.j12,JFz_Scan57.b00_length,JFz_Scan57.b01_length,JFz_Scan57.b02_length,JFz_Scan57.b03_length,JFz_Scan57.b04_length,JFz_Scan57.b05_length,JFz_Scan57.b06_length,JFz_Scan57.b07_length,JFz_Scan57.b08_length,JFz_Scan57.b09_length,JFz_Scan57.b10_length,JFz_Scan57.b11_length,JFz_Scan57.b12_length,JFz_Scan57.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell15
theorem encoded15 : CandidateParserByteOrder.arrayBytes16 cell15=encodeQM31LE limbs15 := by
  funext i
  fin_cases i <;> rfl
theorem parser15 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell15)=
    ok (some ⟨⟨222416989#u32,1910276934#u32⟩,⟨301826256#u32,1662640866#u32⟩⟩) :=
  JFr_EncodedCell.parser cell15 limbs15 encoded15
#print axioms encoded15
#print axioms parser15
def cell16 : Array U8 16#usize := ⟨[101#u8,75#u8,216#u8,126#u8,74#u8,124#u8,169#u8,76#u8,46#u8,136#u8,250#u8,93#u8,219#u8,157#u8,245#u8,105#u8],by rfl⟩
def limbs16 : QM31Limbs := ![⟨2128104293,by change 2128104293<2147483647;omega⟩,⟨1286175818,by change 1286175818<2147483647;omega⟩,⟨1576699950,by change 1576699950<2147483647;omega⟩,⟨1777704411,by change 1777704411<2147483647;omega⟩]
theorem rawCell16 : (raw.drop 256).take 16=cell16.val := by
  simp only [raw,JFz_Scan57.data,JFz_Scan57.j00,JFz_Scan57.j01,JFz_Scan57.j02,JFz_Scan57.j03,JFz_Scan57.j04,JFz_Scan57.j05,JFz_Scan57.j06,JFz_Scan57.j07,JFz_Scan57.j08,JFz_Scan57.j09,JFz_Scan57.j10,JFz_Scan57.j11,JFz_Scan57.j12,JFz_Scan57.b00_length,JFz_Scan57.b01_length,JFz_Scan57.b02_length,JFz_Scan57.b03_length,JFz_Scan57.b04_length,JFz_Scan57.b05_length,JFz_Scan57.b06_length,JFz_Scan57.b07_length,JFz_Scan57.b08_length,JFz_Scan57.b09_length,JFz_Scan57.b10_length,JFz_Scan57.b11_length,JFz_Scan57.b12_length,JFz_Scan57.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell16
theorem encoded16 : CandidateParserByteOrder.arrayBytes16 cell16=encodeQM31LE limbs16 := by
  funext i
  fin_cases i <;> rfl
theorem parser16 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell16)=
    ok (some ⟨⟨2128104293#u32,1286175818#u32⟩,⟨1576699950#u32,1777704411#u32⟩⟩) :=
  JFr_EncodedCell.parser cell16 limbs16 encoded16
#print axioms encoded16
#print axioms parser16
def cell17 : Array U8 16#usize := ⟨[121#u8,81#u8,59#u8,100#u8,21#u8,28#u8,248#u8,59#u8,161#u8,164#u8,187#u8,2#u8,112#u8,72#u8,150#u8,126#u8],by rfl⟩
def limbs17 : QM31Limbs := ![⟨1681609081,by change 1681609081<2147483647;omega⟩,⟨1006115861,by change 1006115861<2147483647;omega⟩,⟨45851809,by change 45851809<2147483647;omega⟩,⟨2123778160,by change 2123778160<2147483647;omega⟩]
theorem rawCell17 : (raw.drop 272).take 16=cell17.val := by
  simp only [raw,JFz_Scan57.data,JFz_Scan57.j00,JFz_Scan57.j01,JFz_Scan57.j02,JFz_Scan57.j03,JFz_Scan57.j04,JFz_Scan57.j05,JFz_Scan57.j06,JFz_Scan57.j07,JFz_Scan57.j08,JFz_Scan57.j09,JFz_Scan57.j10,JFz_Scan57.j11,JFz_Scan57.j12,JFz_Scan57.b00_length,JFz_Scan57.b01_length,JFz_Scan57.b02_length,JFz_Scan57.b03_length,JFz_Scan57.b04_length,JFz_Scan57.b05_length,JFz_Scan57.b06_length,JFz_Scan57.b07_length,JFz_Scan57.b08_length,JFz_Scan57.b09_length,JFz_Scan57.b10_length,JFz_Scan57.b11_length,JFz_Scan57.b12_length,JFz_Scan57.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell17
theorem encoded17 : CandidateParserByteOrder.arrayBytes16 cell17=encodeQM31LE limbs17 := by
  funext i
  fin_cases i <;> rfl
theorem parser17 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell17)=
    ok (some ⟨⟨1681609081#u32,1006115861#u32⟩,⟨45851809#u32,2123778160#u32⟩⟩) :=
  JFr_EncodedCell.parser cell17 limbs17 encoded17
#print axioms encoded17
#print axioms parser17
def cell18 : Array U8 16#usize := ⟨[171#u8,31#u8,72#u8,118#u8,152#u8,228#u8,24#u8,98#u8,146#u8,102#u8,70#u8,69#u8,65#u8,56#u8,161#u8,104#u8],by rfl⟩
def limbs18 : QM31Limbs := ![⟨1984438187,by change 1984438187<2147483647;omega⟩,⟨1645798552,by change 1645798552<2147483647;omega⟩,⟨1162241682,by change 1162241682<2147483647;omega⟩,⟨1755396161,by change 1755396161<2147483647;omega⟩]
theorem rawCell18 : (raw.drop 288).take 16=cell18.val := by
  simp only [raw,JFz_Scan57.data,JFz_Scan57.j00,JFz_Scan57.j01,JFz_Scan57.j02,JFz_Scan57.j03,JFz_Scan57.j04,JFz_Scan57.j05,JFz_Scan57.j06,JFz_Scan57.j07,JFz_Scan57.j08,JFz_Scan57.j09,JFz_Scan57.j10,JFz_Scan57.j11,JFz_Scan57.j12,JFz_Scan57.b00_length,JFz_Scan57.b01_length,JFz_Scan57.b02_length,JFz_Scan57.b03_length,JFz_Scan57.b04_length,JFz_Scan57.b05_length,JFz_Scan57.b06_length,JFz_Scan57.b07_length,JFz_Scan57.b08_length,JFz_Scan57.b09_length,JFz_Scan57.b10_length,JFz_Scan57.b11_length,JFz_Scan57.b12_length,JFz_Scan57.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell18
theorem encoded18 : CandidateParserByteOrder.arrayBytes16 cell18=encodeQM31LE limbs18 := by
  funext i
  fin_cases i <;> rfl
theorem parser18 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell18)=
    ok (some ⟨⟨1984438187#u32,1645798552#u32⟩,⟨1162241682#u32,1755396161#u32⟩⟩) :=
  JFr_EncodedCell.parser cell18 limbs18 encoded18
#print axioms encoded18
#print axioms parser18
def cell19 : Array U8 16#usize := ⟨[142#u8,72#u8,45#u8,38#u8,187#u8,226#u8,201#u8,50#u8,217#u8,58#u8,239#u8,15#u8,155#u8,25#u8,228#u8,54#u8],by rfl⟩
def limbs19 : QM31Limbs := ![⟨640501902,by change 640501902<2147483647;omega⟩,⟨852091579,by change 852091579<2147483647;omega⟩,⟨267336409,by change 267336409<2147483647;omega⟩,⟨920918427,by change 920918427<2147483647;omega⟩]
theorem rawCell19 : (raw.drop 304).take 16=cell19.val := by
  simp only [raw,JFz_Scan57.data,JFz_Scan57.j00,JFz_Scan57.j01,JFz_Scan57.j02,JFz_Scan57.j03,JFz_Scan57.j04,JFz_Scan57.j05,JFz_Scan57.j06,JFz_Scan57.j07,JFz_Scan57.j08,JFz_Scan57.j09,JFz_Scan57.j10,JFz_Scan57.j11,JFz_Scan57.j12,JFz_Scan57.b00_length,JFz_Scan57.b01_length,JFz_Scan57.b02_length,JFz_Scan57.b03_length,JFz_Scan57.b04_length,JFz_Scan57.b05_length,JFz_Scan57.b06_length,JFz_Scan57.b07_length,JFz_Scan57.b08_length,JFz_Scan57.b09_length,JFz_Scan57.b10_length,JFz_Scan57.b11_length,JFz_Scan57.b12_length,JFz_Scan57.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell19
theorem encoded19 : CandidateParserByteOrder.arrayBytes16 cell19=encodeQM31LE limbs19 := by
  funext i
  fin_cases i <;> rfl
theorem parser19 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell19)=
    ok (some ⟨⟨640501902#u32,852091579#u32⟩,⟨267336409#u32,920918427#u32⟩⟩) :=
  JFr_EncodedCell.parser cell19 limbs19 encoded19
#print axioms encoded19
#print axioms parser19
def cell20 : Array U8 16#usize := ⟨[227#u8,244#u8,20#u8,54#u8,103#u8,33#u8,107#u8,125#u8,52#u8,192#u8,9#u8,104#u8,188#u8,152#u8,158#u8,95#u8],by rfl⟩
def limbs20 : QM31Limbs := ![⟨907343075,by change 907343075<2147483647;omega⟩,⟨2104172903,by change 2104172903<2147483647;omega⟩,⟨1745469492,by change 1745469492<2147483647;omega⟩,⟨1604229308,by change 1604229308<2147483647;omega⟩]
theorem rawCell20 : (raw.drop 320).take 16=cell20.val := by
  simp only [raw,JFz_Scan57.data,JFz_Scan57.j00,JFz_Scan57.j01,JFz_Scan57.j02,JFz_Scan57.j03,JFz_Scan57.j04,JFz_Scan57.j05,JFz_Scan57.j06,JFz_Scan57.j07,JFz_Scan57.j08,JFz_Scan57.j09,JFz_Scan57.j10,JFz_Scan57.j11,JFz_Scan57.j12,JFz_Scan57.b00_length,JFz_Scan57.b01_length,JFz_Scan57.b02_length,JFz_Scan57.b03_length,JFz_Scan57.b04_length,JFz_Scan57.b05_length,JFz_Scan57.b06_length,JFz_Scan57.b07_length,JFz_Scan57.b08_length,JFz_Scan57.b09_length,JFz_Scan57.b10_length,JFz_Scan57.b11_length,JFz_Scan57.b12_length,JFz_Scan57.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell20
theorem encoded20 : CandidateParserByteOrder.arrayBytes16 cell20=encodeQM31LE limbs20 := by
  funext i
  fin_cases i <;> rfl
theorem parser20 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell20)=
    ok (some ⟨⟨907343075#u32,2104172903#u32⟩,⟨1745469492#u32,1604229308#u32⟩⟩) :=
  JFr_EncodedCell.parser cell20 limbs20 encoded20
#print axioms encoded20
#print axioms parser20
def cell21 : Array U8 16#usize := ⟨[150#u8,132#u8,150#u8,64#u8,104#u8,45#u8,10#u8,89#u8,224#u8,148#u8,99#u8,16#u8,114#u8,50#u8,128#u8,125#u8],by rfl⟩
def limbs21 : QM31Limbs := ![⟨1083606166,by change 1083606166<2147483647;omega⟩,⟨1493839208,by change 1493839208<2147483647;omega⟩,⟨274961632,by change 274961632<2147483647;omega⟩,⟨2105553522,by change 2105553522<2147483647;omega⟩]
theorem rawCell21 : (raw.drop 336).take 16=cell21.val := by
  simp only [raw,JFz_Scan57.data,JFz_Scan57.j00,JFz_Scan57.j01,JFz_Scan57.j02,JFz_Scan57.j03,JFz_Scan57.j04,JFz_Scan57.j05,JFz_Scan57.j06,JFz_Scan57.j07,JFz_Scan57.j08,JFz_Scan57.j09,JFz_Scan57.j10,JFz_Scan57.j11,JFz_Scan57.j12,JFz_Scan57.b00_length,JFz_Scan57.b01_length,JFz_Scan57.b02_length,JFz_Scan57.b03_length,JFz_Scan57.b04_length,JFz_Scan57.b05_length,JFz_Scan57.b06_length,JFz_Scan57.b07_length,JFz_Scan57.b08_length,JFz_Scan57.b09_length,JFz_Scan57.b10_length,JFz_Scan57.b11_length,JFz_Scan57.b12_length,JFz_Scan57.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell21
theorem encoded21 : CandidateParserByteOrder.arrayBytes16 cell21=encodeQM31LE limbs21 := by
  funext i
  fin_cases i <;> rfl
theorem parser21 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell21)=
    ok (some ⟨⟨1083606166#u32,1493839208#u32⟩,⟨274961632#u32,2105553522#u32⟩⟩) :=
  JFr_EncodedCell.parser cell21 limbs21 encoded21
#print axioms encoded21
#print axioms parser21
def cell22 : Array U8 16#usize := ⟨[13#u8,183#u8,167#u8,14#u8,232#u8,122#u8,254#u8,29#u8,148#u8,54#u8,63#u8,100#u8,77#u8,11#u8,102#u8,36#u8],by rfl⟩
def limbs22 : QM31Limbs := ![⟨245872397,by change 245872397<2147483647;omega⟩,⟨503216872,by change 503216872<2147483647;omega⟩,⟨1681864340,by change 1681864340<2147483647;omega⟩,⟨610667341,by change 610667341<2147483647;omega⟩]
theorem rawCell22 : (raw.drop 352).take 16=cell22.val := by
  simp only [raw,JFz_Scan57.data,JFz_Scan57.j00,JFz_Scan57.j01,JFz_Scan57.j02,JFz_Scan57.j03,JFz_Scan57.j04,JFz_Scan57.j05,JFz_Scan57.j06,JFz_Scan57.j07,JFz_Scan57.j08,JFz_Scan57.j09,JFz_Scan57.j10,JFz_Scan57.j11,JFz_Scan57.j12,JFz_Scan57.b00_length,JFz_Scan57.b01_length,JFz_Scan57.b02_length,JFz_Scan57.b03_length,JFz_Scan57.b04_length,JFz_Scan57.b05_length,JFz_Scan57.b06_length,JFz_Scan57.b07_length,JFz_Scan57.b08_length,JFz_Scan57.b09_length,JFz_Scan57.b10_length,JFz_Scan57.b11_length,JFz_Scan57.b12_length,JFz_Scan57.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell22
theorem encoded22 : CandidateParserByteOrder.arrayBytes16 cell22=encodeQM31LE limbs22 := by
  funext i
  fin_cases i <;> rfl
theorem parser22 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell22)=
    ok (some ⟨⟨245872397#u32,503216872#u32⟩,⟨1681864340#u32,610667341#u32⟩⟩) :=
  JFr_EncodedCell.parser cell22 limbs22 encoded22
#print axioms encoded22
#print axioms parser22
def cell23 : Array U8 16#usize := ⟨[247#u8,150#u8,160#u8,26#u8,122#u8,218#u8,49#u8,19#u8,76#u8,63#u8,120#u8,86#u8,80#u8,28#u8,157#u8,6#u8],by rfl⟩
def limbs23 : QM31Limbs := ![⟨446732023,by change 446732023<2147483647;omega⟩,⟨322034298,by change 322034298<2147483647;omega⟩,⟨1450721100,by change 1450721100<2147483647;omega⟩,⟨110959696,by change 110959696<2147483647;omega⟩]
theorem rawCell23 : (raw.drop 368).take 16=cell23.val := by
  simp only [raw,JFz_Scan57.data,JFz_Scan57.j00,JFz_Scan57.j01,JFz_Scan57.j02,JFz_Scan57.j03,JFz_Scan57.j04,JFz_Scan57.j05,JFz_Scan57.j06,JFz_Scan57.j07,JFz_Scan57.j08,JFz_Scan57.j09,JFz_Scan57.j10,JFz_Scan57.j11,JFz_Scan57.j12,JFz_Scan57.b00_length,JFz_Scan57.b01_length,JFz_Scan57.b02_length,JFz_Scan57.b03_length,JFz_Scan57.b04_length,JFz_Scan57.b05_length,JFz_Scan57.b06_length,JFz_Scan57.b07_length,JFz_Scan57.b08_length,JFz_Scan57.b09_length,JFz_Scan57.b10_length,JFz_Scan57.b11_length,JFz_Scan57.b12_length,JFz_Scan57.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell23
theorem encoded23 : CandidateParserByteOrder.arrayBytes16 cell23=encodeQM31LE limbs23 := by
  funext i
  fin_cases i <;> rfl
theorem parser23 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell23)=
    ok (some ⟨⟨446732023#u32,322034298#u32⟩,⟨1450721100#u32,110959696#u32⟩⟩) :=
  JFr_EncodedCell.parser cell23 limbs23 encoded23
#print axioms encoded23
#print axioms parser23
def cell24 : Array U8 16#usize := ⟨[111#u8,94#u8,225#u8,16#u8,218#u8,75#u8,111#u8,105#u8,152#u8,134#u8,116#u8,52#u8,171#u8,70#u8,86#u8,126#u8],by rfl⟩
def limbs24 : QM31Limbs := ![⟨283205231,by change 283205231<2147483647;omega⟩,⟨1768901594,by change 1768901594<2147483647;omega⟩,⟨880051864,by change 880051864<2147483647;omega⟩,⟨2119583403,by change 2119583403<2147483647;omega⟩]
theorem rawCell24 : (raw.drop 384).take 16=cell24.val := by
  simp only [raw,JFz_Scan57.data,JFz_Scan57.j00,JFz_Scan57.j01,JFz_Scan57.j02,JFz_Scan57.j03,JFz_Scan57.j04,JFz_Scan57.j05,JFz_Scan57.j06,JFz_Scan57.j07,JFz_Scan57.j08,JFz_Scan57.j09,JFz_Scan57.j10,JFz_Scan57.j11,JFz_Scan57.j12,JFz_Scan57.b00_length,JFz_Scan57.b01_length,JFz_Scan57.b02_length,JFz_Scan57.b03_length,JFz_Scan57.b04_length,JFz_Scan57.b05_length,JFz_Scan57.b06_length,JFz_Scan57.b07_length,JFz_Scan57.b08_length,JFz_Scan57.b09_length,JFz_Scan57.b10_length,JFz_Scan57.b11_length,JFz_Scan57.b12_length,JFz_Scan57.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell24
theorem encoded24 : CandidateParserByteOrder.arrayBytes16 cell24=encodeQM31LE limbs24 := by
  funext i
  fin_cases i <;> rfl
theorem parser24 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell24)=
    ok (some ⟨⟨283205231#u32,1768901594#u32⟩,⟨880051864#u32,2119583403#u32⟩⟩) :=
  JFr_EncodedCell.parser cell24 limbs24 encoded24
#print axioms encoded24
#print axioms parser24
def cell25 : Array U8 16#usize := ⟨[112#u8,91#u8,121#u8,52#u8,53#u8,239#u8,29#u8,100#u8,144#u8,231#u8,27#u8,20#u8,169#u8,155#u8,15#u8,8#u8],by rfl⟩
def limbs25 : QM31Limbs := ![⟨880368496,by change 880368496<2147483647;omega⟩,⟨1679683381,by change 1679683381<2147483647;omega⟩,⟨337373072,by change 337373072<2147483647;omega⟩,⟨135240617,by change 135240617<2147483647;omega⟩]
theorem rawCell25 : (raw.drop 400).take 16=cell25.val := by
  simp only [raw,JFz_Scan57.data,JFz_Scan57.j00,JFz_Scan57.j01,JFz_Scan57.j02,JFz_Scan57.j03,JFz_Scan57.j04,JFz_Scan57.j05,JFz_Scan57.j06,JFz_Scan57.j07,JFz_Scan57.j08,JFz_Scan57.j09,JFz_Scan57.j10,JFz_Scan57.j11,JFz_Scan57.j12,JFz_Scan57.b00_length,JFz_Scan57.b01_length,JFz_Scan57.b02_length,JFz_Scan57.b03_length,JFz_Scan57.b04_length,JFz_Scan57.b05_length,JFz_Scan57.b06_length,JFz_Scan57.b07_length,JFz_Scan57.b08_length,JFz_Scan57.b09_length,JFz_Scan57.b10_length,JFz_Scan57.b11_length,JFz_Scan57.b12_length,JFz_Scan57.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell25
theorem encoded25 : CandidateParserByteOrder.arrayBytes16 cell25=encodeQM31LE limbs25 := by
  funext i
  fin_cases i <;> rfl
theorem parser25 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell25)=
    ok (some ⟨⟨880368496#u32,1679683381#u32⟩,⟨337373072#u32,135240617#u32⟩⟩) :=
  JFr_EncodedCell.parser cell25 limbs25 encoded25
#print axioms encoded25
#print axioms parser25
def cell26 : Array U8 16#usize := ⟨[76#u8,101#u8,219#u8,73#u8,38#u8,167#u8,221#u8,91#u8,117#u8,103#u8,238#u8,70#u8,222#u8,253#u8,164#u8,4#u8],by rfl⟩
def limbs26 : QM31Limbs := ![⟨1239115084,by change 1239115084<2147483647;omega⟩,⟨1541252902,by change 1541252902<2147483647;omega⟩,⟨1190029173,by change 1190029173<2147483647;omega⟩,⟨77921758,by change 77921758<2147483647;omega⟩]
theorem rawCell26 : (raw.drop 416).take 16=cell26.val := by
  simp only [raw,JFz_Scan57.data,JFz_Scan57.j00,JFz_Scan57.j01,JFz_Scan57.j02,JFz_Scan57.j03,JFz_Scan57.j04,JFz_Scan57.j05,JFz_Scan57.j06,JFz_Scan57.j07,JFz_Scan57.j08,JFz_Scan57.j09,JFz_Scan57.j10,JFz_Scan57.j11,JFz_Scan57.j12,JFz_Scan57.b00_length,JFz_Scan57.b01_length,JFz_Scan57.b02_length,JFz_Scan57.b03_length,JFz_Scan57.b04_length,JFz_Scan57.b05_length,JFz_Scan57.b06_length,JFz_Scan57.b07_length,JFz_Scan57.b08_length,JFz_Scan57.b09_length,JFz_Scan57.b10_length,JFz_Scan57.b11_length,JFz_Scan57.b12_length,JFz_Scan57.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell26
theorem encoded26 : CandidateParserByteOrder.arrayBytes16 cell26=encodeQM31LE limbs26 := by
  funext i
  fin_cases i <;> rfl
theorem parser26 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell26)=
    ok (some ⟨⟨1239115084#u32,1541252902#u32⟩,⟨1190029173#u32,77921758#u32⟩⟩) :=
  JFr_EncodedCell.parser cell26 limbs26 encoded26
#print axioms encoded26
#print axioms parser26
def cell27 : Array U8 16#usize := ⟨[147#u8,230#u8,83#u8,88#u8,148#u8,124#u8,32#u8,116#u8,75#u8,100#u8,7#u8,109#u8,178#u8,207#u8,144#u8,40#u8],by rfl⟩
def limbs27 : QM31Limbs := ![⟨1481893523,by change 1481893523<2147483647;omega⟩,⟨1948286100,by change 1948286100<2147483647;omega⟩,⟨1829200971,by change 1829200971<2147483647;omega⟩,⟨680578994,by change 680578994<2147483647;omega⟩]
theorem rawCell27 : (raw.drop 432).take 16=cell27.val := by
  simp only [raw,JFz_Scan57.data,JFz_Scan57.j00,JFz_Scan57.j01,JFz_Scan57.j02,JFz_Scan57.j03,JFz_Scan57.j04,JFz_Scan57.j05,JFz_Scan57.j06,JFz_Scan57.j07,JFz_Scan57.j08,JFz_Scan57.j09,JFz_Scan57.j10,JFz_Scan57.j11,JFz_Scan57.j12,JFz_Scan57.b00_length,JFz_Scan57.b01_length,JFz_Scan57.b02_length,JFz_Scan57.b03_length,JFz_Scan57.b04_length,JFz_Scan57.b05_length,JFz_Scan57.b06_length,JFz_Scan57.b07_length,JFz_Scan57.b08_length,JFz_Scan57.b09_length,JFz_Scan57.b10_length,JFz_Scan57.b11_length,JFz_Scan57.b12_length,JFz_Scan57.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell27
theorem encoded27 : CandidateParserByteOrder.arrayBytes16 cell27=encodeQM31LE limbs27 := by
  funext i
  fin_cases i <;> rfl
theorem parser27 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell27)=
    ok (some ⟨⟨1481893523#u32,1948286100#u32⟩,⟨1829200971#u32,680578994#u32⟩⟩) :=
  JFr_EncodedCell.parser cell27 limbs27 encoded27
#print axioms encoded27
#print axioms parser27
end AspisR1.JFr_Bytes09
