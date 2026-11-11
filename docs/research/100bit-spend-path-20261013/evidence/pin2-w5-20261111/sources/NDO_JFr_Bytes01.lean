import NDO_JFr_Data01
import NDO_JFr_EncodedCell
import NDO_JFz_Scan49
set_option autoImplicit false
namespace AspisR1.JFr_Bytes01
open Aeneas Aeneas.Std Result RetainedFieldByteCodec
open AspisR1PublicPreparation
open AspisS1ExtractedRoundChildren
def raw : List U8 := JFz_Scan49.data
theorem rawLength : raw.length=448 := JFz_Scan49.length
#print axioms rawLength
theorem selected : (JFx_NativeBytes.proof.val.drop 629).take 448=raw := JFz_Scan49.selected
#print axioms selected
def cell00 : Array U8 16#usize := ⟨[213#u8,14#u8,6#u8,6#u8,2#u8,183#u8,59#u8,78#u8,93#u8,123#u8,13#u8,39#u8,57#u8,76#u8,52#u8,108#u8],by rfl⟩
def limbs00 : QM31Limbs := ![⟨101060309,by change 101060309<2147483647;omega⟩,⟨1312536322,by change 1312536322<2147483647;omega⟩,⟨655194973,by change 655194973<2147483647;omega⟩,⟨1815366713,by change 1815366713<2147483647;omega⟩]
theorem rawCell00 : (raw.drop 0).take 16=cell00.val := by
  simp only [raw,JFz_Scan49.data,JFz_Scan49.j00,JFz_Scan49.j01,JFz_Scan49.j02,JFz_Scan49.j03,JFz_Scan49.j04,JFz_Scan49.j05,JFz_Scan49.j06,JFz_Scan49.j07,JFz_Scan49.j08,JFz_Scan49.j09,JFz_Scan49.j10,JFz_Scan49.j11,JFz_Scan49.j12,JFz_Scan49.b00_length,JFz_Scan49.b01_length,JFz_Scan49.b02_length,JFz_Scan49.b03_length,JFz_Scan49.b04_length,JFz_Scan49.b05_length,JFz_Scan49.b06_length,JFz_Scan49.b07_length,JFz_Scan49.b08_length,JFz_Scan49.b09_length,JFz_Scan49.b10_length,JFz_Scan49.b11_length,JFz_Scan49.b12_length,JFz_Scan49.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell00
theorem encoded00 : CandidateParserByteOrder.arrayBytes16 cell00=encodeQM31LE limbs00 := by
  funext i
  fin_cases i <;> rfl
theorem parser00 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell00)=
    ok (some ⟨⟨101060309#u32,1312536322#u32⟩,⟨655194973#u32,1815366713#u32⟩⟩) :=
  JFr_EncodedCell.parser cell00 limbs00 encoded00
#print axioms encoded00
#print axioms parser00
def cell01 : Array U8 16#usize := ⟨[205#u8,12#u8,57#u8,69#u8,184#u8,223#u8,85#u8,120#u8,45#u8,72#u8,2#u8,17#u8,22#u8,14#u8,91#u8,121#u8],by rfl⟩
def limbs01 : QM31Limbs := ![⟨1161366733,by change 1161366733<2147483647;omega⟩,⟨2018893752,by change 2018893752<2147483647;omega⟩,⟨285362221,by change 285362221<2147483647;omega⟩,⟨2036010518,by change 2036010518<2147483647;omega⟩]
theorem rawCell01 : (raw.drop 16).take 16=cell01.val := by
  simp only [raw,JFz_Scan49.data,JFz_Scan49.j00,JFz_Scan49.j01,JFz_Scan49.j02,JFz_Scan49.j03,JFz_Scan49.j04,JFz_Scan49.j05,JFz_Scan49.j06,JFz_Scan49.j07,JFz_Scan49.j08,JFz_Scan49.j09,JFz_Scan49.j10,JFz_Scan49.j11,JFz_Scan49.j12,JFz_Scan49.b00_length,JFz_Scan49.b01_length,JFz_Scan49.b02_length,JFz_Scan49.b03_length,JFz_Scan49.b04_length,JFz_Scan49.b05_length,JFz_Scan49.b06_length,JFz_Scan49.b07_length,JFz_Scan49.b08_length,JFz_Scan49.b09_length,JFz_Scan49.b10_length,JFz_Scan49.b11_length,JFz_Scan49.b12_length,JFz_Scan49.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell01
theorem encoded01 : CandidateParserByteOrder.arrayBytes16 cell01=encodeQM31LE limbs01 := by
  funext i
  fin_cases i <;> rfl
theorem parser01 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell01)=
    ok (some ⟨⟨1161366733#u32,2018893752#u32⟩,⟨285362221#u32,2036010518#u32⟩⟩) :=
  JFr_EncodedCell.parser cell01 limbs01 encoded01
#print axioms encoded01
#print axioms parser01
def cell02 : Array U8 16#usize := ⟨[30#u8,0#u8,201#u8,108#u8,155#u8,98#u8,192#u8,30#u8,151#u8,185#u8,144#u8,27#u8,112#u8,79#u8,203#u8,24#u8],by rfl⟩
def limbs02 : QM31Limbs := ![⟨1825112094,by change 1825112094<2147483647;omega⟩,⟨515924635,by change 515924635<2147483647;omega⟩,⟨462469527,by change 462469527<2147483647;omega⟩,⟨415977328,by change 415977328<2147483647;omega⟩]
theorem rawCell02 : (raw.drop 32).take 16=cell02.val := by
  simp only [raw,JFz_Scan49.data,JFz_Scan49.j00,JFz_Scan49.j01,JFz_Scan49.j02,JFz_Scan49.j03,JFz_Scan49.j04,JFz_Scan49.j05,JFz_Scan49.j06,JFz_Scan49.j07,JFz_Scan49.j08,JFz_Scan49.j09,JFz_Scan49.j10,JFz_Scan49.j11,JFz_Scan49.j12,JFz_Scan49.b00_length,JFz_Scan49.b01_length,JFz_Scan49.b02_length,JFz_Scan49.b03_length,JFz_Scan49.b04_length,JFz_Scan49.b05_length,JFz_Scan49.b06_length,JFz_Scan49.b07_length,JFz_Scan49.b08_length,JFz_Scan49.b09_length,JFz_Scan49.b10_length,JFz_Scan49.b11_length,JFz_Scan49.b12_length,JFz_Scan49.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell02
theorem encoded02 : CandidateParserByteOrder.arrayBytes16 cell02=encodeQM31LE limbs02 := by
  funext i
  fin_cases i <;> rfl
theorem parser02 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell02)=
    ok (some ⟨⟨1825112094#u32,515924635#u32⟩,⟨462469527#u32,415977328#u32⟩⟩) :=
  JFr_EncodedCell.parser cell02 limbs02 encoded02
#print axioms encoded02
#print axioms parser02
def cell03 : Array U8 16#usize := ⟨[13#u8,190#u8,207#u8,10#u8,19#u8,83#u8,193#u8,8#u8,234#u8,82#u8,217#u8,94#u8,156#u8,114#u8,20#u8,66#u8],by rfl⟩
def limbs03 : QM31Limbs := ![⟨181386765,by change 181386765<2147483647;omega⟩,⟨146887443,by change 146887443<2147483647;omega⟩,⟨1591300842,by change 1591300842<2147483647;omega⟩,⟨1108636316,by change 1108636316<2147483647;omega⟩]
theorem rawCell03 : (raw.drop 48).take 16=cell03.val := by
  simp only [raw,JFz_Scan49.data,JFz_Scan49.j00,JFz_Scan49.j01,JFz_Scan49.j02,JFz_Scan49.j03,JFz_Scan49.j04,JFz_Scan49.j05,JFz_Scan49.j06,JFz_Scan49.j07,JFz_Scan49.j08,JFz_Scan49.j09,JFz_Scan49.j10,JFz_Scan49.j11,JFz_Scan49.j12,JFz_Scan49.b00_length,JFz_Scan49.b01_length,JFz_Scan49.b02_length,JFz_Scan49.b03_length,JFz_Scan49.b04_length,JFz_Scan49.b05_length,JFz_Scan49.b06_length,JFz_Scan49.b07_length,JFz_Scan49.b08_length,JFz_Scan49.b09_length,JFz_Scan49.b10_length,JFz_Scan49.b11_length,JFz_Scan49.b12_length,JFz_Scan49.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell03
theorem encoded03 : CandidateParserByteOrder.arrayBytes16 cell03=encodeQM31LE limbs03 := by
  funext i
  fin_cases i <;> rfl
theorem parser03 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell03)=
    ok (some ⟨⟨181386765#u32,146887443#u32⟩,⟨1591300842#u32,1108636316#u32⟩⟩) :=
  JFr_EncodedCell.parser cell03 limbs03 encoded03
#print axioms encoded03
#print axioms parser03
def cell04 : Array U8 16#usize := ⟨[186#u8,194#u8,151#u8,127#u8,235#u8,185#u8,15#u8,53#u8,22#u8,235#u8,106#u8,75#u8,6#u8,241#u8,140#u8,43#u8],by rfl⟩
def limbs04 : QM31Limbs := ![⟨2140652218,by change 2140652218<2147483647;omega⟩,⟨890223083,by change 890223083<2147483647;omega⟩,⟨1265298198,by change 1265298198<2147483647;omega⟩,⟨730657030,by change 730657030<2147483647;omega⟩]
theorem rawCell04 : (raw.drop 64).take 16=cell04.val := by
  simp only [raw,JFz_Scan49.data,JFz_Scan49.j00,JFz_Scan49.j01,JFz_Scan49.j02,JFz_Scan49.j03,JFz_Scan49.j04,JFz_Scan49.j05,JFz_Scan49.j06,JFz_Scan49.j07,JFz_Scan49.j08,JFz_Scan49.j09,JFz_Scan49.j10,JFz_Scan49.j11,JFz_Scan49.j12,JFz_Scan49.b00_length,JFz_Scan49.b01_length,JFz_Scan49.b02_length,JFz_Scan49.b03_length,JFz_Scan49.b04_length,JFz_Scan49.b05_length,JFz_Scan49.b06_length,JFz_Scan49.b07_length,JFz_Scan49.b08_length,JFz_Scan49.b09_length,JFz_Scan49.b10_length,JFz_Scan49.b11_length,JFz_Scan49.b12_length,JFz_Scan49.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell04
theorem encoded04 : CandidateParserByteOrder.arrayBytes16 cell04=encodeQM31LE limbs04 := by
  funext i
  fin_cases i <;> rfl
theorem parser04 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell04)=
    ok (some ⟨⟨2140652218#u32,890223083#u32⟩,⟨1265298198#u32,730657030#u32⟩⟩) :=
  JFr_EncodedCell.parser cell04 limbs04 encoded04
#print axioms encoded04
#print axioms parser04
def cell05 : Array U8 16#usize := ⟨[110#u8,175#u8,56#u8,14#u8,202#u8,158#u8,2#u8,76#u8,94#u8,228#u8,217#u8,39#u8,161#u8,178#u8,241#u8,54#u8],by rfl⟩
def limbs05 : QM31Limbs := ![⟨238595950,by change 238595950<2147483647;omega⟩,⟨1275240138,by change 1275240138<2147483647;omega⟩,⟨668591198,by change 668591198<2147483647;omega⟩,⟨921809569,by change 921809569<2147483647;omega⟩]
theorem rawCell05 : (raw.drop 80).take 16=cell05.val := by
  simp only [raw,JFz_Scan49.data,JFz_Scan49.j00,JFz_Scan49.j01,JFz_Scan49.j02,JFz_Scan49.j03,JFz_Scan49.j04,JFz_Scan49.j05,JFz_Scan49.j06,JFz_Scan49.j07,JFz_Scan49.j08,JFz_Scan49.j09,JFz_Scan49.j10,JFz_Scan49.j11,JFz_Scan49.j12,JFz_Scan49.b00_length,JFz_Scan49.b01_length,JFz_Scan49.b02_length,JFz_Scan49.b03_length,JFz_Scan49.b04_length,JFz_Scan49.b05_length,JFz_Scan49.b06_length,JFz_Scan49.b07_length,JFz_Scan49.b08_length,JFz_Scan49.b09_length,JFz_Scan49.b10_length,JFz_Scan49.b11_length,JFz_Scan49.b12_length,JFz_Scan49.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell05
theorem encoded05 : CandidateParserByteOrder.arrayBytes16 cell05=encodeQM31LE limbs05 := by
  funext i
  fin_cases i <;> rfl
theorem parser05 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell05)=
    ok (some ⟨⟨238595950#u32,1275240138#u32⟩,⟨668591198#u32,921809569#u32⟩⟩) :=
  JFr_EncodedCell.parser cell05 limbs05 encoded05
#print axioms encoded05
#print axioms parser05
def cell06 : Array U8 16#usize := ⟨[15#u8,250#u8,127#u8,105#u8,128#u8,233#u8,17#u8,70#u8,216#u8,60#u8,75#u8,25#u8,220#u8,176#u8,157#u8,85#u8],by rfl⟩
def limbs06 : QM31Limbs := ![⟨1769994767,by change 1769994767<2147483647;omega⟩,⟨1175579008,by change 1175579008<2147483647;omega⟩,⟨424361176,by change 424361176<2147483647;omega⟩,⟨1436397788,by change 1436397788<2147483647;omega⟩]
theorem rawCell06 : (raw.drop 96).take 16=cell06.val := by
  simp only [raw,JFz_Scan49.data,JFz_Scan49.j00,JFz_Scan49.j01,JFz_Scan49.j02,JFz_Scan49.j03,JFz_Scan49.j04,JFz_Scan49.j05,JFz_Scan49.j06,JFz_Scan49.j07,JFz_Scan49.j08,JFz_Scan49.j09,JFz_Scan49.j10,JFz_Scan49.j11,JFz_Scan49.j12,JFz_Scan49.b00_length,JFz_Scan49.b01_length,JFz_Scan49.b02_length,JFz_Scan49.b03_length,JFz_Scan49.b04_length,JFz_Scan49.b05_length,JFz_Scan49.b06_length,JFz_Scan49.b07_length,JFz_Scan49.b08_length,JFz_Scan49.b09_length,JFz_Scan49.b10_length,JFz_Scan49.b11_length,JFz_Scan49.b12_length,JFz_Scan49.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell06
theorem encoded06 : CandidateParserByteOrder.arrayBytes16 cell06=encodeQM31LE limbs06 := by
  funext i
  fin_cases i <;> rfl
theorem parser06 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell06)=
    ok (some ⟨⟨1769994767#u32,1175579008#u32⟩,⟨424361176#u32,1436397788#u32⟩⟩) :=
  JFr_EncodedCell.parser cell06 limbs06 encoded06
#print axioms encoded06
#print axioms parser06
def cell07 : Array U8 16#usize := ⟨[104#u8,47#u8,104#u8,94#u8,29#u8,30#u8,159#u8,110#u8,170#u8,101#u8,103#u8,125#u8,36#u8,97#u8,181#u8,32#u8],by rfl⟩
def limbs07 : QM31Limbs := ![⟨1583886184,by change 1583886184<2147483647;omega⟩,⟨1855921693,by change 1855921693<2147483647;omega⟩,⟨2103928234,by change 2103928234<2147483647;omega⟩,⟨548757796,by change 548757796<2147483647;omega⟩]
theorem rawCell07 : (raw.drop 112).take 16=cell07.val := by
  simp only [raw,JFz_Scan49.data,JFz_Scan49.j00,JFz_Scan49.j01,JFz_Scan49.j02,JFz_Scan49.j03,JFz_Scan49.j04,JFz_Scan49.j05,JFz_Scan49.j06,JFz_Scan49.j07,JFz_Scan49.j08,JFz_Scan49.j09,JFz_Scan49.j10,JFz_Scan49.j11,JFz_Scan49.j12,JFz_Scan49.b00_length,JFz_Scan49.b01_length,JFz_Scan49.b02_length,JFz_Scan49.b03_length,JFz_Scan49.b04_length,JFz_Scan49.b05_length,JFz_Scan49.b06_length,JFz_Scan49.b07_length,JFz_Scan49.b08_length,JFz_Scan49.b09_length,JFz_Scan49.b10_length,JFz_Scan49.b11_length,JFz_Scan49.b12_length,JFz_Scan49.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell07
theorem encoded07 : CandidateParserByteOrder.arrayBytes16 cell07=encodeQM31LE limbs07 := by
  funext i
  fin_cases i <;> rfl
theorem parser07 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell07)=
    ok (some ⟨⟨1583886184#u32,1855921693#u32⟩,⟨2103928234#u32,548757796#u32⟩⟩) :=
  JFr_EncodedCell.parser cell07 limbs07 encoded07
#print axioms encoded07
#print axioms parser07
def cell08 : Array U8 16#usize := ⟨[65#u8,115#u8,39#u8,123#u8,255#u8,216#u8,180#u8,71#u8,137#u8,208#u8,86#u8,81#u8,118#u8,45#u8,96#u8,46#u8],by rfl⟩
def limbs08 : QM31Limbs := ![⟨2066182977,by change 2066182977<2147483647;omega⟩,⟨1203034367,by change 1203034367<2147483647;omega⟩,⟨1364643977,by change 1364643977<2147483647;omega⟩,⟨778055030,by change 778055030<2147483647;omega⟩]
theorem rawCell08 : (raw.drop 128).take 16=cell08.val := by
  simp only [raw,JFz_Scan49.data,JFz_Scan49.j00,JFz_Scan49.j01,JFz_Scan49.j02,JFz_Scan49.j03,JFz_Scan49.j04,JFz_Scan49.j05,JFz_Scan49.j06,JFz_Scan49.j07,JFz_Scan49.j08,JFz_Scan49.j09,JFz_Scan49.j10,JFz_Scan49.j11,JFz_Scan49.j12,JFz_Scan49.b00_length,JFz_Scan49.b01_length,JFz_Scan49.b02_length,JFz_Scan49.b03_length,JFz_Scan49.b04_length,JFz_Scan49.b05_length,JFz_Scan49.b06_length,JFz_Scan49.b07_length,JFz_Scan49.b08_length,JFz_Scan49.b09_length,JFz_Scan49.b10_length,JFz_Scan49.b11_length,JFz_Scan49.b12_length,JFz_Scan49.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell08
theorem encoded08 : CandidateParserByteOrder.arrayBytes16 cell08=encodeQM31LE limbs08 := by
  funext i
  fin_cases i <;> rfl
theorem parser08 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell08)=
    ok (some ⟨⟨2066182977#u32,1203034367#u32⟩,⟨1364643977#u32,778055030#u32⟩⟩) :=
  JFr_EncodedCell.parser cell08 limbs08 encoded08
#print axioms encoded08
#print axioms parser08
def cell09 : Array U8 16#usize := ⟨[67#u8,232#u8,151#u8,71#u8,119#u8,243#u8,122#u8,0#u8,27#u8,17#u8,152#u8,4#u8,215#u8,139#u8,41#u8,87#u8],by rfl⟩
def limbs09 : QM31Limbs := ![⟨1201137731,by change 1201137731<2147483647;omega⟩,⟨8057719,by change 8057719<2147483647;omega⟩,⟨77074715,by change 77074715<2147483647;omega⟩,⟨1462340567,by change 1462340567<2147483647;omega⟩]
theorem rawCell09 : (raw.drop 144).take 16=cell09.val := by
  simp only [raw,JFz_Scan49.data,JFz_Scan49.j00,JFz_Scan49.j01,JFz_Scan49.j02,JFz_Scan49.j03,JFz_Scan49.j04,JFz_Scan49.j05,JFz_Scan49.j06,JFz_Scan49.j07,JFz_Scan49.j08,JFz_Scan49.j09,JFz_Scan49.j10,JFz_Scan49.j11,JFz_Scan49.j12,JFz_Scan49.b00_length,JFz_Scan49.b01_length,JFz_Scan49.b02_length,JFz_Scan49.b03_length,JFz_Scan49.b04_length,JFz_Scan49.b05_length,JFz_Scan49.b06_length,JFz_Scan49.b07_length,JFz_Scan49.b08_length,JFz_Scan49.b09_length,JFz_Scan49.b10_length,JFz_Scan49.b11_length,JFz_Scan49.b12_length,JFz_Scan49.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell09
theorem encoded09 : CandidateParserByteOrder.arrayBytes16 cell09=encodeQM31LE limbs09 := by
  funext i
  fin_cases i <;> rfl
theorem parser09 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell09)=
    ok (some ⟨⟨1201137731#u32,8057719#u32⟩,⟨77074715#u32,1462340567#u32⟩⟩) :=
  JFr_EncodedCell.parser cell09 limbs09 encoded09
#print axioms encoded09
#print axioms parser09
def cell10 : Array U8 16#usize := ⟨[94#u8,48#u8,188#u8,31#u8,114#u8,30#u8,136#u8,31#u8,30#u8,94#u8,48#u8,124#u8,213#u8,116#u8,3#u8,109#u8],by rfl⟩
def limbs10 : QM31Limbs := ![⟨532426846,by change 532426846<2147483647;omega⟩,⟨529014386,by change 529014386<2147483647;omega⟩,⟨2083544606,by change 2083544606<2147483647;omega⟩,⟨1828943061,by change 1828943061<2147483647;omega⟩]
theorem rawCell10 : (raw.drop 160).take 16=cell10.val := by
  simp only [raw,JFz_Scan49.data,JFz_Scan49.j00,JFz_Scan49.j01,JFz_Scan49.j02,JFz_Scan49.j03,JFz_Scan49.j04,JFz_Scan49.j05,JFz_Scan49.j06,JFz_Scan49.j07,JFz_Scan49.j08,JFz_Scan49.j09,JFz_Scan49.j10,JFz_Scan49.j11,JFz_Scan49.j12,JFz_Scan49.b00_length,JFz_Scan49.b01_length,JFz_Scan49.b02_length,JFz_Scan49.b03_length,JFz_Scan49.b04_length,JFz_Scan49.b05_length,JFz_Scan49.b06_length,JFz_Scan49.b07_length,JFz_Scan49.b08_length,JFz_Scan49.b09_length,JFz_Scan49.b10_length,JFz_Scan49.b11_length,JFz_Scan49.b12_length,JFz_Scan49.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell10
theorem encoded10 : CandidateParserByteOrder.arrayBytes16 cell10=encodeQM31LE limbs10 := by
  funext i
  fin_cases i <;> rfl
theorem parser10 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell10)=
    ok (some ⟨⟨532426846#u32,529014386#u32⟩,⟨2083544606#u32,1828943061#u32⟩⟩) :=
  JFr_EncodedCell.parser cell10 limbs10 encoded10
#print axioms encoded10
#print axioms parser10
def cell11 : Array U8 16#usize := ⟨[137#u8,35#u8,24#u8,62#u8,26#u8,108#u8,3#u8,34#u8,121#u8,247#u8,217#u8,1#u8,100#u8,214#u8,111#u8,115#u8],by rfl⟩
def limbs11 : QM31Limbs := ![⟨1041769353,by change 1041769353<2147483647;omega⟩,⟨570649626,by change 570649626<2147483647;omega⟩,⟨31061881,by change 31061881<2147483647;omega⟩,⟨1936709220,by change 1936709220<2147483647;omega⟩]
theorem rawCell11 : (raw.drop 176).take 16=cell11.val := by
  simp only [raw,JFz_Scan49.data,JFz_Scan49.j00,JFz_Scan49.j01,JFz_Scan49.j02,JFz_Scan49.j03,JFz_Scan49.j04,JFz_Scan49.j05,JFz_Scan49.j06,JFz_Scan49.j07,JFz_Scan49.j08,JFz_Scan49.j09,JFz_Scan49.j10,JFz_Scan49.j11,JFz_Scan49.j12,JFz_Scan49.b00_length,JFz_Scan49.b01_length,JFz_Scan49.b02_length,JFz_Scan49.b03_length,JFz_Scan49.b04_length,JFz_Scan49.b05_length,JFz_Scan49.b06_length,JFz_Scan49.b07_length,JFz_Scan49.b08_length,JFz_Scan49.b09_length,JFz_Scan49.b10_length,JFz_Scan49.b11_length,JFz_Scan49.b12_length,JFz_Scan49.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell11
theorem encoded11 : CandidateParserByteOrder.arrayBytes16 cell11=encodeQM31LE limbs11 := by
  funext i
  fin_cases i <;> rfl
theorem parser11 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell11)=
    ok (some ⟨⟨1041769353#u32,570649626#u32⟩,⟨31061881#u32,1936709220#u32⟩⟩) :=
  JFr_EncodedCell.parser cell11 limbs11 encoded11
#print axioms encoded11
#print axioms parser11
def cell12 : Array U8 16#usize := ⟨[244#u8,101#u8,227#u8,118#u8,203#u8,42#u8,98#u8,6#u8,163#u8,13#u8,24#u8,79#u8,128#u8,97#u8,73#u8,39#u8],by rfl⟩
def limbs12 : QM31Limbs := ![⟨1994614260,by change 1994614260<2147483647;omega⟩,⟨107096779,by change 107096779<2147483647;omega⟩,⟨1326976419,by change 1326976419<2147483647;omega⟩,⟨659120512,by change 659120512<2147483647;omega⟩]
theorem rawCell12 : (raw.drop 192).take 16=cell12.val := by
  simp only [raw,JFz_Scan49.data,JFz_Scan49.j00,JFz_Scan49.j01,JFz_Scan49.j02,JFz_Scan49.j03,JFz_Scan49.j04,JFz_Scan49.j05,JFz_Scan49.j06,JFz_Scan49.j07,JFz_Scan49.j08,JFz_Scan49.j09,JFz_Scan49.j10,JFz_Scan49.j11,JFz_Scan49.j12,JFz_Scan49.b00_length,JFz_Scan49.b01_length,JFz_Scan49.b02_length,JFz_Scan49.b03_length,JFz_Scan49.b04_length,JFz_Scan49.b05_length,JFz_Scan49.b06_length,JFz_Scan49.b07_length,JFz_Scan49.b08_length,JFz_Scan49.b09_length,JFz_Scan49.b10_length,JFz_Scan49.b11_length,JFz_Scan49.b12_length,JFz_Scan49.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell12
theorem encoded12 : CandidateParserByteOrder.arrayBytes16 cell12=encodeQM31LE limbs12 := by
  funext i
  fin_cases i <;> rfl
theorem parser12 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell12)=
    ok (some ⟨⟨1994614260#u32,107096779#u32⟩,⟨1326976419#u32,659120512#u32⟩⟩) :=
  JFr_EncodedCell.parser cell12 limbs12 encoded12
#print axioms encoded12
#print axioms parser12
def cell13 : Array U8 16#usize := ⟨[198#u8,95#u8,159#u8,27#u8,11#u8,112#u8,253#u8,115#u8,42#u8,46#u8,156#u8,23#u8,194#u8,96#u8,209#u8,4#u8],by rfl⟩
def limbs13 : QM31Limbs := ![⟨463429574,by change 463429574<2147483647;omega⟩,⟨1945989131,by change 1945989131<2147483647;omega⟩,⟨396111402,by change 396111402<2147483647;omega⟩,⟨80830658,by change 80830658<2147483647;omega⟩]
theorem rawCell13 : (raw.drop 208).take 16=cell13.val := by
  simp only [raw,JFz_Scan49.data,JFz_Scan49.j00,JFz_Scan49.j01,JFz_Scan49.j02,JFz_Scan49.j03,JFz_Scan49.j04,JFz_Scan49.j05,JFz_Scan49.j06,JFz_Scan49.j07,JFz_Scan49.j08,JFz_Scan49.j09,JFz_Scan49.j10,JFz_Scan49.j11,JFz_Scan49.j12,JFz_Scan49.b00_length,JFz_Scan49.b01_length,JFz_Scan49.b02_length,JFz_Scan49.b03_length,JFz_Scan49.b04_length,JFz_Scan49.b05_length,JFz_Scan49.b06_length,JFz_Scan49.b07_length,JFz_Scan49.b08_length,JFz_Scan49.b09_length,JFz_Scan49.b10_length,JFz_Scan49.b11_length,JFz_Scan49.b12_length,JFz_Scan49.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell13
theorem encoded13 : CandidateParserByteOrder.arrayBytes16 cell13=encodeQM31LE limbs13 := by
  funext i
  fin_cases i <;> rfl
theorem parser13 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell13)=
    ok (some ⟨⟨463429574#u32,1945989131#u32⟩,⟨396111402#u32,80830658#u32⟩⟩) :=
  JFr_EncodedCell.parser cell13 limbs13 encoded13
#print axioms encoded13
#print axioms parser13
def cell14 : Array U8 16#usize := ⟨[242#u8,93#u8,12#u8,89#u8,211#u8,86#u8,139#u8,96#u8,164#u8,4#u8,73#u8,102#u8,13#u8,66#u8,18#u8,116#u8],by rfl⟩
def limbs14 : QM31Limbs := ![⟨1493982706,by change 1493982706<2147483647;omega⟩,⟨1619744467,by change 1619744467<2147483647;omega⟩,⟨1716061348,by change 1716061348<2147483647;omega⟩,⟨1947353613,by change 1947353613<2147483647;omega⟩]
theorem rawCell14 : (raw.drop 224).take 16=cell14.val := by
  simp only [raw,JFz_Scan49.data,JFz_Scan49.j00,JFz_Scan49.j01,JFz_Scan49.j02,JFz_Scan49.j03,JFz_Scan49.j04,JFz_Scan49.j05,JFz_Scan49.j06,JFz_Scan49.j07,JFz_Scan49.j08,JFz_Scan49.j09,JFz_Scan49.j10,JFz_Scan49.j11,JFz_Scan49.j12,JFz_Scan49.b00_length,JFz_Scan49.b01_length,JFz_Scan49.b02_length,JFz_Scan49.b03_length,JFz_Scan49.b04_length,JFz_Scan49.b05_length,JFz_Scan49.b06_length,JFz_Scan49.b07_length,JFz_Scan49.b08_length,JFz_Scan49.b09_length,JFz_Scan49.b10_length,JFz_Scan49.b11_length,JFz_Scan49.b12_length,JFz_Scan49.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell14
theorem encoded14 : CandidateParserByteOrder.arrayBytes16 cell14=encodeQM31LE limbs14 := by
  funext i
  fin_cases i <;> rfl
theorem parser14 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell14)=
    ok (some ⟨⟨1493982706#u32,1619744467#u32⟩,⟨1716061348#u32,1947353613#u32⟩⟩) :=
  JFr_EncodedCell.parser cell14 limbs14 encoded14
#print axioms encoded14
#print axioms parser14
def cell15 : Array U8 16#usize := ⟨[223#u8,15#u8,192#u8,94#u8,134#u8,221#u8,153#u8,85#u8,110#u8,114#u8,106#u8,84#u8,67#u8,70#u8,82#u8,32#u8],by rfl⟩
def limbs15 : QM31Limbs := ![⟨1589645279,by change 1589645279<2147483647;omega⟩,⟨1436147078,by change 1436147078<2147483647;omega⟩,⟨1416262254,by change 1416262254<2147483647;omega⟩,⟨542262851,by change 542262851<2147483647;omega⟩]
theorem rawCell15 : (raw.drop 240).take 16=cell15.val := by
  simp only [raw,JFz_Scan49.data,JFz_Scan49.j00,JFz_Scan49.j01,JFz_Scan49.j02,JFz_Scan49.j03,JFz_Scan49.j04,JFz_Scan49.j05,JFz_Scan49.j06,JFz_Scan49.j07,JFz_Scan49.j08,JFz_Scan49.j09,JFz_Scan49.j10,JFz_Scan49.j11,JFz_Scan49.j12,JFz_Scan49.b00_length,JFz_Scan49.b01_length,JFz_Scan49.b02_length,JFz_Scan49.b03_length,JFz_Scan49.b04_length,JFz_Scan49.b05_length,JFz_Scan49.b06_length,JFz_Scan49.b07_length,JFz_Scan49.b08_length,JFz_Scan49.b09_length,JFz_Scan49.b10_length,JFz_Scan49.b11_length,JFz_Scan49.b12_length,JFz_Scan49.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell15
theorem encoded15 : CandidateParserByteOrder.arrayBytes16 cell15=encodeQM31LE limbs15 := by
  funext i
  fin_cases i <;> rfl
theorem parser15 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell15)=
    ok (some ⟨⟨1589645279#u32,1436147078#u32⟩,⟨1416262254#u32,542262851#u32⟩⟩) :=
  JFr_EncodedCell.parser cell15 limbs15 encoded15
#print axioms encoded15
#print axioms parser15
def cell16 : Array U8 16#usize := ⟨[211#u8,7#u8,209#u8,96#u8,123#u8,146#u8,130#u8,122#u8,81#u8,155#u8,139#u8,50#u8,106#u8,149#u8,224#u8,81#u8],by rfl⟩
def limbs16 : QM31Limbs := ![⟨1624311763,by change 1624311763<2147483647;omega⟩,⟨2055377531,by change 2055377531<2147483647;omega⟩,⟨848010065,by change 848010065<2147483647;omega⟩,⟨1373672810,by change 1373672810<2147483647;omega⟩]
theorem rawCell16 : (raw.drop 256).take 16=cell16.val := by
  simp only [raw,JFz_Scan49.data,JFz_Scan49.j00,JFz_Scan49.j01,JFz_Scan49.j02,JFz_Scan49.j03,JFz_Scan49.j04,JFz_Scan49.j05,JFz_Scan49.j06,JFz_Scan49.j07,JFz_Scan49.j08,JFz_Scan49.j09,JFz_Scan49.j10,JFz_Scan49.j11,JFz_Scan49.j12,JFz_Scan49.b00_length,JFz_Scan49.b01_length,JFz_Scan49.b02_length,JFz_Scan49.b03_length,JFz_Scan49.b04_length,JFz_Scan49.b05_length,JFz_Scan49.b06_length,JFz_Scan49.b07_length,JFz_Scan49.b08_length,JFz_Scan49.b09_length,JFz_Scan49.b10_length,JFz_Scan49.b11_length,JFz_Scan49.b12_length,JFz_Scan49.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell16
theorem encoded16 : CandidateParserByteOrder.arrayBytes16 cell16=encodeQM31LE limbs16 := by
  funext i
  fin_cases i <;> rfl
theorem parser16 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell16)=
    ok (some ⟨⟨1624311763#u32,2055377531#u32⟩,⟨848010065#u32,1373672810#u32⟩⟩) :=
  JFr_EncodedCell.parser cell16 limbs16 encoded16
#print axioms encoded16
#print axioms parser16
def cell17 : Array U8 16#usize := ⟨[175#u8,85#u8,34#u8,40#u8,182#u8,22#u8,246#u8,76#u8,28#u8,220#u8,128#u8,123#u8,41#u8,43#u8,166#u8,8#u8],by rfl⟩
def limbs17 : QM31Limbs := ![⟨673338799,by change 673338799<2147483647;omega⟩,⟨1291196086,by change 1291196086<2147483647;omega⟩,⟨2072042524,by change 2072042524<2147483647;omega⟩,⟨145107753,by change 145107753<2147483647;omega⟩]
theorem rawCell17 : (raw.drop 272).take 16=cell17.val := by
  simp only [raw,JFz_Scan49.data,JFz_Scan49.j00,JFz_Scan49.j01,JFz_Scan49.j02,JFz_Scan49.j03,JFz_Scan49.j04,JFz_Scan49.j05,JFz_Scan49.j06,JFz_Scan49.j07,JFz_Scan49.j08,JFz_Scan49.j09,JFz_Scan49.j10,JFz_Scan49.j11,JFz_Scan49.j12,JFz_Scan49.b00_length,JFz_Scan49.b01_length,JFz_Scan49.b02_length,JFz_Scan49.b03_length,JFz_Scan49.b04_length,JFz_Scan49.b05_length,JFz_Scan49.b06_length,JFz_Scan49.b07_length,JFz_Scan49.b08_length,JFz_Scan49.b09_length,JFz_Scan49.b10_length,JFz_Scan49.b11_length,JFz_Scan49.b12_length,JFz_Scan49.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell17
theorem encoded17 : CandidateParserByteOrder.arrayBytes16 cell17=encodeQM31LE limbs17 := by
  funext i
  fin_cases i <;> rfl
theorem parser17 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell17)=
    ok (some ⟨⟨673338799#u32,1291196086#u32⟩,⟨2072042524#u32,145107753#u32⟩⟩) :=
  JFr_EncodedCell.parser cell17 limbs17 encoded17
#print axioms encoded17
#print axioms parser17
def cell18 : Array U8 16#usize := ⟨[63#u8,210#u8,234#u8,0#u8,52#u8,103#u8,123#u8,29#u8,128#u8,214#u8,104#u8,85#u8,77#u8,232#u8,2#u8,123#u8],by rfl⟩
def limbs18 : QM31Limbs := ![⟨15389247,by change 15389247<2147483647;omega⟩,⟨494626612,by change 494626612<2147483647;omega⟩,⟨1432934016,by change 1432934016<2147483647;omega⟩,⟨2063788109,by change 2063788109<2147483647;omega⟩]
theorem rawCell18 : (raw.drop 288).take 16=cell18.val := by
  simp only [raw,JFz_Scan49.data,JFz_Scan49.j00,JFz_Scan49.j01,JFz_Scan49.j02,JFz_Scan49.j03,JFz_Scan49.j04,JFz_Scan49.j05,JFz_Scan49.j06,JFz_Scan49.j07,JFz_Scan49.j08,JFz_Scan49.j09,JFz_Scan49.j10,JFz_Scan49.j11,JFz_Scan49.j12,JFz_Scan49.b00_length,JFz_Scan49.b01_length,JFz_Scan49.b02_length,JFz_Scan49.b03_length,JFz_Scan49.b04_length,JFz_Scan49.b05_length,JFz_Scan49.b06_length,JFz_Scan49.b07_length,JFz_Scan49.b08_length,JFz_Scan49.b09_length,JFz_Scan49.b10_length,JFz_Scan49.b11_length,JFz_Scan49.b12_length,JFz_Scan49.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell18
theorem encoded18 : CandidateParserByteOrder.arrayBytes16 cell18=encodeQM31LE limbs18 := by
  funext i
  fin_cases i <;> rfl
theorem parser18 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell18)=
    ok (some ⟨⟨15389247#u32,494626612#u32⟩,⟨1432934016#u32,2063788109#u32⟩⟩) :=
  JFr_EncodedCell.parser cell18 limbs18 encoded18
#print axioms encoded18
#print axioms parser18
def cell19 : Array U8 16#usize := ⟨[242#u8,170#u8,2#u8,55#u8,68#u8,205#u8,8#u8,76#u8,211#u8,114#u8,179#u8,44#u8,255#u8,169#u8,16#u8,25#u8],by rfl⟩
def limbs19 : QM31Limbs := ![⟨922921714,by change 922921714<2147483647;omega⟩,⟨1275645252,by change 1275645252<2147483647;omega⟩,⟨749957843,by change 749957843<2147483647;omega⟩,⟨420522495,by change 420522495<2147483647;omega⟩]
theorem rawCell19 : (raw.drop 304).take 16=cell19.val := by
  simp only [raw,JFz_Scan49.data,JFz_Scan49.j00,JFz_Scan49.j01,JFz_Scan49.j02,JFz_Scan49.j03,JFz_Scan49.j04,JFz_Scan49.j05,JFz_Scan49.j06,JFz_Scan49.j07,JFz_Scan49.j08,JFz_Scan49.j09,JFz_Scan49.j10,JFz_Scan49.j11,JFz_Scan49.j12,JFz_Scan49.b00_length,JFz_Scan49.b01_length,JFz_Scan49.b02_length,JFz_Scan49.b03_length,JFz_Scan49.b04_length,JFz_Scan49.b05_length,JFz_Scan49.b06_length,JFz_Scan49.b07_length,JFz_Scan49.b08_length,JFz_Scan49.b09_length,JFz_Scan49.b10_length,JFz_Scan49.b11_length,JFz_Scan49.b12_length,JFz_Scan49.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell19
theorem encoded19 : CandidateParserByteOrder.arrayBytes16 cell19=encodeQM31LE limbs19 := by
  funext i
  fin_cases i <;> rfl
theorem parser19 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell19)=
    ok (some ⟨⟨922921714#u32,1275645252#u32⟩,⟨749957843#u32,420522495#u32⟩⟩) :=
  JFr_EncodedCell.parser cell19 limbs19 encoded19
#print axioms encoded19
#print axioms parser19
def cell20 : Array U8 16#usize := ⟨[23#u8,98#u8,8#u8,118#u8,124#u8,133#u8,185#u8,94#u8,146#u8,78#u8,14#u8,14#u8,48#u8,157#u8,202#u8,21#u8],by rfl⟩
def limbs20 : QM31Limbs := ![⟨1980260887,by change 1980260887<2147483647;omega⟩,⟨1589216636,by change 1589216636<2147483647;omega⟩,⟨235818642,by change 235818642<2147483647;omega⟩,⟨365600048,by change 365600048<2147483647;omega⟩]
theorem rawCell20 : (raw.drop 320).take 16=cell20.val := by
  simp only [raw,JFz_Scan49.data,JFz_Scan49.j00,JFz_Scan49.j01,JFz_Scan49.j02,JFz_Scan49.j03,JFz_Scan49.j04,JFz_Scan49.j05,JFz_Scan49.j06,JFz_Scan49.j07,JFz_Scan49.j08,JFz_Scan49.j09,JFz_Scan49.j10,JFz_Scan49.j11,JFz_Scan49.j12,JFz_Scan49.b00_length,JFz_Scan49.b01_length,JFz_Scan49.b02_length,JFz_Scan49.b03_length,JFz_Scan49.b04_length,JFz_Scan49.b05_length,JFz_Scan49.b06_length,JFz_Scan49.b07_length,JFz_Scan49.b08_length,JFz_Scan49.b09_length,JFz_Scan49.b10_length,JFz_Scan49.b11_length,JFz_Scan49.b12_length,JFz_Scan49.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell20
theorem encoded20 : CandidateParserByteOrder.arrayBytes16 cell20=encodeQM31LE limbs20 := by
  funext i
  fin_cases i <;> rfl
theorem parser20 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell20)=
    ok (some ⟨⟨1980260887#u32,1589216636#u32⟩,⟨235818642#u32,365600048#u32⟩⟩) :=
  JFr_EncodedCell.parser cell20 limbs20 encoded20
#print axioms encoded20
#print axioms parser20
def cell21 : Array U8 16#usize := ⟨[24#u8,221#u8,127#u8,104#u8,155#u8,68#u8,39#u8,123#u8,20#u8,32#u8,117#u8,69#u8,104#u8,184#u8,104#u8,93#u8],by rfl⟩
def limbs21 : QM31Limbs := ![⟨1753210136,by change 1753210136<2147483647;omega⟩,⟨2066171035,by change 2066171035<2147483647;omega⟩,⟨1165303828,by change 1165303828<2147483647;omega⟩,⟨1567144040,by change 1567144040<2147483647;omega⟩]
theorem rawCell21 : (raw.drop 336).take 16=cell21.val := by
  simp only [raw,JFz_Scan49.data,JFz_Scan49.j00,JFz_Scan49.j01,JFz_Scan49.j02,JFz_Scan49.j03,JFz_Scan49.j04,JFz_Scan49.j05,JFz_Scan49.j06,JFz_Scan49.j07,JFz_Scan49.j08,JFz_Scan49.j09,JFz_Scan49.j10,JFz_Scan49.j11,JFz_Scan49.j12,JFz_Scan49.b00_length,JFz_Scan49.b01_length,JFz_Scan49.b02_length,JFz_Scan49.b03_length,JFz_Scan49.b04_length,JFz_Scan49.b05_length,JFz_Scan49.b06_length,JFz_Scan49.b07_length,JFz_Scan49.b08_length,JFz_Scan49.b09_length,JFz_Scan49.b10_length,JFz_Scan49.b11_length,JFz_Scan49.b12_length,JFz_Scan49.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell21
theorem encoded21 : CandidateParserByteOrder.arrayBytes16 cell21=encodeQM31LE limbs21 := by
  funext i
  fin_cases i <;> rfl
theorem parser21 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell21)=
    ok (some ⟨⟨1753210136#u32,2066171035#u32⟩,⟨1165303828#u32,1567144040#u32⟩⟩) :=
  JFr_EncodedCell.parser cell21 limbs21 encoded21
#print axioms encoded21
#print axioms parser21
def cell22 : Array U8 16#usize := ⟨[134#u8,82#u8,53#u8,26#u8,118#u8,125#u8,117#u8,26#u8,72#u8,245#u8,198#u8,83#u8,114#u8,81#u8,50#u8,25#u8],by rfl⟩
def limbs22 : QM31Limbs := ![⟨439702150,by change 439702150<2147483647;omega⟩,⟨443907446,by change 443907446<2147483647;omega⟩,⟨1405547848,by change 1405547848<2147483647;omega⟩,⟨422728050,by change 422728050<2147483647;omega⟩]
theorem rawCell22 : (raw.drop 352).take 16=cell22.val := by
  simp only [raw,JFz_Scan49.data,JFz_Scan49.j00,JFz_Scan49.j01,JFz_Scan49.j02,JFz_Scan49.j03,JFz_Scan49.j04,JFz_Scan49.j05,JFz_Scan49.j06,JFz_Scan49.j07,JFz_Scan49.j08,JFz_Scan49.j09,JFz_Scan49.j10,JFz_Scan49.j11,JFz_Scan49.j12,JFz_Scan49.b00_length,JFz_Scan49.b01_length,JFz_Scan49.b02_length,JFz_Scan49.b03_length,JFz_Scan49.b04_length,JFz_Scan49.b05_length,JFz_Scan49.b06_length,JFz_Scan49.b07_length,JFz_Scan49.b08_length,JFz_Scan49.b09_length,JFz_Scan49.b10_length,JFz_Scan49.b11_length,JFz_Scan49.b12_length,JFz_Scan49.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell22
theorem encoded22 : CandidateParserByteOrder.arrayBytes16 cell22=encodeQM31LE limbs22 := by
  funext i
  fin_cases i <;> rfl
theorem parser22 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell22)=
    ok (some ⟨⟨439702150#u32,443907446#u32⟩,⟨1405547848#u32,422728050#u32⟩⟩) :=
  JFr_EncodedCell.parser cell22 limbs22 encoded22
#print axioms encoded22
#print axioms parser22
def cell23 : Array U8 16#usize := ⟨[103#u8,187#u8,230#u8,85#u8,171#u8,183#u8,153#u8,10#u8,38#u8,54#u8,237#u8,67#u8,133#u8,111#u8,142#u8,122#u8],by rfl⟩
def limbs23 : QM31Limbs := ![⟨1441184615,by change 1441184615<2147483647;omega⟩,⟨177846187,by change 177846187<2147483647;omega⟩,⟨1139619366,by change 1139619366<2147483647;omega⟩,⟨2056155013,by change 2056155013<2147483647;omega⟩]
theorem rawCell23 : (raw.drop 368).take 16=cell23.val := by
  simp only [raw,JFz_Scan49.data,JFz_Scan49.j00,JFz_Scan49.j01,JFz_Scan49.j02,JFz_Scan49.j03,JFz_Scan49.j04,JFz_Scan49.j05,JFz_Scan49.j06,JFz_Scan49.j07,JFz_Scan49.j08,JFz_Scan49.j09,JFz_Scan49.j10,JFz_Scan49.j11,JFz_Scan49.j12,JFz_Scan49.b00_length,JFz_Scan49.b01_length,JFz_Scan49.b02_length,JFz_Scan49.b03_length,JFz_Scan49.b04_length,JFz_Scan49.b05_length,JFz_Scan49.b06_length,JFz_Scan49.b07_length,JFz_Scan49.b08_length,JFz_Scan49.b09_length,JFz_Scan49.b10_length,JFz_Scan49.b11_length,JFz_Scan49.b12_length,JFz_Scan49.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell23
theorem encoded23 : CandidateParserByteOrder.arrayBytes16 cell23=encodeQM31LE limbs23 := by
  funext i
  fin_cases i <;> rfl
theorem parser23 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell23)=
    ok (some ⟨⟨1441184615#u32,177846187#u32⟩,⟨1139619366#u32,2056155013#u32⟩⟩) :=
  JFr_EncodedCell.parser cell23 limbs23 encoded23
#print axioms encoded23
#print axioms parser23
def cell24 : Array U8 16#usize := ⟨[144#u8,245#u8,227#u8,107#u8,123#u8,104#u8,246#u8,83#u8,235#u8,250#u8,126#u8,97#u8,93#u8,248#u8,108#u8,51#u8],by rfl⟩
def limbs24 : QM31Limbs := ![⟨1810101648,by change 1810101648<2147483647;omega⟩,⟨1408657531,by change 1408657531<2147483647;omega⟩,⟨1635711723,by change 1635711723<2147483647;omega⟩,⟨862779485,by change 862779485<2147483647;omega⟩]
theorem rawCell24 : (raw.drop 384).take 16=cell24.val := by
  simp only [raw,JFz_Scan49.data,JFz_Scan49.j00,JFz_Scan49.j01,JFz_Scan49.j02,JFz_Scan49.j03,JFz_Scan49.j04,JFz_Scan49.j05,JFz_Scan49.j06,JFz_Scan49.j07,JFz_Scan49.j08,JFz_Scan49.j09,JFz_Scan49.j10,JFz_Scan49.j11,JFz_Scan49.j12,JFz_Scan49.b00_length,JFz_Scan49.b01_length,JFz_Scan49.b02_length,JFz_Scan49.b03_length,JFz_Scan49.b04_length,JFz_Scan49.b05_length,JFz_Scan49.b06_length,JFz_Scan49.b07_length,JFz_Scan49.b08_length,JFz_Scan49.b09_length,JFz_Scan49.b10_length,JFz_Scan49.b11_length,JFz_Scan49.b12_length,JFz_Scan49.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell24
theorem encoded24 : CandidateParserByteOrder.arrayBytes16 cell24=encodeQM31LE limbs24 := by
  funext i
  fin_cases i <;> rfl
theorem parser24 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell24)=
    ok (some ⟨⟨1810101648#u32,1408657531#u32⟩,⟨1635711723#u32,862779485#u32⟩⟩) :=
  JFr_EncodedCell.parser cell24 limbs24 encoded24
#print axioms encoded24
#print axioms parser24
def cell25 : Array U8 16#usize := ⟨[53#u8,15#u8,6#u8,66#u8,90#u8,246#u8,145#u8,75#u8,191#u8,214#u8,67#u8,67#u8,101#u8,90#u8,217#u8,34#u8],by rfl⟩
def limbs25 : QM31Limbs := ![⟨1107693365,by change 1107693365<2147483647;omega⟩,⟨1267856986,by change 1267856986<2147483647;omega⟩,⟨1128519359,by change 1128519359<2147483647;omega⟩,⟨584669797,by change 584669797<2147483647;omega⟩]
theorem rawCell25 : (raw.drop 400).take 16=cell25.val := by
  simp only [raw,JFz_Scan49.data,JFz_Scan49.j00,JFz_Scan49.j01,JFz_Scan49.j02,JFz_Scan49.j03,JFz_Scan49.j04,JFz_Scan49.j05,JFz_Scan49.j06,JFz_Scan49.j07,JFz_Scan49.j08,JFz_Scan49.j09,JFz_Scan49.j10,JFz_Scan49.j11,JFz_Scan49.j12,JFz_Scan49.b00_length,JFz_Scan49.b01_length,JFz_Scan49.b02_length,JFz_Scan49.b03_length,JFz_Scan49.b04_length,JFz_Scan49.b05_length,JFz_Scan49.b06_length,JFz_Scan49.b07_length,JFz_Scan49.b08_length,JFz_Scan49.b09_length,JFz_Scan49.b10_length,JFz_Scan49.b11_length,JFz_Scan49.b12_length,JFz_Scan49.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell25
theorem encoded25 : CandidateParserByteOrder.arrayBytes16 cell25=encodeQM31LE limbs25 := by
  funext i
  fin_cases i <;> rfl
theorem parser25 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell25)=
    ok (some ⟨⟨1107693365#u32,1267856986#u32⟩,⟨1128519359#u32,584669797#u32⟩⟩) :=
  JFr_EncodedCell.parser cell25 limbs25 encoded25
#print axioms encoded25
#print axioms parser25
def cell26 : Array U8 16#usize := ⟨[222#u8,172#u8,76#u8,121#u8,83#u8,153#u8,178#u8,4#u8,79#u8,199#u8,84#u8,19#u8,78#u8,104#u8,191#u8,23#u8],by rfl⟩
def limbs26 : QM31Limbs := ![⟨2035068126,by change 2035068126<2147483647;omega⟩,⟨78813523,by change 78813523<2147483647;omega⟩,⟨324323151,by change 324323151<2147483647;omega⟩,⟨398420046,by change 398420046<2147483647;omega⟩]
theorem rawCell26 : (raw.drop 416).take 16=cell26.val := by
  simp only [raw,JFz_Scan49.data,JFz_Scan49.j00,JFz_Scan49.j01,JFz_Scan49.j02,JFz_Scan49.j03,JFz_Scan49.j04,JFz_Scan49.j05,JFz_Scan49.j06,JFz_Scan49.j07,JFz_Scan49.j08,JFz_Scan49.j09,JFz_Scan49.j10,JFz_Scan49.j11,JFz_Scan49.j12,JFz_Scan49.b00_length,JFz_Scan49.b01_length,JFz_Scan49.b02_length,JFz_Scan49.b03_length,JFz_Scan49.b04_length,JFz_Scan49.b05_length,JFz_Scan49.b06_length,JFz_Scan49.b07_length,JFz_Scan49.b08_length,JFz_Scan49.b09_length,JFz_Scan49.b10_length,JFz_Scan49.b11_length,JFz_Scan49.b12_length,JFz_Scan49.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell26
theorem encoded26 : CandidateParserByteOrder.arrayBytes16 cell26=encodeQM31LE limbs26 := by
  funext i
  fin_cases i <;> rfl
theorem parser26 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell26)=
    ok (some ⟨⟨2035068126#u32,78813523#u32⟩,⟨324323151#u32,398420046#u32⟩⟩) :=
  JFr_EncodedCell.parser cell26 limbs26 encoded26
#print axioms encoded26
#print axioms parser26
def cell27 : Array U8 16#usize := ⟨[88#u8,161#u8,134#u8,33#u8,66#u8,7#u8,116#u8,84#u8,78#u8,123#u8,85#u8,106#u8,91#u8,200#u8,33#u8,19#u8],by rfl⟩
def limbs27 : QM31Limbs := ![⟨562471256,by change 562471256<2147483647;omega⟩,⟨1416890178,by change 1416890178<2147483647;omega⟩,⟨1783987022,by change 1783987022<2147483647;omega⟩,⟨320981083,by change 320981083<2147483647;omega⟩]
theorem rawCell27 : (raw.drop 432).take 16=cell27.val := by
  simp only [raw,JFz_Scan49.data,JFz_Scan49.j00,JFz_Scan49.j01,JFz_Scan49.j02,JFz_Scan49.j03,JFz_Scan49.j04,JFz_Scan49.j05,JFz_Scan49.j06,JFz_Scan49.j07,JFz_Scan49.j08,JFz_Scan49.j09,JFz_Scan49.j10,JFz_Scan49.j11,JFz_Scan49.j12,JFz_Scan49.b00_length,JFz_Scan49.b01_length,JFz_Scan49.b02_length,JFz_Scan49.b03_length,JFz_Scan49.b04_length,JFz_Scan49.b05_length,JFz_Scan49.b06_length,JFz_Scan49.b07_length,JFz_Scan49.b08_length,JFz_Scan49.b09_length,JFz_Scan49.b10_length,JFz_Scan49.b11_length,JFz_Scan49.b12_length,JFz_Scan49.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell27
theorem encoded27 : CandidateParserByteOrder.arrayBytes16 cell27=encodeQM31LE limbs27 := by
  funext i
  fin_cases i <;> rfl
theorem parser27 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell27)=
    ok (some ⟨⟨562471256#u32,1416890178#u32⟩,⟨1783987022#u32,320981083#u32⟩⟩) :=
  JFr_EncodedCell.parser cell27 limbs27 encoded27
#print axioms encoded27
#print axioms parser27
end AspisR1.JFr_Bytes01
