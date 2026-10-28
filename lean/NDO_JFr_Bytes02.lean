import NDO_JFr_Data02
import NDO_JFr_EncodedCell
import NDO_JFz_Scan50
set_option autoImplicit false
namespace AspisR1.JFr_Bytes02
open Aeneas Aeneas.Std Result RetainedFieldByteCodec
open AspisR1PublicPreparation
open AspisS1ExtractedRoundChildren
def raw : List U8 := JFz_Scan50.data
theorem rawLength : raw.length=448 := JFz_Scan50.length
#print axioms rawLength
theorem selected : (JFx_NativeBytes.proof.val.drop 1082).take 448=raw := JFz_Scan50.selected
#print axioms selected
def cell00 : Array U8 16#usize := ⟨[59#u8,10#u8,83#u8,115#u8,141#u8,240#u8,243#u8,17#u8,156#u8,157#u8,144#u8,76#u8,76#u8,55#u8,195#u8,61#u8],by rfl⟩
def limbs00 : QM31Limbs := ![⟨1934821947,by change 1934821947<2147483647;omega⟩,⟨301199501,by change 301199501<2147483647;omega⟩,⟨1284545948,by change 1284545948<2147483647;omega⟩,⟨1036203852,by change 1036203852<2147483647;omega⟩]
theorem rawCell00 : (raw.drop 0).take 16=cell00.val := by
  simp only [raw,JFz_Scan50.data,JFz_Scan50.j00,JFz_Scan50.j01,JFz_Scan50.j02,JFz_Scan50.j03,JFz_Scan50.j04,JFz_Scan50.j05,JFz_Scan50.j06,JFz_Scan50.j07,JFz_Scan50.j08,JFz_Scan50.j09,JFz_Scan50.j10,JFz_Scan50.j11,JFz_Scan50.j12,JFz_Scan50.b00_length,JFz_Scan50.b01_length,JFz_Scan50.b02_length,JFz_Scan50.b03_length,JFz_Scan50.b04_length,JFz_Scan50.b05_length,JFz_Scan50.b06_length,JFz_Scan50.b07_length,JFz_Scan50.b08_length,JFz_Scan50.b09_length,JFz_Scan50.b10_length,JFz_Scan50.b11_length,JFz_Scan50.b12_length,JFz_Scan50.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell00
theorem encoded00 : CandidateParserByteOrder.arrayBytes16 cell00=encodeQM31LE limbs00 := by
  funext i
  fin_cases i <;> rfl
theorem parser00 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell00)=
    ok (some ⟨⟨1934821947#u32,301199501#u32⟩,⟨1284545948#u32,1036203852#u32⟩⟩) :=
  JFr_EncodedCell.parser cell00 limbs00 encoded00
#print axioms encoded00
#print axioms parser00
def cell01 : Array U8 16#usize := ⟨[89#u8,129#u8,6#u8,77#u8,204#u8,223#u8,196#u8,50#u8,96#u8,72#u8,65#u8,25#u8,164#u8,101#u8,197#u8,16#u8],by rfl⟩
def limbs01 : QM31Limbs := ![⟨1292271961,by change 1292271961<2147483647;omega⟩,⟨851763148,by change 851763148<2147483647;omega⟩,⟨423708768,by change 423708768<2147483647;omega⟩,⟨281372068,by change 281372068<2147483647;omega⟩]
theorem rawCell01 : (raw.drop 16).take 16=cell01.val := by
  simp only [raw,JFz_Scan50.data,JFz_Scan50.j00,JFz_Scan50.j01,JFz_Scan50.j02,JFz_Scan50.j03,JFz_Scan50.j04,JFz_Scan50.j05,JFz_Scan50.j06,JFz_Scan50.j07,JFz_Scan50.j08,JFz_Scan50.j09,JFz_Scan50.j10,JFz_Scan50.j11,JFz_Scan50.j12,JFz_Scan50.b00_length,JFz_Scan50.b01_length,JFz_Scan50.b02_length,JFz_Scan50.b03_length,JFz_Scan50.b04_length,JFz_Scan50.b05_length,JFz_Scan50.b06_length,JFz_Scan50.b07_length,JFz_Scan50.b08_length,JFz_Scan50.b09_length,JFz_Scan50.b10_length,JFz_Scan50.b11_length,JFz_Scan50.b12_length,JFz_Scan50.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell01
theorem encoded01 : CandidateParserByteOrder.arrayBytes16 cell01=encodeQM31LE limbs01 := by
  funext i
  fin_cases i <;> rfl
theorem parser01 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell01)=
    ok (some ⟨⟨1292271961#u32,851763148#u32⟩,⟨423708768#u32,281372068#u32⟩⟩) :=
  JFr_EncodedCell.parser cell01 limbs01 encoded01
#print axioms encoded01
#print axioms parser01
def cell02 : Array U8 16#usize := ⟨[223#u8,75#u8,134#u8,51#u8,155#u8,105#u8,196#u8,91#u8,85#u8,94#u8,188#u8,33#u8,20#u8,56#u8,218#u8,17#u8],by rfl⟩
def limbs02 : QM31Limbs := ![⟨864439263,by change 864439263<2147483647;omega⟩,⟨1539598747,by change 1539598747<2147483647;omega⟩,⟨565993045,by change 565993045<2147483647;omega⟩,⟨299513876,by change 299513876<2147483647;omega⟩]
theorem rawCell02 : (raw.drop 32).take 16=cell02.val := by
  simp only [raw,JFz_Scan50.data,JFz_Scan50.j00,JFz_Scan50.j01,JFz_Scan50.j02,JFz_Scan50.j03,JFz_Scan50.j04,JFz_Scan50.j05,JFz_Scan50.j06,JFz_Scan50.j07,JFz_Scan50.j08,JFz_Scan50.j09,JFz_Scan50.j10,JFz_Scan50.j11,JFz_Scan50.j12,JFz_Scan50.b00_length,JFz_Scan50.b01_length,JFz_Scan50.b02_length,JFz_Scan50.b03_length,JFz_Scan50.b04_length,JFz_Scan50.b05_length,JFz_Scan50.b06_length,JFz_Scan50.b07_length,JFz_Scan50.b08_length,JFz_Scan50.b09_length,JFz_Scan50.b10_length,JFz_Scan50.b11_length,JFz_Scan50.b12_length,JFz_Scan50.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell02
theorem encoded02 : CandidateParserByteOrder.arrayBytes16 cell02=encodeQM31LE limbs02 := by
  funext i
  fin_cases i <;> rfl
theorem parser02 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell02)=
    ok (some ⟨⟨864439263#u32,1539598747#u32⟩,⟨565993045#u32,299513876#u32⟩⟩) :=
  JFr_EncodedCell.parser cell02 limbs02 encoded02
#print axioms encoded02
#print axioms parser02
def cell03 : Array U8 16#usize := ⟨[155#u8,204#u8,53#u8,96#u8,112#u8,124#u8,159#u8,33#u8,119#u8,99#u8,213#u8,123#u8,7#u8,45#u8,41#u8,40#u8],by rfl⟩
def limbs03 : QM31Limbs := ![⟨1614138523,by change 1614138523<2147483647;omega⟩,⟨564100208,by change 564100208<2147483647;omega⟩,⟨2077582199,by change 2077582199<2147483647;omega⟩,⟨673787143,by change 673787143<2147483647;omega⟩]
theorem rawCell03 : (raw.drop 48).take 16=cell03.val := by
  simp only [raw,JFz_Scan50.data,JFz_Scan50.j00,JFz_Scan50.j01,JFz_Scan50.j02,JFz_Scan50.j03,JFz_Scan50.j04,JFz_Scan50.j05,JFz_Scan50.j06,JFz_Scan50.j07,JFz_Scan50.j08,JFz_Scan50.j09,JFz_Scan50.j10,JFz_Scan50.j11,JFz_Scan50.j12,JFz_Scan50.b00_length,JFz_Scan50.b01_length,JFz_Scan50.b02_length,JFz_Scan50.b03_length,JFz_Scan50.b04_length,JFz_Scan50.b05_length,JFz_Scan50.b06_length,JFz_Scan50.b07_length,JFz_Scan50.b08_length,JFz_Scan50.b09_length,JFz_Scan50.b10_length,JFz_Scan50.b11_length,JFz_Scan50.b12_length,JFz_Scan50.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell03
theorem encoded03 : CandidateParserByteOrder.arrayBytes16 cell03=encodeQM31LE limbs03 := by
  funext i
  fin_cases i <;> rfl
theorem parser03 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell03)=
    ok (some ⟨⟨1614138523#u32,564100208#u32⟩,⟨2077582199#u32,673787143#u32⟩⟩) :=
  JFr_EncodedCell.parser cell03 limbs03 encoded03
#print axioms encoded03
#print axioms parser03
def cell04 : Array U8 16#usize := ⟨[204#u8,11#u8,161#u8,114#u8,153#u8,220#u8,106#u8,79#u8,81#u8,182#u8,57#u8,41#u8,37#u8,121#u8,219#u8,107#u8],by rfl⟩
def limbs04 : QM31Limbs := ![⟨1923156940,by change 1923156940<2147483647;omega⟩,⟨1332403353,by change 1332403353<2147483647;omega⟩,⟨691648081,by change 691648081<2147483647;omega⟩,⟨1809545509,by change 1809545509<2147483647;omega⟩]
theorem rawCell04 : (raw.drop 64).take 16=cell04.val := by
  simp only [raw,JFz_Scan50.data,JFz_Scan50.j00,JFz_Scan50.j01,JFz_Scan50.j02,JFz_Scan50.j03,JFz_Scan50.j04,JFz_Scan50.j05,JFz_Scan50.j06,JFz_Scan50.j07,JFz_Scan50.j08,JFz_Scan50.j09,JFz_Scan50.j10,JFz_Scan50.j11,JFz_Scan50.j12,JFz_Scan50.b00_length,JFz_Scan50.b01_length,JFz_Scan50.b02_length,JFz_Scan50.b03_length,JFz_Scan50.b04_length,JFz_Scan50.b05_length,JFz_Scan50.b06_length,JFz_Scan50.b07_length,JFz_Scan50.b08_length,JFz_Scan50.b09_length,JFz_Scan50.b10_length,JFz_Scan50.b11_length,JFz_Scan50.b12_length,JFz_Scan50.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell04
theorem encoded04 : CandidateParserByteOrder.arrayBytes16 cell04=encodeQM31LE limbs04 := by
  funext i
  fin_cases i <;> rfl
theorem parser04 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell04)=
    ok (some ⟨⟨1923156940#u32,1332403353#u32⟩,⟨691648081#u32,1809545509#u32⟩⟩) :=
  JFr_EncodedCell.parser cell04 limbs04 encoded04
#print axioms encoded04
#print axioms parser04
def cell05 : Array U8 16#usize := ⟨[96#u8,234#u8,53#u8,92#u8,121#u8,146#u8,240#u8,10#u8,55#u8,46#u8,233#u8,123#u8,116#u8,68#u8,218#u8,98#u8],by rfl⟩
def limbs05 : QM31Limbs := ![⟨1547037280,by change 1547037280<2147483647;omega⟩,⟨183538297,by change 183538297<2147483647;omega⟩,⟨2078879287,by change 2078879287<2147483647;omega⟩,⟨1658471540,by change 1658471540<2147483647;omega⟩]
theorem rawCell05 : (raw.drop 80).take 16=cell05.val := by
  simp only [raw,JFz_Scan50.data,JFz_Scan50.j00,JFz_Scan50.j01,JFz_Scan50.j02,JFz_Scan50.j03,JFz_Scan50.j04,JFz_Scan50.j05,JFz_Scan50.j06,JFz_Scan50.j07,JFz_Scan50.j08,JFz_Scan50.j09,JFz_Scan50.j10,JFz_Scan50.j11,JFz_Scan50.j12,JFz_Scan50.b00_length,JFz_Scan50.b01_length,JFz_Scan50.b02_length,JFz_Scan50.b03_length,JFz_Scan50.b04_length,JFz_Scan50.b05_length,JFz_Scan50.b06_length,JFz_Scan50.b07_length,JFz_Scan50.b08_length,JFz_Scan50.b09_length,JFz_Scan50.b10_length,JFz_Scan50.b11_length,JFz_Scan50.b12_length,JFz_Scan50.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell05
theorem encoded05 : CandidateParserByteOrder.arrayBytes16 cell05=encodeQM31LE limbs05 := by
  funext i
  fin_cases i <;> rfl
theorem parser05 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell05)=
    ok (some ⟨⟨1547037280#u32,183538297#u32⟩,⟨2078879287#u32,1658471540#u32⟩⟩) :=
  JFr_EncodedCell.parser cell05 limbs05 encoded05
#print axioms encoded05
#print axioms parser05
def cell06 : Array U8 16#usize := ⟨[238#u8,7#u8,138#u8,2#u8,48#u8,93#u8,223#u8,69#u8,128#u8,55#u8,164#u8,17#u8,124#u8,181#u8,49#u8,52#u8],by rfl⟩
def limbs06 : QM31Limbs := ![⟨42600430,by change 42600430<2147483647;omega⟩,⟨1172266288,by change 1172266288<2147483647;omega⟩,⟨295974784,by change 295974784<2147483647;omega⟩,⟨875672956,by change 875672956<2147483647;omega⟩]
theorem rawCell06 : (raw.drop 96).take 16=cell06.val := by
  simp only [raw,JFz_Scan50.data,JFz_Scan50.j00,JFz_Scan50.j01,JFz_Scan50.j02,JFz_Scan50.j03,JFz_Scan50.j04,JFz_Scan50.j05,JFz_Scan50.j06,JFz_Scan50.j07,JFz_Scan50.j08,JFz_Scan50.j09,JFz_Scan50.j10,JFz_Scan50.j11,JFz_Scan50.j12,JFz_Scan50.b00_length,JFz_Scan50.b01_length,JFz_Scan50.b02_length,JFz_Scan50.b03_length,JFz_Scan50.b04_length,JFz_Scan50.b05_length,JFz_Scan50.b06_length,JFz_Scan50.b07_length,JFz_Scan50.b08_length,JFz_Scan50.b09_length,JFz_Scan50.b10_length,JFz_Scan50.b11_length,JFz_Scan50.b12_length,JFz_Scan50.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell06
theorem encoded06 : CandidateParserByteOrder.arrayBytes16 cell06=encodeQM31LE limbs06 := by
  funext i
  fin_cases i <;> rfl
theorem parser06 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell06)=
    ok (some ⟨⟨42600430#u32,1172266288#u32⟩,⟨295974784#u32,875672956#u32⟩⟩) :=
  JFr_EncodedCell.parser cell06 limbs06 encoded06
#print axioms encoded06
#print axioms parser06
def cell07 : Array U8 16#usize := ⟨[111#u8,95#u8,11#u8,71#u8,176#u8,185#u8,45#u8,16#u8,28#u8,25#u8,22#u8,103#u8,80#u8,254#u8,136#u8,92#u8],by rfl⟩
def limbs07 : QM31Limbs := ![⟨1191927663,by change 1191927663<2147483647;omega⟩,⟨271432112,by change 271432112<2147483647;omega⟩,⟨1729501468,by change 1729501468<2147483647;omega⟩,⟨1552481872,by change 1552481872<2147483647;omega⟩]
theorem rawCell07 : (raw.drop 112).take 16=cell07.val := by
  simp only [raw,JFz_Scan50.data,JFz_Scan50.j00,JFz_Scan50.j01,JFz_Scan50.j02,JFz_Scan50.j03,JFz_Scan50.j04,JFz_Scan50.j05,JFz_Scan50.j06,JFz_Scan50.j07,JFz_Scan50.j08,JFz_Scan50.j09,JFz_Scan50.j10,JFz_Scan50.j11,JFz_Scan50.j12,JFz_Scan50.b00_length,JFz_Scan50.b01_length,JFz_Scan50.b02_length,JFz_Scan50.b03_length,JFz_Scan50.b04_length,JFz_Scan50.b05_length,JFz_Scan50.b06_length,JFz_Scan50.b07_length,JFz_Scan50.b08_length,JFz_Scan50.b09_length,JFz_Scan50.b10_length,JFz_Scan50.b11_length,JFz_Scan50.b12_length,JFz_Scan50.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell07
theorem encoded07 : CandidateParserByteOrder.arrayBytes16 cell07=encodeQM31LE limbs07 := by
  funext i
  fin_cases i <;> rfl
theorem parser07 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell07)=
    ok (some ⟨⟨1191927663#u32,271432112#u32⟩,⟨1729501468#u32,1552481872#u32⟩⟩) :=
  JFr_EncodedCell.parser cell07 limbs07 encoded07
#print axioms encoded07
#print axioms parser07
def cell08 : Array U8 16#usize := ⟨[140#u8,65#u8,160#u8,108#u8,166#u8,151#u8,105#u8,68#u8,43#u8,127#u8,144#u8,45#u8,147#u8,155#u8,159#u8,1#u8],by rfl⟩
def limbs08 : QM31Limbs := ![⟨1822441868,by change 1822441868<2147483647;omega⟩,⟨1147770790,by change 1147770790<2147483647;omega⟩,⟨764444459,by change 764444459<2147483647;omega⟩,⟨27237267,by change 27237267<2147483647;omega⟩]
theorem rawCell08 : (raw.drop 128).take 16=cell08.val := by
  simp only [raw,JFz_Scan50.data,JFz_Scan50.j00,JFz_Scan50.j01,JFz_Scan50.j02,JFz_Scan50.j03,JFz_Scan50.j04,JFz_Scan50.j05,JFz_Scan50.j06,JFz_Scan50.j07,JFz_Scan50.j08,JFz_Scan50.j09,JFz_Scan50.j10,JFz_Scan50.j11,JFz_Scan50.j12,JFz_Scan50.b00_length,JFz_Scan50.b01_length,JFz_Scan50.b02_length,JFz_Scan50.b03_length,JFz_Scan50.b04_length,JFz_Scan50.b05_length,JFz_Scan50.b06_length,JFz_Scan50.b07_length,JFz_Scan50.b08_length,JFz_Scan50.b09_length,JFz_Scan50.b10_length,JFz_Scan50.b11_length,JFz_Scan50.b12_length,JFz_Scan50.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell08
theorem encoded08 : CandidateParserByteOrder.arrayBytes16 cell08=encodeQM31LE limbs08 := by
  funext i
  fin_cases i <;> rfl
theorem parser08 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell08)=
    ok (some ⟨⟨1822441868#u32,1147770790#u32⟩,⟨764444459#u32,27237267#u32⟩⟩) :=
  JFr_EncodedCell.parser cell08 limbs08 encoded08
#print axioms encoded08
#print axioms parser08
def cell09 : Array U8 16#usize := ⟨[47#u8,225#u8,127#u8,103#u8,139#u8,15#u8,48#u8,118#u8,104#u8,254#u8,119#u8,50#u8,240#u8,78#u8,178#u8,32#u8],by rfl⟩
def limbs09 : QM31Limbs := ![⟨1736433967,by change 1736433967<2147483647;omega⟩,⟨1982861195,by change 1982861195<2147483647;omega⟩,⟨846724712,by change 846724712<2147483647;omega⟩,⟨548556528,by change 548556528<2147483647;omega⟩]
theorem rawCell09 : (raw.drop 144).take 16=cell09.val := by
  simp only [raw,JFz_Scan50.data,JFz_Scan50.j00,JFz_Scan50.j01,JFz_Scan50.j02,JFz_Scan50.j03,JFz_Scan50.j04,JFz_Scan50.j05,JFz_Scan50.j06,JFz_Scan50.j07,JFz_Scan50.j08,JFz_Scan50.j09,JFz_Scan50.j10,JFz_Scan50.j11,JFz_Scan50.j12,JFz_Scan50.b00_length,JFz_Scan50.b01_length,JFz_Scan50.b02_length,JFz_Scan50.b03_length,JFz_Scan50.b04_length,JFz_Scan50.b05_length,JFz_Scan50.b06_length,JFz_Scan50.b07_length,JFz_Scan50.b08_length,JFz_Scan50.b09_length,JFz_Scan50.b10_length,JFz_Scan50.b11_length,JFz_Scan50.b12_length,JFz_Scan50.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell09
theorem encoded09 : CandidateParserByteOrder.arrayBytes16 cell09=encodeQM31LE limbs09 := by
  funext i
  fin_cases i <;> rfl
theorem parser09 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell09)=
    ok (some ⟨⟨1736433967#u32,1982861195#u32⟩,⟨846724712#u32,548556528#u32⟩⟩) :=
  JFr_EncodedCell.parser cell09 limbs09 encoded09
#print axioms encoded09
#print axioms parser09
def cell10 : Array U8 16#usize := ⟨[15#u8,169#u8,132#u8,58#u8,164#u8,34#u8,178#u8,119#u8,55#u8,89#u8,100#u8,3#u8,219#u8,194#u8,187#u8,109#u8],by rfl⟩
def limbs10 : QM31Limbs := ![⟨981772559,by change 981772559<2147483647;omega⟩,⟨2008162980,by change 2008162980<2147483647;omega⟩,⟨56908087,by change 56908087<2147483647;omega⟩,⟨1841021659,by change 1841021659<2147483647;omega⟩]
theorem rawCell10 : (raw.drop 160).take 16=cell10.val := by
  simp only [raw,JFz_Scan50.data,JFz_Scan50.j00,JFz_Scan50.j01,JFz_Scan50.j02,JFz_Scan50.j03,JFz_Scan50.j04,JFz_Scan50.j05,JFz_Scan50.j06,JFz_Scan50.j07,JFz_Scan50.j08,JFz_Scan50.j09,JFz_Scan50.j10,JFz_Scan50.j11,JFz_Scan50.j12,JFz_Scan50.b00_length,JFz_Scan50.b01_length,JFz_Scan50.b02_length,JFz_Scan50.b03_length,JFz_Scan50.b04_length,JFz_Scan50.b05_length,JFz_Scan50.b06_length,JFz_Scan50.b07_length,JFz_Scan50.b08_length,JFz_Scan50.b09_length,JFz_Scan50.b10_length,JFz_Scan50.b11_length,JFz_Scan50.b12_length,JFz_Scan50.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell10
theorem encoded10 : CandidateParserByteOrder.arrayBytes16 cell10=encodeQM31LE limbs10 := by
  funext i
  fin_cases i <;> rfl
theorem parser10 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell10)=
    ok (some ⟨⟨981772559#u32,2008162980#u32⟩,⟨56908087#u32,1841021659#u32⟩⟩) :=
  JFr_EncodedCell.parser cell10 limbs10 encoded10
#print axioms encoded10
#print axioms parser10
def cell11 : Array U8 16#usize := ⟨[198#u8,210#u8,123#u8,92#u8,198#u8,39#u8,175#u8,8#u8,210#u8,75#u8,107#u8,36#u8,190#u8,87#u8,229#u8,7#u8],by rfl⟩
def limbs11 : QM31Limbs := ![⟨1551618758,by change 1551618758<2147483647;omega⟩,⟨145696710,by change 145696710<2147483647;omega⟩,⟨611011538,by change 611011538<2147483647;omega⟩,⟨132470718,by change 132470718<2147483647;omega⟩]
theorem rawCell11 : (raw.drop 176).take 16=cell11.val := by
  simp only [raw,JFz_Scan50.data,JFz_Scan50.j00,JFz_Scan50.j01,JFz_Scan50.j02,JFz_Scan50.j03,JFz_Scan50.j04,JFz_Scan50.j05,JFz_Scan50.j06,JFz_Scan50.j07,JFz_Scan50.j08,JFz_Scan50.j09,JFz_Scan50.j10,JFz_Scan50.j11,JFz_Scan50.j12,JFz_Scan50.b00_length,JFz_Scan50.b01_length,JFz_Scan50.b02_length,JFz_Scan50.b03_length,JFz_Scan50.b04_length,JFz_Scan50.b05_length,JFz_Scan50.b06_length,JFz_Scan50.b07_length,JFz_Scan50.b08_length,JFz_Scan50.b09_length,JFz_Scan50.b10_length,JFz_Scan50.b11_length,JFz_Scan50.b12_length,JFz_Scan50.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell11
theorem encoded11 : CandidateParserByteOrder.arrayBytes16 cell11=encodeQM31LE limbs11 := by
  funext i
  fin_cases i <;> rfl
theorem parser11 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell11)=
    ok (some ⟨⟨1551618758#u32,145696710#u32⟩,⟨611011538#u32,132470718#u32⟩⟩) :=
  JFr_EncodedCell.parser cell11 limbs11 encoded11
#print axioms encoded11
#print axioms parser11
def cell12 : Array U8 16#usize := ⟨[161#u8,49#u8,171#u8,40#u8,39#u8,35#u8,13#u8,2#u8,38#u8,204#u8,135#u8,71#u8,73#u8,176#u8,185#u8,38#u8],by rfl⟩
def limbs12 : QM31Limbs := ![⟨682308001,by change 682308001<2147483647;omega⟩,⟨34415399,by change 34415399<2147483647;omega⟩,⟨1200081958,by change 1200081958<2147483647;omega⟩,⟨649703497,by change 649703497<2147483647;omega⟩]
theorem rawCell12 : (raw.drop 192).take 16=cell12.val := by
  simp only [raw,JFz_Scan50.data,JFz_Scan50.j00,JFz_Scan50.j01,JFz_Scan50.j02,JFz_Scan50.j03,JFz_Scan50.j04,JFz_Scan50.j05,JFz_Scan50.j06,JFz_Scan50.j07,JFz_Scan50.j08,JFz_Scan50.j09,JFz_Scan50.j10,JFz_Scan50.j11,JFz_Scan50.j12,JFz_Scan50.b00_length,JFz_Scan50.b01_length,JFz_Scan50.b02_length,JFz_Scan50.b03_length,JFz_Scan50.b04_length,JFz_Scan50.b05_length,JFz_Scan50.b06_length,JFz_Scan50.b07_length,JFz_Scan50.b08_length,JFz_Scan50.b09_length,JFz_Scan50.b10_length,JFz_Scan50.b11_length,JFz_Scan50.b12_length,JFz_Scan50.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell12
theorem encoded12 : CandidateParserByteOrder.arrayBytes16 cell12=encodeQM31LE limbs12 := by
  funext i
  fin_cases i <;> rfl
theorem parser12 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell12)=
    ok (some ⟨⟨682308001#u32,34415399#u32⟩,⟨1200081958#u32,649703497#u32⟩⟩) :=
  JFr_EncodedCell.parser cell12 limbs12 encoded12
#print axioms encoded12
#print axioms parser12
def cell13 : Array U8 16#usize := ⟨[147#u8,147#u8,202#u8,76#u8,232#u8,39#u8,188#u8,107#u8,196#u8,244#u8,193#u8,115#u8,50#u8,235#u8,116#u8,121#u8],by rfl⟩
def limbs13 : QM31Limbs := ![⟨1288344467,by change 1288344467<2147483647;omega⟩,⟨1807493096,by change 1807493096<2147483647;omega⟩,⟨1942090948,by change 1942090948<2147483647;omega⟩,⟨2037705522,by change 2037705522<2147483647;omega⟩]
theorem rawCell13 : (raw.drop 208).take 16=cell13.val := by
  simp only [raw,JFz_Scan50.data,JFz_Scan50.j00,JFz_Scan50.j01,JFz_Scan50.j02,JFz_Scan50.j03,JFz_Scan50.j04,JFz_Scan50.j05,JFz_Scan50.j06,JFz_Scan50.j07,JFz_Scan50.j08,JFz_Scan50.j09,JFz_Scan50.j10,JFz_Scan50.j11,JFz_Scan50.j12,JFz_Scan50.b00_length,JFz_Scan50.b01_length,JFz_Scan50.b02_length,JFz_Scan50.b03_length,JFz_Scan50.b04_length,JFz_Scan50.b05_length,JFz_Scan50.b06_length,JFz_Scan50.b07_length,JFz_Scan50.b08_length,JFz_Scan50.b09_length,JFz_Scan50.b10_length,JFz_Scan50.b11_length,JFz_Scan50.b12_length,JFz_Scan50.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell13
theorem encoded13 : CandidateParserByteOrder.arrayBytes16 cell13=encodeQM31LE limbs13 := by
  funext i
  fin_cases i <;> rfl
theorem parser13 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell13)=
    ok (some ⟨⟨1288344467#u32,1807493096#u32⟩,⟨1942090948#u32,2037705522#u32⟩⟩) :=
  JFr_EncodedCell.parser cell13 limbs13 encoded13
#print axioms encoded13
#print axioms parser13
def cell14 : Array U8 16#usize := ⟨[182#u8,140#u8,246#u8,45#u8,104#u8,254#u8,33#u8,58#u8,39#u8,155#u8,96#u8,32#u8,247#u8,223#u8,126#u8,74#u8],by rfl⟩
def limbs14 : QM31Limbs := ![⟨771132598,by change 771132598<2147483647;omega⟩,⟨975306344,by change 975306344<2147483647;omega⟩,⟨543202087,by change 543202087<2147483647;omega⟩,⟨1249828855,by change 1249828855<2147483647;omega⟩]
theorem rawCell14 : (raw.drop 224).take 16=cell14.val := by
  simp only [raw,JFz_Scan50.data,JFz_Scan50.j00,JFz_Scan50.j01,JFz_Scan50.j02,JFz_Scan50.j03,JFz_Scan50.j04,JFz_Scan50.j05,JFz_Scan50.j06,JFz_Scan50.j07,JFz_Scan50.j08,JFz_Scan50.j09,JFz_Scan50.j10,JFz_Scan50.j11,JFz_Scan50.j12,JFz_Scan50.b00_length,JFz_Scan50.b01_length,JFz_Scan50.b02_length,JFz_Scan50.b03_length,JFz_Scan50.b04_length,JFz_Scan50.b05_length,JFz_Scan50.b06_length,JFz_Scan50.b07_length,JFz_Scan50.b08_length,JFz_Scan50.b09_length,JFz_Scan50.b10_length,JFz_Scan50.b11_length,JFz_Scan50.b12_length,JFz_Scan50.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell14
theorem encoded14 : CandidateParserByteOrder.arrayBytes16 cell14=encodeQM31LE limbs14 := by
  funext i
  fin_cases i <;> rfl
theorem parser14 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell14)=
    ok (some ⟨⟨771132598#u32,975306344#u32⟩,⟨543202087#u32,1249828855#u32⟩⟩) :=
  JFr_EncodedCell.parser cell14 limbs14 encoded14
#print axioms encoded14
#print axioms parser14
def cell15 : Array U8 16#usize := ⟨[217#u8,23#u8,153#u8,77#u8,9#u8,17#u8,3#u8,97#u8,180#u8,62#u8,90#u8,40#u8,28#u8,240#u8,76#u8,123#u8],by rfl⟩
def limbs15 : QM31Limbs := ![⟨1301878745,by change 1301878745<2147483647;omega⟩,⟨1627590921,by change 1627590921<2147483647;omega⟩,⟨677002932,by change 677002932<2147483647;omega⟩,⟨2068639772,by change 2068639772<2147483647;omega⟩]
theorem rawCell15 : (raw.drop 240).take 16=cell15.val := by
  simp only [raw,JFz_Scan50.data,JFz_Scan50.j00,JFz_Scan50.j01,JFz_Scan50.j02,JFz_Scan50.j03,JFz_Scan50.j04,JFz_Scan50.j05,JFz_Scan50.j06,JFz_Scan50.j07,JFz_Scan50.j08,JFz_Scan50.j09,JFz_Scan50.j10,JFz_Scan50.j11,JFz_Scan50.j12,JFz_Scan50.b00_length,JFz_Scan50.b01_length,JFz_Scan50.b02_length,JFz_Scan50.b03_length,JFz_Scan50.b04_length,JFz_Scan50.b05_length,JFz_Scan50.b06_length,JFz_Scan50.b07_length,JFz_Scan50.b08_length,JFz_Scan50.b09_length,JFz_Scan50.b10_length,JFz_Scan50.b11_length,JFz_Scan50.b12_length,JFz_Scan50.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell15
theorem encoded15 : CandidateParserByteOrder.arrayBytes16 cell15=encodeQM31LE limbs15 := by
  funext i
  fin_cases i <;> rfl
theorem parser15 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell15)=
    ok (some ⟨⟨1301878745#u32,1627590921#u32⟩,⟨677002932#u32,2068639772#u32⟩⟩) :=
  JFr_EncodedCell.parser cell15 limbs15 encoded15
#print axioms encoded15
#print axioms parser15
def cell16 : Array U8 16#usize := ⟨[94#u8,85#u8,182#u8,62#u8,43#u8,201#u8,1#u8,21#u8,170#u8,224#u8,156#u8,45#u8,160#u8,62#u8,99#u8,56#u8],by rfl⟩
def limbs16 : QM31Limbs := ![⟨1052136798,by change 1052136798<2147483647;omega⟩,⟨352438571,by change 352438571<2147483647;omega⟩,⟨765255850,by change 765255850<2147483647;omega⟩,⟨946028192,by change 946028192<2147483647;omega⟩]
theorem rawCell16 : (raw.drop 256).take 16=cell16.val := by
  simp only [raw,JFz_Scan50.data,JFz_Scan50.j00,JFz_Scan50.j01,JFz_Scan50.j02,JFz_Scan50.j03,JFz_Scan50.j04,JFz_Scan50.j05,JFz_Scan50.j06,JFz_Scan50.j07,JFz_Scan50.j08,JFz_Scan50.j09,JFz_Scan50.j10,JFz_Scan50.j11,JFz_Scan50.j12,JFz_Scan50.b00_length,JFz_Scan50.b01_length,JFz_Scan50.b02_length,JFz_Scan50.b03_length,JFz_Scan50.b04_length,JFz_Scan50.b05_length,JFz_Scan50.b06_length,JFz_Scan50.b07_length,JFz_Scan50.b08_length,JFz_Scan50.b09_length,JFz_Scan50.b10_length,JFz_Scan50.b11_length,JFz_Scan50.b12_length,JFz_Scan50.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell16
theorem encoded16 : CandidateParserByteOrder.arrayBytes16 cell16=encodeQM31LE limbs16 := by
  funext i
  fin_cases i <;> rfl
theorem parser16 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell16)=
    ok (some ⟨⟨1052136798#u32,352438571#u32⟩,⟨765255850#u32,946028192#u32⟩⟩) :=
  JFr_EncodedCell.parser cell16 limbs16 encoded16
#print axioms encoded16
#print axioms parser16
def cell17 : Array U8 16#usize := ⟨[76#u8,216#u8,71#u8,46#u8,46#u8,171#u8,54#u8,39#u8,5#u8,133#u8,151#u8,67#u8,143#u8,164#u8,80#u8,45#u8],by rfl⟩
def limbs17 : QM31Limbs := ![⟨776460364,by change 776460364<2147483647;omega⟩,⟨657894190,by change 657894190<2147483647;omega⟩,⟨1134003461,by change 1134003461<2147483647;omega⟩,⟨760259727,by change 760259727<2147483647;omega⟩]
theorem rawCell17 : (raw.drop 272).take 16=cell17.val := by
  simp only [raw,JFz_Scan50.data,JFz_Scan50.j00,JFz_Scan50.j01,JFz_Scan50.j02,JFz_Scan50.j03,JFz_Scan50.j04,JFz_Scan50.j05,JFz_Scan50.j06,JFz_Scan50.j07,JFz_Scan50.j08,JFz_Scan50.j09,JFz_Scan50.j10,JFz_Scan50.j11,JFz_Scan50.j12,JFz_Scan50.b00_length,JFz_Scan50.b01_length,JFz_Scan50.b02_length,JFz_Scan50.b03_length,JFz_Scan50.b04_length,JFz_Scan50.b05_length,JFz_Scan50.b06_length,JFz_Scan50.b07_length,JFz_Scan50.b08_length,JFz_Scan50.b09_length,JFz_Scan50.b10_length,JFz_Scan50.b11_length,JFz_Scan50.b12_length,JFz_Scan50.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell17
theorem encoded17 : CandidateParserByteOrder.arrayBytes16 cell17=encodeQM31LE limbs17 := by
  funext i
  fin_cases i <;> rfl
theorem parser17 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell17)=
    ok (some ⟨⟨776460364#u32,657894190#u32⟩,⟨1134003461#u32,760259727#u32⟩⟩) :=
  JFr_EncodedCell.parser cell17 limbs17 encoded17
#print axioms encoded17
#print axioms parser17
def cell18 : Array U8 16#usize := ⟨[222#u8,70#u8,169#u8,49#u8,31#u8,182#u8,16#u8,86#u8,14#u8,220#u8,44#u8,61#u8,17#u8,160#u8,90#u8,109#u8],by rfl⟩
def limbs18 : QM31Limbs := ![⟨833177310,by change 833177310<2147483647;omega⟩,⟨1443935775,by change 1443935775<2147483647;omega⟩,⟨1026350094,by change 1026350094<2147483647;omega⟩,⟨1834655761,by change 1834655761<2147483647;omega⟩]
theorem rawCell18 : (raw.drop 288).take 16=cell18.val := by
  simp only [raw,JFz_Scan50.data,JFz_Scan50.j00,JFz_Scan50.j01,JFz_Scan50.j02,JFz_Scan50.j03,JFz_Scan50.j04,JFz_Scan50.j05,JFz_Scan50.j06,JFz_Scan50.j07,JFz_Scan50.j08,JFz_Scan50.j09,JFz_Scan50.j10,JFz_Scan50.j11,JFz_Scan50.j12,JFz_Scan50.b00_length,JFz_Scan50.b01_length,JFz_Scan50.b02_length,JFz_Scan50.b03_length,JFz_Scan50.b04_length,JFz_Scan50.b05_length,JFz_Scan50.b06_length,JFz_Scan50.b07_length,JFz_Scan50.b08_length,JFz_Scan50.b09_length,JFz_Scan50.b10_length,JFz_Scan50.b11_length,JFz_Scan50.b12_length,JFz_Scan50.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell18
theorem encoded18 : CandidateParserByteOrder.arrayBytes16 cell18=encodeQM31LE limbs18 := by
  funext i
  fin_cases i <;> rfl
theorem parser18 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell18)=
    ok (some ⟨⟨833177310#u32,1443935775#u32⟩,⟨1026350094#u32,1834655761#u32⟩⟩) :=
  JFr_EncodedCell.parser cell18 limbs18 encoded18
#print axioms encoded18
#print axioms parser18
def cell19 : Array U8 16#usize := ⟨[245#u8,198#u8,21#u8,30#u8,53#u8,39#u8,110#u8,0#u8,11#u8,101#u8,17#u8,36#u8,132#u8,75#u8,167#u8,115#u8],by rfl⟩
def limbs19 : QM31Limbs := ![⟨504743669,by change 504743669<2147483647;omega⟩,⟨7218997,by change 7218997<2147483647;omega⟩,⟨605119755,by change 605119755<2147483647;omega⟩,⟨1940343684,by change 1940343684<2147483647;omega⟩]
theorem rawCell19 : (raw.drop 304).take 16=cell19.val := by
  simp only [raw,JFz_Scan50.data,JFz_Scan50.j00,JFz_Scan50.j01,JFz_Scan50.j02,JFz_Scan50.j03,JFz_Scan50.j04,JFz_Scan50.j05,JFz_Scan50.j06,JFz_Scan50.j07,JFz_Scan50.j08,JFz_Scan50.j09,JFz_Scan50.j10,JFz_Scan50.j11,JFz_Scan50.j12,JFz_Scan50.b00_length,JFz_Scan50.b01_length,JFz_Scan50.b02_length,JFz_Scan50.b03_length,JFz_Scan50.b04_length,JFz_Scan50.b05_length,JFz_Scan50.b06_length,JFz_Scan50.b07_length,JFz_Scan50.b08_length,JFz_Scan50.b09_length,JFz_Scan50.b10_length,JFz_Scan50.b11_length,JFz_Scan50.b12_length,JFz_Scan50.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell19
theorem encoded19 : CandidateParserByteOrder.arrayBytes16 cell19=encodeQM31LE limbs19 := by
  funext i
  fin_cases i <;> rfl
theorem parser19 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell19)=
    ok (some ⟨⟨504743669#u32,7218997#u32⟩,⟨605119755#u32,1940343684#u32⟩⟩) :=
  JFr_EncodedCell.parser cell19 limbs19 encoded19
#print axioms encoded19
#print axioms parser19
def cell20 : Array U8 16#usize := ⟨[54#u8,132#u8,170#u8,61#u8,173#u8,23#u8,196#u8,27#u8,1#u8,133#u8,134#u8,12#u8,72#u8,107#u8,4#u8,7#u8],by rfl⟩
def limbs20 : QM31Limbs := ![⟨1034585142,by change 1034585142<2147483647;omega⟩,⟨465835949,by change 465835949<2147483647;omega⟩,⟨210142465,by change 210142465<2147483647;omega⟩,⟨117730120,by change 117730120<2147483647;omega⟩]
theorem rawCell20 : (raw.drop 320).take 16=cell20.val := by
  simp only [raw,JFz_Scan50.data,JFz_Scan50.j00,JFz_Scan50.j01,JFz_Scan50.j02,JFz_Scan50.j03,JFz_Scan50.j04,JFz_Scan50.j05,JFz_Scan50.j06,JFz_Scan50.j07,JFz_Scan50.j08,JFz_Scan50.j09,JFz_Scan50.j10,JFz_Scan50.j11,JFz_Scan50.j12,JFz_Scan50.b00_length,JFz_Scan50.b01_length,JFz_Scan50.b02_length,JFz_Scan50.b03_length,JFz_Scan50.b04_length,JFz_Scan50.b05_length,JFz_Scan50.b06_length,JFz_Scan50.b07_length,JFz_Scan50.b08_length,JFz_Scan50.b09_length,JFz_Scan50.b10_length,JFz_Scan50.b11_length,JFz_Scan50.b12_length,JFz_Scan50.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell20
theorem encoded20 : CandidateParserByteOrder.arrayBytes16 cell20=encodeQM31LE limbs20 := by
  funext i
  fin_cases i <;> rfl
theorem parser20 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell20)=
    ok (some ⟨⟨1034585142#u32,465835949#u32⟩,⟨210142465#u32,117730120#u32⟩⟩) :=
  JFr_EncodedCell.parser cell20 limbs20 encoded20
#print axioms encoded20
#print axioms parser20
def cell21 : Array U8 16#usize := ⟨[48#u8,7#u8,251#u8,109#u8,233#u8,5#u8,198#u8,71#u8,143#u8,152#u8,76#u8,33#u8,253#u8,181#u8,222#u8,37#u8],by rfl⟩
def limbs21 : QM31Limbs := ![⟨1845167920,by change 1845167920<2147483647;omega⟩,⟨1204159977,by change 1204159977<2147483647;omega⟩,⟨558667919,by change 558667919<2147483647;omega⟩,⟨635352573,by change 635352573<2147483647;omega⟩]
theorem rawCell21 : (raw.drop 336).take 16=cell21.val := by
  simp only [raw,JFz_Scan50.data,JFz_Scan50.j00,JFz_Scan50.j01,JFz_Scan50.j02,JFz_Scan50.j03,JFz_Scan50.j04,JFz_Scan50.j05,JFz_Scan50.j06,JFz_Scan50.j07,JFz_Scan50.j08,JFz_Scan50.j09,JFz_Scan50.j10,JFz_Scan50.j11,JFz_Scan50.j12,JFz_Scan50.b00_length,JFz_Scan50.b01_length,JFz_Scan50.b02_length,JFz_Scan50.b03_length,JFz_Scan50.b04_length,JFz_Scan50.b05_length,JFz_Scan50.b06_length,JFz_Scan50.b07_length,JFz_Scan50.b08_length,JFz_Scan50.b09_length,JFz_Scan50.b10_length,JFz_Scan50.b11_length,JFz_Scan50.b12_length,JFz_Scan50.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell21
theorem encoded21 : CandidateParserByteOrder.arrayBytes16 cell21=encodeQM31LE limbs21 := by
  funext i
  fin_cases i <;> rfl
theorem parser21 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell21)=
    ok (some ⟨⟨1845167920#u32,1204159977#u32⟩,⟨558667919#u32,635352573#u32⟩⟩) :=
  JFr_EncodedCell.parser cell21 limbs21 encoded21
#print axioms encoded21
#print axioms parser21
def cell22 : Array U8 16#usize := ⟨[176#u8,110#u8,232#u8,109#u8,126#u8,82#u8,241#u8,102#u8,230#u8,12#u8,168#u8,37#u8,173#u8,139#u8,47#u8,55#u8],by rfl⟩
def limbs22 : QM31Limbs := ![⟨1843949232,by change 1843949232<2147483647;omega⟩,⟨1727091326,by change 1727091326<2147483647;omega⟩,⟨631770342,by change 631770342<2147483647;omega⟩,⟨925862829,by change 925862829<2147483647;omega⟩]
theorem rawCell22 : (raw.drop 352).take 16=cell22.val := by
  simp only [raw,JFz_Scan50.data,JFz_Scan50.j00,JFz_Scan50.j01,JFz_Scan50.j02,JFz_Scan50.j03,JFz_Scan50.j04,JFz_Scan50.j05,JFz_Scan50.j06,JFz_Scan50.j07,JFz_Scan50.j08,JFz_Scan50.j09,JFz_Scan50.j10,JFz_Scan50.j11,JFz_Scan50.j12,JFz_Scan50.b00_length,JFz_Scan50.b01_length,JFz_Scan50.b02_length,JFz_Scan50.b03_length,JFz_Scan50.b04_length,JFz_Scan50.b05_length,JFz_Scan50.b06_length,JFz_Scan50.b07_length,JFz_Scan50.b08_length,JFz_Scan50.b09_length,JFz_Scan50.b10_length,JFz_Scan50.b11_length,JFz_Scan50.b12_length,JFz_Scan50.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell22
theorem encoded22 : CandidateParserByteOrder.arrayBytes16 cell22=encodeQM31LE limbs22 := by
  funext i
  fin_cases i <;> rfl
theorem parser22 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell22)=
    ok (some ⟨⟨1843949232#u32,1727091326#u32⟩,⟨631770342#u32,925862829#u32⟩⟩) :=
  JFr_EncodedCell.parser cell22 limbs22 encoded22
#print axioms encoded22
#print axioms parser22
def cell23 : Array U8 16#usize := ⟨[239#u8,45#u8,191#u8,92#u8,30#u8,74#u8,33#u8,41#u8,35#u8,166#u8,188#u8,106#u8,147#u8,248#u8,253#u8,87#u8],by rfl⟩
def limbs23 : QM31Limbs := ![⟨1556033007,by change 1556033007<2147483647;omega⟩,⟨690047518,by change 690047518<2147483647;omega⟩,⟨1790748195,by change 1790748195<2147483647;omega⟩,⟨1476262035,by change 1476262035<2147483647;omega⟩]
theorem rawCell23 : (raw.drop 368).take 16=cell23.val := by
  simp only [raw,JFz_Scan50.data,JFz_Scan50.j00,JFz_Scan50.j01,JFz_Scan50.j02,JFz_Scan50.j03,JFz_Scan50.j04,JFz_Scan50.j05,JFz_Scan50.j06,JFz_Scan50.j07,JFz_Scan50.j08,JFz_Scan50.j09,JFz_Scan50.j10,JFz_Scan50.j11,JFz_Scan50.j12,JFz_Scan50.b00_length,JFz_Scan50.b01_length,JFz_Scan50.b02_length,JFz_Scan50.b03_length,JFz_Scan50.b04_length,JFz_Scan50.b05_length,JFz_Scan50.b06_length,JFz_Scan50.b07_length,JFz_Scan50.b08_length,JFz_Scan50.b09_length,JFz_Scan50.b10_length,JFz_Scan50.b11_length,JFz_Scan50.b12_length,JFz_Scan50.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell23
theorem encoded23 : CandidateParserByteOrder.arrayBytes16 cell23=encodeQM31LE limbs23 := by
  funext i
  fin_cases i <;> rfl
theorem parser23 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell23)=
    ok (some ⟨⟨1556033007#u32,690047518#u32⟩,⟨1790748195#u32,1476262035#u32⟩⟩) :=
  JFr_EncodedCell.parser cell23 limbs23 encoded23
#print axioms encoded23
#print axioms parser23
def cell24 : Array U8 16#usize := ⟨[102#u8,28#u8,171#u8,123#u8,214#u8,59#u8,18#u8,117#u8,184#u8,208#u8,231#u8,51#u8,183#u8,51#u8,99#u8,102#u8],by rfl⟩
def limbs24 : QM31Limbs := ![⟨2074811494,by change 2074811494<2147483647;omega⟩,⟨1964129238,by change 1964129238<2147483647;omega⟩,⟨870830264,by change 870830264<2147483647;omega⟩,⟨1717777335,by change 1717777335<2147483647;omega⟩]
theorem rawCell24 : (raw.drop 384).take 16=cell24.val := by
  simp only [raw,JFz_Scan50.data,JFz_Scan50.j00,JFz_Scan50.j01,JFz_Scan50.j02,JFz_Scan50.j03,JFz_Scan50.j04,JFz_Scan50.j05,JFz_Scan50.j06,JFz_Scan50.j07,JFz_Scan50.j08,JFz_Scan50.j09,JFz_Scan50.j10,JFz_Scan50.j11,JFz_Scan50.j12,JFz_Scan50.b00_length,JFz_Scan50.b01_length,JFz_Scan50.b02_length,JFz_Scan50.b03_length,JFz_Scan50.b04_length,JFz_Scan50.b05_length,JFz_Scan50.b06_length,JFz_Scan50.b07_length,JFz_Scan50.b08_length,JFz_Scan50.b09_length,JFz_Scan50.b10_length,JFz_Scan50.b11_length,JFz_Scan50.b12_length,JFz_Scan50.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell24
theorem encoded24 : CandidateParserByteOrder.arrayBytes16 cell24=encodeQM31LE limbs24 := by
  funext i
  fin_cases i <;> rfl
theorem parser24 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell24)=
    ok (some ⟨⟨2074811494#u32,1964129238#u32⟩,⟨870830264#u32,1717777335#u32⟩⟩) :=
  JFr_EncodedCell.parser cell24 limbs24 encoded24
#print axioms encoded24
#print axioms parser24
def cell25 : Array U8 16#usize := ⟨[73#u8,189#u8,71#u8,77#u8,93#u8,177#u8,67#u8,30#u8,128#u8,171#u8,206#u8,57#u8,208#u8,53#u8,180#u8,39#u8],by rfl⟩
def limbs25 : QM31Limbs := ![⟨1296547145,by change 1296547145<2147483647;omega⟩,⟨507752797,by change 507752797<2147483647;omega⟩,⟨969845632,by change 969845632<2147483647;omega⟩,⟨666121680,by change 666121680<2147483647;omega⟩]
theorem rawCell25 : (raw.drop 400).take 16=cell25.val := by
  simp only [raw,JFz_Scan50.data,JFz_Scan50.j00,JFz_Scan50.j01,JFz_Scan50.j02,JFz_Scan50.j03,JFz_Scan50.j04,JFz_Scan50.j05,JFz_Scan50.j06,JFz_Scan50.j07,JFz_Scan50.j08,JFz_Scan50.j09,JFz_Scan50.j10,JFz_Scan50.j11,JFz_Scan50.j12,JFz_Scan50.b00_length,JFz_Scan50.b01_length,JFz_Scan50.b02_length,JFz_Scan50.b03_length,JFz_Scan50.b04_length,JFz_Scan50.b05_length,JFz_Scan50.b06_length,JFz_Scan50.b07_length,JFz_Scan50.b08_length,JFz_Scan50.b09_length,JFz_Scan50.b10_length,JFz_Scan50.b11_length,JFz_Scan50.b12_length,JFz_Scan50.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell25
theorem encoded25 : CandidateParserByteOrder.arrayBytes16 cell25=encodeQM31LE limbs25 := by
  funext i
  fin_cases i <;> rfl
theorem parser25 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell25)=
    ok (some ⟨⟨1296547145#u32,507752797#u32⟩,⟨969845632#u32,666121680#u32⟩⟩) :=
  JFr_EncodedCell.parser cell25 limbs25 encoded25
#print axioms encoded25
#print axioms parser25
def cell26 : Array U8 16#usize := ⟨[129#u8,7#u8,190#u8,23#u8,243#u8,86#u8,35#u8,8#u8,255#u8,45#u8,76#u8,59#u8,186#u8,153#u8,58#u8,36#u8],by rfl⟩
def limbs26 : QM31Limbs := ![⟨398329729,by change 398329729<2147483647;omega⟩,⟨136533747,by change 136533747<2147483647;omega⟩,⟨994848255,by change 994848255<2147483647;omega⟩,⟨607820218,by change 607820218<2147483647;omega⟩]
theorem rawCell26 : (raw.drop 416).take 16=cell26.val := by
  simp only [raw,JFz_Scan50.data,JFz_Scan50.j00,JFz_Scan50.j01,JFz_Scan50.j02,JFz_Scan50.j03,JFz_Scan50.j04,JFz_Scan50.j05,JFz_Scan50.j06,JFz_Scan50.j07,JFz_Scan50.j08,JFz_Scan50.j09,JFz_Scan50.j10,JFz_Scan50.j11,JFz_Scan50.j12,JFz_Scan50.b00_length,JFz_Scan50.b01_length,JFz_Scan50.b02_length,JFz_Scan50.b03_length,JFz_Scan50.b04_length,JFz_Scan50.b05_length,JFz_Scan50.b06_length,JFz_Scan50.b07_length,JFz_Scan50.b08_length,JFz_Scan50.b09_length,JFz_Scan50.b10_length,JFz_Scan50.b11_length,JFz_Scan50.b12_length,JFz_Scan50.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell26
theorem encoded26 : CandidateParserByteOrder.arrayBytes16 cell26=encodeQM31LE limbs26 := by
  funext i
  fin_cases i <;> rfl
theorem parser26 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell26)=
    ok (some ⟨⟨398329729#u32,136533747#u32⟩,⟨994848255#u32,607820218#u32⟩⟩) :=
  JFr_EncodedCell.parser cell26 limbs26 encoded26
#print axioms encoded26
#print axioms parser26
def cell27 : Array U8 16#usize := ⟨[88#u8,178#u8,46#u8,81#u8,226#u8,198#u8,164#u8,127#u8,161#u8,24#u8,253#u8,97#u8,159#u8,240#u8,153#u8,100#u8],by rfl⟩
def limbs27 : QM31Limbs := ![⟨1362014808,by change 1362014808<2147483647;omega⟩,⟨2141505250,by change 2141505250<2147483647;omega⟩,⟨1643976865,by change 1643976865<2147483647;omega⟩,⟨1687810207,by change 1687810207<2147483647;omega⟩]
theorem rawCell27 : (raw.drop 432).take 16=cell27.val := by
  simp only [raw,JFz_Scan50.data,JFz_Scan50.j00,JFz_Scan50.j01,JFz_Scan50.j02,JFz_Scan50.j03,JFz_Scan50.j04,JFz_Scan50.j05,JFz_Scan50.j06,JFz_Scan50.j07,JFz_Scan50.j08,JFz_Scan50.j09,JFz_Scan50.j10,JFz_Scan50.j11,JFz_Scan50.j12,JFz_Scan50.b00_length,JFz_Scan50.b01_length,JFz_Scan50.b02_length,JFz_Scan50.b03_length,JFz_Scan50.b04_length,JFz_Scan50.b05_length,JFz_Scan50.b06_length,JFz_Scan50.b07_length,JFz_Scan50.b08_length,JFz_Scan50.b09_length,JFz_Scan50.b10_length,JFz_Scan50.b11_length,JFz_Scan50.b12_length,JFz_Scan50.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell27
theorem encoded27 : CandidateParserByteOrder.arrayBytes16 cell27=encodeQM31LE limbs27 := by
  funext i
  fin_cases i <;> rfl
theorem parser27 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell27)=
    ok (some ⟨⟨1362014808#u32,2141505250#u32⟩,⟨1643976865#u32,1687810207#u32⟩⟩) :=
  JFr_EncodedCell.parser cell27 limbs27 encoded27
#print axioms encoded27
#print axioms parser27
end AspisR1.JFr_Bytes02
