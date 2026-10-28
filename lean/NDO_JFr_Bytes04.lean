import NDO_JFr_Data04
import NDO_JFr_EncodedCell
import NDO_JFz_Scan52
set_option autoImplicit false
namespace AspisR1.JFr_Bytes04
open Aeneas Aeneas.Std Result RetainedFieldByteCodec
open AspisR1PublicPreparation
open AspisS1ExtractedRoundChildren
def raw : List U8 := JFz_Scan52.data
theorem rawLength : raw.length=448 := JFz_Scan52.length
#print axioms rawLength
theorem selected : (JFx_NativeBytes.proof.val.drop 1988).take 448=raw := JFz_Scan52.selected
#print axioms selected
def cell00 : Array U8 16#usize := ⟨[185#u8,199#u8,68#u8,115#u8,245#u8,182#u8,10#u8,6#u8,168#u8,223#u8,18#u8,123#u8,54#u8,155#u8,186#u8,82#u8],by rfl⟩
def limbs00 : QM31Limbs := ![⟨1933887417,by change 1933887417<2147483647;omega⟩,⟨101365493,by change 101365493<2147483647;omega⟩,⟨2064834472,by change 2064834472<2147483647;omega⟩,⟨1387961142,by change 1387961142<2147483647;omega⟩]
theorem rawCell00 : (raw.drop 0).take 16=cell00.val := by
  simp only [raw,JFz_Scan52.data,JFz_Scan52.j00,JFz_Scan52.j01,JFz_Scan52.j02,JFz_Scan52.j03,JFz_Scan52.j04,JFz_Scan52.j05,JFz_Scan52.j06,JFz_Scan52.j07,JFz_Scan52.j08,JFz_Scan52.j09,JFz_Scan52.j10,JFz_Scan52.j11,JFz_Scan52.j12,JFz_Scan52.b00_length,JFz_Scan52.b01_length,JFz_Scan52.b02_length,JFz_Scan52.b03_length,JFz_Scan52.b04_length,JFz_Scan52.b05_length,JFz_Scan52.b06_length,JFz_Scan52.b07_length,JFz_Scan52.b08_length,JFz_Scan52.b09_length,JFz_Scan52.b10_length,JFz_Scan52.b11_length,JFz_Scan52.b12_length,JFz_Scan52.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell00
theorem encoded00 : CandidateParserByteOrder.arrayBytes16 cell00=encodeQM31LE limbs00 := by
  funext i
  fin_cases i <;> rfl
theorem parser00 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell00)=
    ok (some ⟨⟨1933887417#u32,101365493#u32⟩,⟨2064834472#u32,1387961142#u32⟩⟩) :=
  JFr_EncodedCell.parser cell00 limbs00 encoded00
#print axioms encoded00
#print axioms parser00
def cell01 : Array U8 16#usize := ⟨[237#u8,201#u8,120#u8,19#u8,176#u8,125#u8,19#u8,35#u8,112#u8,65#u8,35#u8,68#u8,71#u8,79#u8,214#u8,99#u8],by rfl⟩
def limbs01 : QM31Limbs := ![⟨326683117,by change 326683117<2147483647;omega⟩,⟨588479920,by change 588479920<2147483647;omega⟩,⟨1143161200,by change 1143161200<2147483647;omega⟩,⟨1674989383,by change 1674989383<2147483647;omega⟩]
theorem rawCell01 : (raw.drop 16).take 16=cell01.val := by
  simp only [raw,JFz_Scan52.data,JFz_Scan52.j00,JFz_Scan52.j01,JFz_Scan52.j02,JFz_Scan52.j03,JFz_Scan52.j04,JFz_Scan52.j05,JFz_Scan52.j06,JFz_Scan52.j07,JFz_Scan52.j08,JFz_Scan52.j09,JFz_Scan52.j10,JFz_Scan52.j11,JFz_Scan52.j12,JFz_Scan52.b00_length,JFz_Scan52.b01_length,JFz_Scan52.b02_length,JFz_Scan52.b03_length,JFz_Scan52.b04_length,JFz_Scan52.b05_length,JFz_Scan52.b06_length,JFz_Scan52.b07_length,JFz_Scan52.b08_length,JFz_Scan52.b09_length,JFz_Scan52.b10_length,JFz_Scan52.b11_length,JFz_Scan52.b12_length,JFz_Scan52.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell01
theorem encoded01 : CandidateParserByteOrder.arrayBytes16 cell01=encodeQM31LE limbs01 := by
  funext i
  fin_cases i <;> rfl
theorem parser01 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell01)=
    ok (some ⟨⟨326683117#u32,588479920#u32⟩,⟨1143161200#u32,1674989383#u32⟩⟩) :=
  JFr_EncodedCell.parser cell01 limbs01 encoded01
#print axioms encoded01
#print axioms parser01
def cell02 : Array U8 16#usize := ⟨[137#u8,159#u8,103#u8,17#u8,120#u8,201#u8,150#u8,47#u8,175#u8,40#u8,218#u8,63#u8,51#u8,96#u8,152#u8,125#u8],by rfl⟩
def limbs02 : QM31Limbs := ![⟨292003721,by change 292003721<2147483647;omega⟩,⟨798411128,by change 798411128<2147483647;omega⟩,⟨1071261871,by change 1071261871<2147483647;omega⟩,⟨2107138099,by change 2107138099<2147483647;omega⟩]
theorem rawCell02 : (raw.drop 32).take 16=cell02.val := by
  simp only [raw,JFz_Scan52.data,JFz_Scan52.j00,JFz_Scan52.j01,JFz_Scan52.j02,JFz_Scan52.j03,JFz_Scan52.j04,JFz_Scan52.j05,JFz_Scan52.j06,JFz_Scan52.j07,JFz_Scan52.j08,JFz_Scan52.j09,JFz_Scan52.j10,JFz_Scan52.j11,JFz_Scan52.j12,JFz_Scan52.b00_length,JFz_Scan52.b01_length,JFz_Scan52.b02_length,JFz_Scan52.b03_length,JFz_Scan52.b04_length,JFz_Scan52.b05_length,JFz_Scan52.b06_length,JFz_Scan52.b07_length,JFz_Scan52.b08_length,JFz_Scan52.b09_length,JFz_Scan52.b10_length,JFz_Scan52.b11_length,JFz_Scan52.b12_length,JFz_Scan52.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell02
theorem encoded02 : CandidateParserByteOrder.arrayBytes16 cell02=encodeQM31LE limbs02 := by
  funext i
  fin_cases i <;> rfl
theorem parser02 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell02)=
    ok (some ⟨⟨292003721#u32,798411128#u32⟩,⟨1071261871#u32,2107138099#u32⟩⟩) :=
  JFr_EncodedCell.parser cell02 limbs02 encoded02
#print axioms encoded02
#print axioms parser02
def cell03 : Array U8 16#usize := ⟨[214#u8,143#u8,95#u8,6#u8,47#u8,24#u8,206#u8,120#u8,5#u8,50#u8,208#u8,61#u8,74#u8,161#u8,7#u8,106#u8],by rfl⟩
def limbs03 : QM31Limbs := ![⟨106926038,by change 106926038<2147483647;omega⟩,⟨2026772527,by change 2026772527<2147483647;omega⟩,⟨1037054469,by change 1037054469<2147483647;omega⟩,⟨1778884938,by change 1778884938<2147483647;omega⟩]
theorem rawCell03 : (raw.drop 48).take 16=cell03.val := by
  simp only [raw,JFz_Scan52.data,JFz_Scan52.j00,JFz_Scan52.j01,JFz_Scan52.j02,JFz_Scan52.j03,JFz_Scan52.j04,JFz_Scan52.j05,JFz_Scan52.j06,JFz_Scan52.j07,JFz_Scan52.j08,JFz_Scan52.j09,JFz_Scan52.j10,JFz_Scan52.j11,JFz_Scan52.j12,JFz_Scan52.b00_length,JFz_Scan52.b01_length,JFz_Scan52.b02_length,JFz_Scan52.b03_length,JFz_Scan52.b04_length,JFz_Scan52.b05_length,JFz_Scan52.b06_length,JFz_Scan52.b07_length,JFz_Scan52.b08_length,JFz_Scan52.b09_length,JFz_Scan52.b10_length,JFz_Scan52.b11_length,JFz_Scan52.b12_length,JFz_Scan52.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell03
theorem encoded03 : CandidateParserByteOrder.arrayBytes16 cell03=encodeQM31LE limbs03 := by
  funext i
  fin_cases i <;> rfl
theorem parser03 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell03)=
    ok (some ⟨⟨106926038#u32,2026772527#u32⟩,⟨1037054469#u32,1778884938#u32⟩⟩) :=
  JFr_EncodedCell.parser cell03 limbs03 encoded03
#print axioms encoded03
#print axioms parser03
def cell04 : Array U8 16#usize := ⟨[115#u8,214#u8,132#u8,20#u8,30#u8,65#u8,235#u8,32#u8,167#u8,114#u8,215#u8,114#u8,178#u8,165#u8,85#u8,85#u8],by rfl⟩
def limbs04 : QM31Limbs := ![⟨344249971,by change 344249971<2147483647;omega⟩,⟨552288542,by change 552288542<2147483647;omega⟩,⟨1926722215,by change 1926722215<2147483647;omega⟩,⟨1431676338,by change 1431676338<2147483647;omega⟩]
theorem rawCell04 : (raw.drop 64).take 16=cell04.val := by
  simp only [raw,JFz_Scan52.data,JFz_Scan52.j00,JFz_Scan52.j01,JFz_Scan52.j02,JFz_Scan52.j03,JFz_Scan52.j04,JFz_Scan52.j05,JFz_Scan52.j06,JFz_Scan52.j07,JFz_Scan52.j08,JFz_Scan52.j09,JFz_Scan52.j10,JFz_Scan52.j11,JFz_Scan52.j12,JFz_Scan52.b00_length,JFz_Scan52.b01_length,JFz_Scan52.b02_length,JFz_Scan52.b03_length,JFz_Scan52.b04_length,JFz_Scan52.b05_length,JFz_Scan52.b06_length,JFz_Scan52.b07_length,JFz_Scan52.b08_length,JFz_Scan52.b09_length,JFz_Scan52.b10_length,JFz_Scan52.b11_length,JFz_Scan52.b12_length,JFz_Scan52.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell04
theorem encoded04 : CandidateParserByteOrder.arrayBytes16 cell04=encodeQM31LE limbs04 := by
  funext i
  fin_cases i <;> rfl
theorem parser04 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell04)=
    ok (some ⟨⟨344249971#u32,552288542#u32⟩,⟨1926722215#u32,1431676338#u32⟩⟩) :=
  JFr_EncodedCell.parser cell04 limbs04 encoded04
#print axioms encoded04
#print axioms parser04
def cell05 : Array U8 16#usize := ⟨[101#u8,141#u8,50#u8,21#u8,74#u8,236#u8,196#u8,5#u8,13#u8,97#u8,61#u8,91#u8,140#u8,140#u8,226#u8,5#u8],by rfl⟩
def limbs05 : QM31Limbs := ![⟨355634533,by change 355634533<2147483647;omega⟩,⟨96791626,by change 96791626<2147483647;omega⟩,⟨1530749197,by change 1530749197<2147483647;omega⟩,⟨98733196,by change 98733196<2147483647;omega⟩]
theorem rawCell05 : (raw.drop 80).take 16=cell05.val := by
  simp only [raw,JFz_Scan52.data,JFz_Scan52.j00,JFz_Scan52.j01,JFz_Scan52.j02,JFz_Scan52.j03,JFz_Scan52.j04,JFz_Scan52.j05,JFz_Scan52.j06,JFz_Scan52.j07,JFz_Scan52.j08,JFz_Scan52.j09,JFz_Scan52.j10,JFz_Scan52.j11,JFz_Scan52.j12,JFz_Scan52.b00_length,JFz_Scan52.b01_length,JFz_Scan52.b02_length,JFz_Scan52.b03_length,JFz_Scan52.b04_length,JFz_Scan52.b05_length,JFz_Scan52.b06_length,JFz_Scan52.b07_length,JFz_Scan52.b08_length,JFz_Scan52.b09_length,JFz_Scan52.b10_length,JFz_Scan52.b11_length,JFz_Scan52.b12_length,JFz_Scan52.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell05
theorem encoded05 : CandidateParserByteOrder.arrayBytes16 cell05=encodeQM31LE limbs05 := by
  funext i
  fin_cases i <;> rfl
theorem parser05 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell05)=
    ok (some ⟨⟨355634533#u32,96791626#u32⟩,⟨1530749197#u32,98733196#u32⟩⟩) :=
  JFr_EncodedCell.parser cell05 limbs05 encoded05
#print axioms encoded05
#print axioms parser05
def cell06 : Array U8 16#usize := ⟨[167#u8,132#u8,211#u8,118#u8,165#u8,235#u8,252#u8,80#u8,225#u8,202#u8,7#u8,60#u8,95#u8,25#u8,187#u8,99#u8],by rfl⟩
def limbs06 : QM31Limbs := ![⟨1993573543,by change 1993573543<2147483647;omega⟩,⟨1358752677,by change 1358752677<2147483647;omega⟩,⟨1007143649,by change 1007143649<2147483647;omega⟩,⟨1673206111,by change 1673206111<2147483647;omega⟩]
theorem rawCell06 : (raw.drop 96).take 16=cell06.val := by
  simp only [raw,JFz_Scan52.data,JFz_Scan52.j00,JFz_Scan52.j01,JFz_Scan52.j02,JFz_Scan52.j03,JFz_Scan52.j04,JFz_Scan52.j05,JFz_Scan52.j06,JFz_Scan52.j07,JFz_Scan52.j08,JFz_Scan52.j09,JFz_Scan52.j10,JFz_Scan52.j11,JFz_Scan52.j12,JFz_Scan52.b00_length,JFz_Scan52.b01_length,JFz_Scan52.b02_length,JFz_Scan52.b03_length,JFz_Scan52.b04_length,JFz_Scan52.b05_length,JFz_Scan52.b06_length,JFz_Scan52.b07_length,JFz_Scan52.b08_length,JFz_Scan52.b09_length,JFz_Scan52.b10_length,JFz_Scan52.b11_length,JFz_Scan52.b12_length,JFz_Scan52.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell06
theorem encoded06 : CandidateParserByteOrder.arrayBytes16 cell06=encodeQM31LE limbs06 := by
  funext i
  fin_cases i <;> rfl
theorem parser06 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell06)=
    ok (some ⟨⟨1993573543#u32,1358752677#u32⟩,⟨1007143649#u32,1673206111#u32⟩⟩) :=
  JFr_EncodedCell.parser cell06 limbs06 encoded06
#print axioms encoded06
#print axioms parser06
def cell07 : Array U8 16#usize := ⟨[221#u8,46#u8,36#u8,99#u8,26#u8,207#u8,189#u8,92#u8,4#u8,7#u8,80#u8,104#u8,35#u8,207#u8,43#u8,57#u8],by rfl⟩
def limbs07 : QM31Limbs := ![⟨1663315677,by change 1663315677<2147483647;omega⟩,⟨1555943194,by change 1555943194<2147483647;omega⟩,⟨1750075140,by change 1750075140<2147483647;omega⟩,⟨959172387,by change 959172387<2147483647;omega⟩]
theorem rawCell07 : (raw.drop 112).take 16=cell07.val := by
  simp only [raw,JFz_Scan52.data,JFz_Scan52.j00,JFz_Scan52.j01,JFz_Scan52.j02,JFz_Scan52.j03,JFz_Scan52.j04,JFz_Scan52.j05,JFz_Scan52.j06,JFz_Scan52.j07,JFz_Scan52.j08,JFz_Scan52.j09,JFz_Scan52.j10,JFz_Scan52.j11,JFz_Scan52.j12,JFz_Scan52.b00_length,JFz_Scan52.b01_length,JFz_Scan52.b02_length,JFz_Scan52.b03_length,JFz_Scan52.b04_length,JFz_Scan52.b05_length,JFz_Scan52.b06_length,JFz_Scan52.b07_length,JFz_Scan52.b08_length,JFz_Scan52.b09_length,JFz_Scan52.b10_length,JFz_Scan52.b11_length,JFz_Scan52.b12_length,JFz_Scan52.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell07
theorem encoded07 : CandidateParserByteOrder.arrayBytes16 cell07=encodeQM31LE limbs07 := by
  funext i
  fin_cases i <;> rfl
theorem parser07 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell07)=
    ok (some ⟨⟨1663315677#u32,1555943194#u32⟩,⟨1750075140#u32,959172387#u32⟩⟩) :=
  JFr_EncodedCell.parser cell07 limbs07 encoded07
#print axioms encoded07
#print axioms parser07
def cell08 : Array U8 16#usize := ⟨[146#u8,217#u8,136#u8,29#u8,221#u8,81#u8,184#u8,113#u8,46#u8,36#u8,56#u8,20#u8,122#u8,211#u8,171#u8,27#u8],by rfl⟩
def limbs08 : QM31Limbs := ![⟨495507858,by change 495507858<2147483647;omega⟩,⟨1907904989,by change 1907904989<2147483647;omega⟩,⟨339223598,by change 339223598<2147483647;omega⟩,⟨464245626,by change 464245626<2147483647;omega⟩]
theorem rawCell08 : (raw.drop 128).take 16=cell08.val := by
  simp only [raw,JFz_Scan52.data,JFz_Scan52.j00,JFz_Scan52.j01,JFz_Scan52.j02,JFz_Scan52.j03,JFz_Scan52.j04,JFz_Scan52.j05,JFz_Scan52.j06,JFz_Scan52.j07,JFz_Scan52.j08,JFz_Scan52.j09,JFz_Scan52.j10,JFz_Scan52.j11,JFz_Scan52.j12,JFz_Scan52.b00_length,JFz_Scan52.b01_length,JFz_Scan52.b02_length,JFz_Scan52.b03_length,JFz_Scan52.b04_length,JFz_Scan52.b05_length,JFz_Scan52.b06_length,JFz_Scan52.b07_length,JFz_Scan52.b08_length,JFz_Scan52.b09_length,JFz_Scan52.b10_length,JFz_Scan52.b11_length,JFz_Scan52.b12_length,JFz_Scan52.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell08
theorem encoded08 : CandidateParserByteOrder.arrayBytes16 cell08=encodeQM31LE limbs08 := by
  funext i
  fin_cases i <;> rfl
theorem parser08 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell08)=
    ok (some ⟨⟨495507858#u32,1907904989#u32⟩,⟨339223598#u32,464245626#u32⟩⟩) :=
  JFr_EncodedCell.parser cell08 limbs08 encoded08
#print axioms encoded08
#print axioms parser08
def cell09 : Array U8 16#usize := ⟨[130#u8,207#u8,173#u8,113#u8,185#u8,103#u8,227#u8,102#u8,111#u8,133#u8,184#u8,104#u8,192#u8,46#u8,219#u8,27#u8],by rfl⟩
def limbs09 : QM31Limbs := ![⟨1907216258,by change 1907216258<2147483647;omega⟩,⟨1726179257,by change 1726179257<2147483647;omega⟩,⟨1756923247,by change 1756923247<2147483647;omega⟩,⟨467349184,by change 467349184<2147483647;omega⟩]
theorem rawCell09 : (raw.drop 144).take 16=cell09.val := by
  simp only [raw,JFz_Scan52.data,JFz_Scan52.j00,JFz_Scan52.j01,JFz_Scan52.j02,JFz_Scan52.j03,JFz_Scan52.j04,JFz_Scan52.j05,JFz_Scan52.j06,JFz_Scan52.j07,JFz_Scan52.j08,JFz_Scan52.j09,JFz_Scan52.j10,JFz_Scan52.j11,JFz_Scan52.j12,JFz_Scan52.b00_length,JFz_Scan52.b01_length,JFz_Scan52.b02_length,JFz_Scan52.b03_length,JFz_Scan52.b04_length,JFz_Scan52.b05_length,JFz_Scan52.b06_length,JFz_Scan52.b07_length,JFz_Scan52.b08_length,JFz_Scan52.b09_length,JFz_Scan52.b10_length,JFz_Scan52.b11_length,JFz_Scan52.b12_length,JFz_Scan52.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell09
theorem encoded09 : CandidateParserByteOrder.arrayBytes16 cell09=encodeQM31LE limbs09 := by
  funext i
  fin_cases i <;> rfl
theorem parser09 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell09)=
    ok (some ⟨⟨1907216258#u32,1726179257#u32⟩,⟨1756923247#u32,467349184#u32⟩⟩) :=
  JFr_EncodedCell.parser cell09 limbs09 encoded09
#print axioms encoded09
#print axioms parser09
def cell10 : Array U8 16#usize := ⟨[180#u8,167#u8,77#u8,84#u8,79#u8,69#u8,132#u8,48#u8,57#u8,24#u8,70#u8,68#u8,138#u8,123#u8,66#u8,125#u8],by rfl⟩
def limbs10 : QM31Limbs := ![⟨1414375348,by change 1414375348<2147483647;omega⟩,⟨813974863,by change 813974863<2147483647;omega⟩,⟨1145444409,by change 1145444409<2147483647;omega⟩,⟨2101509002,by change 2101509002<2147483647;omega⟩]
theorem rawCell10 : (raw.drop 160).take 16=cell10.val := by
  simp only [raw,JFz_Scan52.data,JFz_Scan52.j00,JFz_Scan52.j01,JFz_Scan52.j02,JFz_Scan52.j03,JFz_Scan52.j04,JFz_Scan52.j05,JFz_Scan52.j06,JFz_Scan52.j07,JFz_Scan52.j08,JFz_Scan52.j09,JFz_Scan52.j10,JFz_Scan52.j11,JFz_Scan52.j12,JFz_Scan52.b00_length,JFz_Scan52.b01_length,JFz_Scan52.b02_length,JFz_Scan52.b03_length,JFz_Scan52.b04_length,JFz_Scan52.b05_length,JFz_Scan52.b06_length,JFz_Scan52.b07_length,JFz_Scan52.b08_length,JFz_Scan52.b09_length,JFz_Scan52.b10_length,JFz_Scan52.b11_length,JFz_Scan52.b12_length,JFz_Scan52.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell10
theorem encoded10 : CandidateParserByteOrder.arrayBytes16 cell10=encodeQM31LE limbs10 := by
  funext i
  fin_cases i <;> rfl
theorem parser10 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell10)=
    ok (some ⟨⟨1414375348#u32,813974863#u32⟩,⟨1145444409#u32,2101509002#u32⟩⟩) :=
  JFr_EncodedCell.parser cell10 limbs10 encoded10
#print axioms encoded10
#print axioms parser10
def cell11 : Array U8 16#usize := ⟨[81#u8,235#u8,92#u8,120#u8,3#u8,204#u8,158#u8,31#u8,96#u8,78#u8,57#u8,1#u8,210#u8,108#u8,207#u8,80#u8],by rfl⟩
def limbs11 : QM31Limbs := ![⟨2019355473,by change 2019355473<2147483647;omega⟩,⟨530500611,by change 530500611<2147483647;omega⟩,⟨20532832,by change 20532832<2147483647;omega⟩,⟨1355771090,by change 1355771090<2147483647;omega⟩]
theorem rawCell11 : (raw.drop 176).take 16=cell11.val := by
  simp only [raw,JFz_Scan52.data,JFz_Scan52.j00,JFz_Scan52.j01,JFz_Scan52.j02,JFz_Scan52.j03,JFz_Scan52.j04,JFz_Scan52.j05,JFz_Scan52.j06,JFz_Scan52.j07,JFz_Scan52.j08,JFz_Scan52.j09,JFz_Scan52.j10,JFz_Scan52.j11,JFz_Scan52.j12,JFz_Scan52.b00_length,JFz_Scan52.b01_length,JFz_Scan52.b02_length,JFz_Scan52.b03_length,JFz_Scan52.b04_length,JFz_Scan52.b05_length,JFz_Scan52.b06_length,JFz_Scan52.b07_length,JFz_Scan52.b08_length,JFz_Scan52.b09_length,JFz_Scan52.b10_length,JFz_Scan52.b11_length,JFz_Scan52.b12_length,JFz_Scan52.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell11
theorem encoded11 : CandidateParserByteOrder.arrayBytes16 cell11=encodeQM31LE limbs11 := by
  funext i
  fin_cases i <;> rfl
theorem parser11 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell11)=
    ok (some ⟨⟨2019355473#u32,530500611#u32⟩,⟨20532832#u32,1355771090#u32⟩⟩) :=
  JFr_EncodedCell.parser cell11 limbs11 encoded11
#print axioms encoded11
#print axioms parser11
def cell12 : Array U8 16#usize := ⟨[17#u8,2#u8,95#u8,42#u8,2#u8,52#u8,156#u8,76#u8,35#u8,139#u8,56#u8,21#u8,86#u8,0#u8,237#u8,126#u8],by rfl⟩
def limbs12 : QM31Limbs := ![⟨710869521,by change 710869521<2147483647;omega⟩,⟨1285305346,by change 1285305346<2147483647;omega⟩,⟨356027171,by change 356027171<2147483647;omega⟩,⟨2129461334,by change 2129461334<2147483647;omega⟩]
theorem rawCell12 : (raw.drop 192).take 16=cell12.val := by
  simp only [raw,JFz_Scan52.data,JFz_Scan52.j00,JFz_Scan52.j01,JFz_Scan52.j02,JFz_Scan52.j03,JFz_Scan52.j04,JFz_Scan52.j05,JFz_Scan52.j06,JFz_Scan52.j07,JFz_Scan52.j08,JFz_Scan52.j09,JFz_Scan52.j10,JFz_Scan52.j11,JFz_Scan52.j12,JFz_Scan52.b00_length,JFz_Scan52.b01_length,JFz_Scan52.b02_length,JFz_Scan52.b03_length,JFz_Scan52.b04_length,JFz_Scan52.b05_length,JFz_Scan52.b06_length,JFz_Scan52.b07_length,JFz_Scan52.b08_length,JFz_Scan52.b09_length,JFz_Scan52.b10_length,JFz_Scan52.b11_length,JFz_Scan52.b12_length,JFz_Scan52.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell12
theorem encoded12 : CandidateParserByteOrder.arrayBytes16 cell12=encodeQM31LE limbs12 := by
  funext i
  fin_cases i <;> rfl
theorem parser12 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell12)=
    ok (some ⟨⟨710869521#u32,1285305346#u32⟩,⟨356027171#u32,2129461334#u32⟩⟩) :=
  JFr_EncodedCell.parser cell12 limbs12 encoded12
#print axioms encoded12
#print axioms parser12
def cell13 : Array U8 16#usize := ⟨[245#u8,238#u8,197#u8,14#u8,62#u8,130#u8,203#u8,108#u8,99#u8,29#u8,231#u8,89#u8,76#u8,214#u8,227#u8,104#u8],by rfl⟩
def limbs13 : QM31Limbs := ![⟨247852789,by change 247852789<2147483647;omega⟩,⟨1825276478,by change 1825276478<2147483647;omega⟩,⟨1508318563,by change 1508318563<2147483647;omega⟩,⟨1759761996,by change 1759761996<2147483647;omega⟩]
theorem rawCell13 : (raw.drop 208).take 16=cell13.val := by
  simp only [raw,JFz_Scan52.data,JFz_Scan52.j00,JFz_Scan52.j01,JFz_Scan52.j02,JFz_Scan52.j03,JFz_Scan52.j04,JFz_Scan52.j05,JFz_Scan52.j06,JFz_Scan52.j07,JFz_Scan52.j08,JFz_Scan52.j09,JFz_Scan52.j10,JFz_Scan52.j11,JFz_Scan52.j12,JFz_Scan52.b00_length,JFz_Scan52.b01_length,JFz_Scan52.b02_length,JFz_Scan52.b03_length,JFz_Scan52.b04_length,JFz_Scan52.b05_length,JFz_Scan52.b06_length,JFz_Scan52.b07_length,JFz_Scan52.b08_length,JFz_Scan52.b09_length,JFz_Scan52.b10_length,JFz_Scan52.b11_length,JFz_Scan52.b12_length,JFz_Scan52.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell13
theorem encoded13 : CandidateParserByteOrder.arrayBytes16 cell13=encodeQM31LE limbs13 := by
  funext i
  fin_cases i <;> rfl
theorem parser13 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell13)=
    ok (some ⟨⟨247852789#u32,1825276478#u32⟩,⟨1508318563#u32,1759761996#u32⟩⟩) :=
  JFr_EncodedCell.parser cell13 limbs13 encoded13
#print axioms encoded13
#print axioms parser13
def cell14 : Array U8 16#usize := ⟨[176#u8,106#u8,176#u8,71#u8,34#u8,1#u8,137#u8,27#u8,119#u8,227#u8,156#u8,115#u8,101#u8,95#u8,178#u8,61#u8],by rfl⟩
def limbs14 : QM31Limbs := ![⟨1202743984,by change 1202743984<2147483647;omega⟩,⟨461963554,by change 461963554<2147483647;omega⟩,⟨1939661687,by change 1939661687<2147483647;omega⟩,⟨1035100005,by change 1035100005<2147483647;omega⟩]
theorem rawCell14 : (raw.drop 224).take 16=cell14.val := by
  simp only [raw,JFz_Scan52.data,JFz_Scan52.j00,JFz_Scan52.j01,JFz_Scan52.j02,JFz_Scan52.j03,JFz_Scan52.j04,JFz_Scan52.j05,JFz_Scan52.j06,JFz_Scan52.j07,JFz_Scan52.j08,JFz_Scan52.j09,JFz_Scan52.j10,JFz_Scan52.j11,JFz_Scan52.j12,JFz_Scan52.b00_length,JFz_Scan52.b01_length,JFz_Scan52.b02_length,JFz_Scan52.b03_length,JFz_Scan52.b04_length,JFz_Scan52.b05_length,JFz_Scan52.b06_length,JFz_Scan52.b07_length,JFz_Scan52.b08_length,JFz_Scan52.b09_length,JFz_Scan52.b10_length,JFz_Scan52.b11_length,JFz_Scan52.b12_length,JFz_Scan52.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell14
theorem encoded14 : CandidateParserByteOrder.arrayBytes16 cell14=encodeQM31LE limbs14 := by
  funext i
  fin_cases i <;> rfl
theorem parser14 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell14)=
    ok (some ⟨⟨1202743984#u32,461963554#u32⟩,⟨1939661687#u32,1035100005#u32⟩⟩) :=
  JFr_EncodedCell.parser cell14 limbs14 encoded14
#print axioms encoded14
#print axioms parser14
def cell15 : Array U8 16#usize := ⟨[175#u8,189#u8,87#u8,111#u8,88#u8,10#u8,152#u8,13#u8,26#u8,45#u8,118#u8,105#u8,3#u8,156#u8,71#u8,58#u8],by rfl⟩
def limbs15 : QM31Limbs := ![⟨1868021167,by change 1868021167<2147483647;omega⟩,⟨228067928,by change 228067928<2147483647;omega⟩,⟨1769352474,by change 1769352474<2147483647;omega⟩,⟨977771523,by change 977771523<2147483647;omega⟩]
theorem rawCell15 : (raw.drop 240).take 16=cell15.val := by
  simp only [raw,JFz_Scan52.data,JFz_Scan52.j00,JFz_Scan52.j01,JFz_Scan52.j02,JFz_Scan52.j03,JFz_Scan52.j04,JFz_Scan52.j05,JFz_Scan52.j06,JFz_Scan52.j07,JFz_Scan52.j08,JFz_Scan52.j09,JFz_Scan52.j10,JFz_Scan52.j11,JFz_Scan52.j12,JFz_Scan52.b00_length,JFz_Scan52.b01_length,JFz_Scan52.b02_length,JFz_Scan52.b03_length,JFz_Scan52.b04_length,JFz_Scan52.b05_length,JFz_Scan52.b06_length,JFz_Scan52.b07_length,JFz_Scan52.b08_length,JFz_Scan52.b09_length,JFz_Scan52.b10_length,JFz_Scan52.b11_length,JFz_Scan52.b12_length,JFz_Scan52.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell15
theorem encoded15 : CandidateParserByteOrder.arrayBytes16 cell15=encodeQM31LE limbs15 := by
  funext i
  fin_cases i <;> rfl
theorem parser15 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell15)=
    ok (some ⟨⟨1868021167#u32,228067928#u32⟩,⟨1769352474#u32,977771523#u32⟩⟩) :=
  JFr_EncodedCell.parser cell15 limbs15 encoded15
#print axioms encoded15
#print axioms parser15
def cell16 : Array U8 16#usize := ⟨[91#u8,105#u8,58#u8,118#u8,224#u8,236#u8,68#u8,50#u8,185#u8,246#u8,63#u8,26#u8,91#u8,108#u8,107#u8,103#u8],by rfl⟩
def limbs16 : QM31Limbs := ![⟨1983539547,by change 1983539547<2147483647;omega⟩,⟨843377888,by change 843377888<2147483647;omega⟩,⟨440399545,by change 440399545<2147483647;omega⟩,⟨1735093339,by change 1735093339<2147483647;omega⟩]
theorem rawCell16 : (raw.drop 256).take 16=cell16.val := by
  simp only [raw,JFz_Scan52.data,JFz_Scan52.j00,JFz_Scan52.j01,JFz_Scan52.j02,JFz_Scan52.j03,JFz_Scan52.j04,JFz_Scan52.j05,JFz_Scan52.j06,JFz_Scan52.j07,JFz_Scan52.j08,JFz_Scan52.j09,JFz_Scan52.j10,JFz_Scan52.j11,JFz_Scan52.j12,JFz_Scan52.b00_length,JFz_Scan52.b01_length,JFz_Scan52.b02_length,JFz_Scan52.b03_length,JFz_Scan52.b04_length,JFz_Scan52.b05_length,JFz_Scan52.b06_length,JFz_Scan52.b07_length,JFz_Scan52.b08_length,JFz_Scan52.b09_length,JFz_Scan52.b10_length,JFz_Scan52.b11_length,JFz_Scan52.b12_length,JFz_Scan52.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell16
theorem encoded16 : CandidateParserByteOrder.arrayBytes16 cell16=encodeQM31LE limbs16 := by
  funext i
  fin_cases i <;> rfl
theorem parser16 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell16)=
    ok (some ⟨⟨1983539547#u32,843377888#u32⟩,⟨440399545#u32,1735093339#u32⟩⟩) :=
  JFr_EncodedCell.parser cell16 limbs16 encoded16
#print axioms encoded16
#print axioms parser16
def cell17 : Array U8 16#usize := ⟨[100#u8,251#u8,82#u8,23#u8,219#u8,75#u8,77#u8,106#u8,65#u8,167#u8,135#u8,22#u8,70#u8,118#u8,172#u8,70#u8],by rfl⟩
def limbs17 : QM31Limbs := ![⟨391314276,by change 391314276<2147483647;omega⟩,⟨1783450587,by change 1783450587<2147483647;omega⟩,⟨377988929,by change 377988929<2147483647;omega⟩,⟨1185707590,by change 1185707590<2147483647;omega⟩]
theorem rawCell17 : (raw.drop 272).take 16=cell17.val := by
  simp only [raw,JFz_Scan52.data,JFz_Scan52.j00,JFz_Scan52.j01,JFz_Scan52.j02,JFz_Scan52.j03,JFz_Scan52.j04,JFz_Scan52.j05,JFz_Scan52.j06,JFz_Scan52.j07,JFz_Scan52.j08,JFz_Scan52.j09,JFz_Scan52.j10,JFz_Scan52.j11,JFz_Scan52.j12,JFz_Scan52.b00_length,JFz_Scan52.b01_length,JFz_Scan52.b02_length,JFz_Scan52.b03_length,JFz_Scan52.b04_length,JFz_Scan52.b05_length,JFz_Scan52.b06_length,JFz_Scan52.b07_length,JFz_Scan52.b08_length,JFz_Scan52.b09_length,JFz_Scan52.b10_length,JFz_Scan52.b11_length,JFz_Scan52.b12_length,JFz_Scan52.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell17
theorem encoded17 : CandidateParserByteOrder.arrayBytes16 cell17=encodeQM31LE limbs17 := by
  funext i
  fin_cases i <;> rfl
theorem parser17 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell17)=
    ok (some ⟨⟨391314276#u32,1783450587#u32⟩,⟨377988929#u32,1185707590#u32⟩⟩) :=
  JFr_EncodedCell.parser cell17 limbs17 encoded17
#print axioms encoded17
#print axioms parser17
def cell18 : Array U8 16#usize := ⟨[244#u8,135#u8,89#u8,115#u8,40#u8,81#u8,0#u8,81#u8,194#u8,233#u8,236#u8,97#u8,192#u8,103#u8,91#u8,92#u8],by rfl⟩
def limbs18 : QM31Limbs := ![⟨1935247348,by change 1935247348<2147483647;omega⟩,⟨1358975272,by change 1358975272<2147483647;omega⟩,⟨1642916290,by change 1642916290<2147483647;omega⟩,⟨1549494208,by change 1549494208<2147483647;omega⟩]
theorem rawCell18 : (raw.drop 288).take 16=cell18.val := by
  simp only [raw,JFz_Scan52.data,JFz_Scan52.j00,JFz_Scan52.j01,JFz_Scan52.j02,JFz_Scan52.j03,JFz_Scan52.j04,JFz_Scan52.j05,JFz_Scan52.j06,JFz_Scan52.j07,JFz_Scan52.j08,JFz_Scan52.j09,JFz_Scan52.j10,JFz_Scan52.j11,JFz_Scan52.j12,JFz_Scan52.b00_length,JFz_Scan52.b01_length,JFz_Scan52.b02_length,JFz_Scan52.b03_length,JFz_Scan52.b04_length,JFz_Scan52.b05_length,JFz_Scan52.b06_length,JFz_Scan52.b07_length,JFz_Scan52.b08_length,JFz_Scan52.b09_length,JFz_Scan52.b10_length,JFz_Scan52.b11_length,JFz_Scan52.b12_length,JFz_Scan52.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell18
theorem encoded18 : CandidateParserByteOrder.arrayBytes16 cell18=encodeQM31LE limbs18 := by
  funext i
  fin_cases i <;> rfl
theorem parser18 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell18)=
    ok (some ⟨⟨1935247348#u32,1358975272#u32⟩,⟨1642916290#u32,1549494208#u32⟩⟩) :=
  JFr_EncodedCell.parser cell18 limbs18 encoded18
#print axioms encoded18
#print axioms parser18
def cell19 : Array U8 16#usize := ⟨[100#u8,118#u8,19#u8,98#u8,23#u8,69#u8,185#u8,5#u8,91#u8,14#u8,74#u8,62#u8,3#u8,216#u8,35#u8,3#u8],by rfl⟩
def limbs19 : QM31Limbs := ![⟨1645442660,by change 1645442660<2147483647;omega⟩,⟨96027927,by change 96027927<2147483647;omega⟩,⟨1045040731,by change 1045040731<2147483647;omega⟩,⟨52680707,by change 52680707<2147483647;omega⟩]
theorem rawCell19 : (raw.drop 304).take 16=cell19.val := by
  simp only [raw,JFz_Scan52.data,JFz_Scan52.j00,JFz_Scan52.j01,JFz_Scan52.j02,JFz_Scan52.j03,JFz_Scan52.j04,JFz_Scan52.j05,JFz_Scan52.j06,JFz_Scan52.j07,JFz_Scan52.j08,JFz_Scan52.j09,JFz_Scan52.j10,JFz_Scan52.j11,JFz_Scan52.j12,JFz_Scan52.b00_length,JFz_Scan52.b01_length,JFz_Scan52.b02_length,JFz_Scan52.b03_length,JFz_Scan52.b04_length,JFz_Scan52.b05_length,JFz_Scan52.b06_length,JFz_Scan52.b07_length,JFz_Scan52.b08_length,JFz_Scan52.b09_length,JFz_Scan52.b10_length,JFz_Scan52.b11_length,JFz_Scan52.b12_length,JFz_Scan52.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell19
theorem encoded19 : CandidateParserByteOrder.arrayBytes16 cell19=encodeQM31LE limbs19 := by
  funext i
  fin_cases i <;> rfl
theorem parser19 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell19)=
    ok (some ⟨⟨1645442660#u32,96027927#u32⟩,⟨1045040731#u32,52680707#u32⟩⟩) :=
  JFr_EncodedCell.parser cell19 limbs19 encoded19
#print axioms encoded19
#print axioms parser19
def cell20 : Array U8 16#usize := ⟨[220#u8,250#u8,15#u8,0#u8,175#u8,65#u8,54#u8,14#u8,71#u8,232#u8,43#u8,80#u8,159#u8,234#u8,57#u8,121#u8],by rfl⟩
def limbs20 : QM31Limbs := ![⟨1047260,by change 1047260<2147483647;omega⟩,⟨238436783,by change 238436783<2147483647;omega⟩,⟨1345054791,by change 1345054791<2147483647;omega⟩,⟨2033838751,by change 2033838751<2147483647;omega⟩]
theorem rawCell20 : (raw.drop 320).take 16=cell20.val := by
  simp only [raw,JFz_Scan52.data,JFz_Scan52.j00,JFz_Scan52.j01,JFz_Scan52.j02,JFz_Scan52.j03,JFz_Scan52.j04,JFz_Scan52.j05,JFz_Scan52.j06,JFz_Scan52.j07,JFz_Scan52.j08,JFz_Scan52.j09,JFz_Scan52.j10,JFz_Scan52.j11,JFz_Scan52.j12,JFz_Scan52.b00_length,JFz_Scan52.b01_length,JFz_Scan52.b02_length,JFz_Scan52.b03_length,JFz_Scan52.b04_length,JFz_Scan52.b05_length,JFz_Scan52.b06_length,JFz_Scan52.b07_length,JFz_Scan52.b08_length,JFz_Scan52.b09_length,JFz_Scan52.b10_length,JFz_Scan52.b11_length,JFz_Scan52.b12_length,JFz_Scan52.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell20
theorem encoded20 : CandidateParserByteOrder.arrayBytes16 cell20=encodeQM31LE limbs20 := by
  funext i
  fin_cases i <;> rfl
theorem parser20 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell20)=
    ok (some ⟨⟨1047260#u32,238436783#u32⟩,⟨1345054791#u32,2033838751#u32⟩⟩) :=
  JFr_EncodedCell.parser cell20 limbs20 encoded20
#print axioms encoded20
#print axioms parser20
def cell21 : Array U8 16#usize := ⟨[221#u8,181#u8,41#u8,88#u8,161#u8,34#u8,249#u8,41#u8,102#u8,49#u8,14#u8,115#u8,32#u8,15#u8,1#u8,36#u8],by rfl⟩
def limbs21 : QM31Limbs := ![⟨1479128541,by change 1479128541<2147483647;omega⟩,⟨704193185,by change 704193185<2147483647;omega⟩,⟨1930309990,by change 1930309990<2147483647;omega⟩,⟨604049184,by change 604049184<2147483647;omega⟩]
theorem rawCell21 : (raw.drop 336).take 16=cell21.val := by
  simp only [raw,JFz_Scan52.data,JFz_Scan52.j00,JFz_Scan52.j01,JFz_Scan52.j02,JFz_Scan52.j03,JFz_Scan52.j04,JFz_Scan52.j05,JFz_Scan52.j06,JFz_Scan52.j07,JFz_Scan52.j08,JFz_Scan52.j09,JFz_Scan52.j10,JFz_Scan52.j11,JFz_Scan52.j12,JFz_Scan52.b00_length,JFz_Scan52.b01_length,JFz_Scan52.b02_length,JFz_Scan52.b03_length,JFz_Scan52.b04_length,JFz_Scan52.b05_length,JFz_Scan52.b06_length,JFz_Scan52.b07_length,JFz_Scan52.b08_length,JFz_Scan52.b09_length,JFz_Scan52.b10_length,JFz_Scan52.b11_length,JFz_Scan52.b12_length,JFz_Scan52.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell21
theorem encoded21 : CandidateParserByteOrder.arrayBytes16 cell21=encodeQM31LE limbs21 := by
  funext i
  fin_cases i <;> rfl
theorem parser21 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell21)=
    ok (some ⟨⟨1479128541#u32,704193185#u32⟩,⟨1930309990#u32,604049184#u32⟩⟩) :=
  JFr_EncodedCell.parser cell21 limbs21 encoded21
#print axioms encoded21
#print axioms parser21
def cell22 : Array U8 16#usize := ⟨[226#u8,7#u8,128#u8,116#u8,142#u8,233#u8,33#u8,98#u8,111#u8,165#u8,80#u8,74#u8,169#u8,45#u8,37#u8,4#u8],by rfl⟩
def limbs22 : QM31Limbs := ![⟨1954547682,by change 1954547682<2147483647;omega⟩,⟨1646389646,by change 1646389646<2147483647;omega⟩,⟨1246799215,by change 1246799215<2147483647;omega⟩,⟨69545385,by change 69545385<2147483647;omega⟩]
theorem rawCell22 : (raw.drop 352).take 16=cell22.val := by
  simp only [raw,JFz_Scan52.data,JFz_Scan52.j00,JFz_Scan52.j01,JFz_Scan52.j02,JFz_Scan52.j03,JFz_Scan52.j04,JFz_Scan52.j05,JFz_Scan52.j06,JFz_Scan52.j07,JFz_Scan52.j08,JFz_Scan52.j09,JFz_Scan52.j10,JFz_Scan52.j11,JFz_Scan52.j12,JFz_Scan52.b00_length,JFz_Scan52.b01_length,JFz_Scan52.b02_length,JFz_Scan52.b03_length,JFz_Scan52.b04_length,JFz_Scan52.b05_length,JFz_Scan52.b06_length,JFz_Scan52.b07_length,JFz_Scan52.b08_length,JFz_Scan52.b09_length,JFz_Scan52.b10_length,JFz_Scan52.b11_length,JFz_Scan52.b12_length,JFz_Scan52.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell22
theorem encoded22 : CandidateParserByteOrder.arrayBytes16 cell22=encodeQM31LE limbs22 := by
  funext i
  fin_cases i <;> rfl
theorem parser22 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell22)=
    ok (some ⟨⟨1954547682#u32,1646389646#u32⟩,⟨1246799215#u32,69545385#u32⟩⟩) :=
  JFr_EncodedCell.parser cell22 limbs22 encoded22
#print axioms encoded22
#print axioms parser22
def cell23 : Array U8 16#usize := ⟨[148#u8,239#u8,14#u8,3#u8,249#u8,145#u8,130#u8,41#u8,239#u8,91#u8,145#u8,82#u8,228#u8,125#u8,252#u8,25#u8],by rfl⟩
def limbs23 : QM31Limbs := ![⟨51310484,by change 51310484<2147483647;omega⟩,⟨696422905,by change 696422905<2147483647;omega⟩,⟨1385257967,by change 1385257967<2147483647;omega⟩,⟨435977700,by change 435977700<2147483647;omega⟩]
theorem rawCell23 : (raw.drop 368).take 16=cell23.val := by
  simp only [raw,JFz_Scan52.data,JFz_Scan52.j00,JFz_Scan52.j01,JFz_Scan52.j02,JFz_Scan52.j03,JFz_Scan52.j04,JFz_Scan52.j05,JFz_Scan52.j06,JFz_Scan52.j07,JFz_Scan52.j08,JFz_Scan52.j09,JFz_Scan52.j10,JFz_Scan52.j11,JFz_Scan52.j12,JFz_Scan52.b00_length,JFz_Scan52.b01_length,JFz_Scan52.b02_length,JFz_Scan52.b03_length,JFz_Scan52.b04_length,JFz_Scan52.b05_length,JFz_Scan52.b06_length,JFz_Scan52.b07_length,JFz_Scan52.b08_length,JFz_Scan52.b09_length,JFz_Scan52.b10_length,JFz_Scan52.b11_length,JFz_Scan52.b12_length,JFz_Scan52.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell23
theorem encoded23 : CandidateParserByteOrder.arrayBytes16 cell23=encodeQM31LE limbs23 := by
  funext i
  fin_cases i <;> rfl
theorem parser23 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell23)=
    ok (some ⟨⟨51310484#u32,696422905#u32⟩,⟨1385257967#u32,435977700#u32⟩⟩) :=
  JFr_EncodedCell.parser cell23 limbs23 encoded23
#print axioms encoded23
#print axioms parser23
def cell24 : Array U8 16#usize := ⟨[197#u8,87#u8,162#u8,41#u8,126#u8,103#u8,120#u8,111#u8,123#u8,237#u8,71#u8,115#u8,102#u8,122#u8,103#u8,47#u8],by rfl⟩
def limbs24 : QM31Limbs := ![⟨698505157,by change 698505157<2147483647;omega⟩,⟨1870161790,by change 1870161790<2147483647;omega⟩,⟨1934093691,by change 1934093691<2147483647;omega⟩,⟨795310694,by change 795310694<2147483647;omega⟩]
theorem rawCell24 : (raw.drop 384).take 16=cell24.val := by
  simp only [raw,JFz_Scan52.data,JFz_Scan52.j00,JFz_Scan52.j01,JFz_Scan52.j02,JFz_Scan52.j03,JFz_Scan52.j04,JFz_Scan52.j05,JFz_Scan52.j06,JFz_Scan52.j07,JFz_Scan52.j08,JFz_Scan52.j09,JFz_Scan52.j10,JFz_Scan52.j11,JFz_Scan52.j12,JFz_Scan52.b00_length,JFz_Scan52.b01_length,JFz_Scan52.b02_length,JFz_Scan52.b03_length,JFz_Scan52.b04_length,JFz_Scan52.b05_length,JFz_Scan52.b06_length,JFz_Scan52.b07_length,JFz_Scan52.b08_length,JFz_Scan52.b09_length,JFz_Scan52.b10_length,JFz_Scan52.b11_length,JFz_Scan52.b12_length,JFz_Scan52.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell24
theorem encoded24 : CandidateParserByteOrder.arrayBytes16 cell24=encodeQM31LE limbs24 := by
  funext i
  fin_cases i <;> rfl
theorem parser24 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell24)=
    ok (some ⟨⟨698505157#u32,1870161790#u32⟩,⟨1934093691#u32,795310694#u32⟩⟩) :=
  JFr_EncodedCell.parser cell24 limbs24 encoded24
#print axioms encoded24
#print axioms parser24
def cell25 : Array U8 16#usize := ⟨[137#u8,84#u8,242#u8,44#u8,219#u8,46#u8,197#u8,49#u8,88#u8,56#u8,56#u8,19#u8,205#u8,195#u8,81#u8,25#u8],by rfl⟩
def limbs25 : QM31Limbs := ![⟨754078857,by change 754078857<2147483647;omega⟩,⟨835006171,by change 835006171<2147483647;omega⟩,⟨322451544,by change 322451544<2147483647;omega⟩,⟨424788941,by change 424788941<2147483647;omega⟩]
theorem rawCell25 : (raw.drop 400).take 16=cell25.val := by
  simp only [raw,JFz_Scan52.data,JFz_Scan52.j00,JFz_Scan52.j01,JFz_Scan52.j02,JFz_Scan52.j03,JFz_Scan52.j04,JFz_Scan52.j05,JFz_Scan52.j06,JFz_Scan52.j07,JFz_Scan52.j08,JFz_Scan52.j09,JFz_Scan52.j10,JFz_Scan52.j11,JFz_Scan52.j12,JFz_Scan52.b00_length,JFz_Scan52.b01_length,JFz_Scan52.b02_length,JFz_Scan52.b03_length,JFz_Scan52.b04_length,JFz_Scan52.b05_length,JFz_Scan52.b06_length,JFz_Scan52.b07_length,JFz_Scan52.b08_length,JFz_Scan52.b09_length,JFz_Scan52.b10_length,JFz_Scan52.b11_length,JFz_Scan52.b12_length,JFz_Scan52.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell25
theorem encoded25 : CandidateParserByteOrder.arrayBytes16 cell25=encodeQM31LE limbs25 := by
  funext i
  fin_cases i <;> rfl
theorem parser25 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell25)=
    ok (some ⟨⟨754078857#u32,835006171#u32⟩,⟨322451544#u32,424788941#u32⟩⟩) :=
  JFr_EncodedCell.parser cell25 limbs25 encoded25
#print axioms encoded25
#print axioms parser25
def cell26 : Array U8 16#usize := ⟨[127#u8,38#u8,192#u8,114#u8,153#u8,205#u8,72#u8,123#u8,1#u8,49#u8,190#u8,100#u8,42#u8,105#u8,32#u8,103#u8],by rfl⟩
def limbs26 : QM31Limbs := ![⟨1925195391,by change 1925195391<2147483647;omega⟩,⟨2068368793,by change 2068368793<2147483647;omega⟩,⟨1690185985,by change 1690185985<2147483647;omega⟩,⟨1730177322,by change 1730177322<2147483647;omega⟩]
theorem rawCell26 : (raw.drop 416).take 16=cell26.val := by
  simp only [raw,JFz_Scan52.data,JFz_Scan52.j00,JFz_Scan52.j01,JFz_Scan52.j02,JFz_Scan52.j03,JFz_Scan52.j04,JFz_Scan52.j05,JFz_Scan52.j06,JFz_Scan52.j07,JFz_Scan52.j08,JFz_Scan52.j09,JFz_Scan52.j10,JFz_Scan52.j11,JFz_Scan52.j12,JFz_Scan52.b00_length,JFz_Scan52.b01_length,JFz_Scan52.b02_length,JFz_Scan52.b03_length,JFz_Scan52.b04_length,JFz_Scan52.b05_length,JFz_Scan52.b06_length,JFz_Scan52.b07_length,JFz_Scan52.b08_length,JFz_Scan52.b09_length,JFz_Scan52.b10_length,JFz_Scan52.b11_length,JFz_Scan52.b12_length,JFz_Scan52.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell26
theorem encoded26 : CandidateParserByteOrder.arrayBytes16 cell26=encodeQM31LE limbs26 := by
  funext i
  fin_cases i <;> rfl
theorem parser26 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell26)=
    ok (some ⟨⟨1925195391#u32,2068368793#u32⟩,⟨1690185985#u32,1730177322#u32⟩⟩) :=
  JFr_EncodedCell.parser cell26 limbs26 encoded26
#print axioms encoded26
#print axioms parser26
def cell27 : Array U8 16#usize := ⟨[68#u8,181#u8,14#u8,61#u8,140#u8,190#u8,148#u8,28#u8,220#u8,20#u8,100#u8,39#u8,33#u8,224#u8,159#u8,41#u8],by rfl⟩
def limbs27 : QM31Limbs := ![⟨1024374084,by change 1024374084<2147483647;omega⟩,⟨479510156,by change 479510156<2147483647;omega⟩,⟨660870364,by change 660870364<2147483647;omega⟩,⟨698343457,by change 698343457<2147483647;omega⟩]
theorem rawCell27 : (raw.drop 432).take 16=cell27.val := by
  simp only [raw,JFz_Scan52.data,JFz_Scan52.j00,JFz_Scan52.j01,JFz_Scan52.j02,JFz_Scan52.j03,JFz_Scan52.j04,JFz_Scan52.j05,JFz_Scan52.j06,JFz_Scan52.j07,JFz_Scan52.j08,JFz_Scan52.j09,JFz_Scan52.j10,JFz_Scan52.j11,JFz_Scan52.j12,JFz_Scan52.b00_length,JFz_Scan52.b01_length,JFz_Scan52.b02_length,JFz_Scan52.b03_length,JFz_Scan52.b04_length,JFz_Scan52.b05_length,JFz_Scan52.b06_length,JFz_Scan52.b07_length,JFz_Scan52.b08_length,JFz_Scan52.b09_length,JFz_Scan52.b10_length,JFz_Scan52.b11_length,JFz_Scan52.b12_length,JFz_Scan52.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell27
theorem encoded27 : CandidateParserByteOrder.arrayBytes16 cell27=encodeQM31LE limbs27 := by
  funext i
  fin_cases i <;> rfl
theorem parser27 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell27)=
    ok (some ⟨⟨1024374084#u32,479510156#u32⟩,⟨660870364#u32,698343457#u32⟩⟩) :=
  JFr_EncodedCell.parser cell27 limbs27 encoded27
#print axioms encoded27
#print axioms parser27
end AspisR1.JFr_Bytes04
