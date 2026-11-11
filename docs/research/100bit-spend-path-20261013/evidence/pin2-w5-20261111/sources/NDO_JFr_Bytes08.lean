import NDO_JFr_Data08
import NDO_JFr_EncodedCell
import NDO_JFz_Scan56
set_option autoImplicit false
namespace AspisR1.JFr_Bytes08
open Aeneas Aeneas.Std Result RetainedFieldByteCodec
open AspisR1PublicPreparation
open AspisS1ExtractedRoundChildren
def raw : List U8 := JFz_Scan56.data
theorem rawLength : raw.length=448 := JFz_Scan56.length
#print axioms rawLength
theorem selected : (JFx_NativeBytes.proof.val.drop 3800).take 448=raw := JFz_Scan56.selected
#print axioms selected
def cell00 : Array U8 16#usize := ⟨[245#u8,10#u8,33#u8,63#u8,138#u8,2#u8,93#u8,52#u8,29#u8,156#u8,61#u8,71#u8,222#u8,186#u8,106#u8,9#u8],by rfl⟩
def limbs00 : QM31Limbs := ![⟨1059130101,by change 1059130101<2147483647;omega⟩,⟨878510730,by change 878510730<2147483647;omega⟩,⟨1195219997,by change 1195219997<2147483647;omega⟩,⟨157989598,by change 157989598<2147483647;omega⟩]
theorem rawCell00 : (raw.drop 0).take 16=cell00.val := by
  simp only [raw,JFz_Scan56.data,JFz_Scan56.j00,JFz_Scan56.j01,JFz_Scan56.j02,JFz_Scan56.j03,JFz_Scan56.j04,JFz_Scan56.j05,JFz_Scan56.j06,JFz_Scan56.j07,JFz_Scan56.j08,JFz_Scan56.j09,JFz_Scan56.j10,JFz_Scan56.j11,JFz_Scan56.j12,JFz_Scan56.b00_length,JFz_Scan56.b01_length,JFz_Scan56.b02_length,JFz_Scan56.b03_length,JFz_Scan56.b04_length,JFz_Scan56.b05_length,JFz_Scan56.b06_length,JFz_Scan56.b07_length,JFz_Scan56.b08_length,JFz_Scan56.b09_length,JFz_Scan56.b10_length,JFz_Scan56.b11_length,JFz_Scan56.b12_length,JFz_Scan56.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell00
theorem encoded00 : CandidateParserByteOrder.arrayBytes16 cell00=encodeQM31LE limbs00 := by
  funext i
  fin_cases i <;> rfl
theorem parser00 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell00)=
    ok (some ⟨⟨1059130101#u32,878510730#u32⟩,⟨1195219997#u32,157989598#u32⟩⟩) :=
  JFr_EncodedCell.parser cell00 limbs00 encoded00
#print axioms encoded00
#print axioms parser00
def cell01 : Array U8 16#usize := ⟨[135#u8,178#u8,21#u8,123#u8,136#u8,185#u8,135#u8,105#u8,119#u8,108#u8,242#u8,112#u8,29#u8,193#u8,220#u8,82#u8],by rfl⟩
def limbs01 : QM31Limbs := ![⟨2065019527,by change 2065019527<2147483647;omega⟩,⟨1770502536,by change 1770502536<2147483647;omega⟩,⟨1894935671,by change 1894935671<2147483647;omega⟩,⟨1390199069,by change 1390199069<2147483647;omega⟩]
theorem rawCell01 : (raw.drop 16).take 16=cell01.val := by
  simp only [raw,JFz_Scan56.data,JFz_Scan56.j00,JFz_Scan56.j01,JFz_Scan56.j02,JFz_Scan56.j03,JFz_Scan56.j04,JFz_Scan56.j05,JFz_Scan56.j06,JFz_Scan56.j07,JFz_Scan56.j08,JFz_Scan56.j09,JFz_Scan56.j10,JFz_Scan56.j11,JFz_Scan56.j12,JFz_Scan56.b00_length,JFz_Scan56.b01_length,JFz_Scan56.b02_length,JFz_Scan56.b03_length,JFz_Scan56.b04_length,JFz_Scan56.b05_length,JFz_Scan56.b06_length,JFz_Scan56.b07_length,JFz_Scan56.b08_length,JFz_Scan56.b09_length,JFz_Scan56.b10_length,JFz_Scan56.b11_length,JFz_Scan56.b12_length,JFz_Scan56.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell01
theorem encoded01 : CandidateParserByteOrder.arrayBytes16 cell01=encodeQM31LE limbs01 := by
  funext i
  fin_cases i <;> rfl
theorem parser01 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell01)=
    ok (some ⟨⟨2065019527#u32,1770502536#u32⟩,⟨1894935671#u32,1390199069#u32⟩⟩) :=
  JFr_EncodedCell.parser cell01 limbs01 encoded01
#print axioms encoded01
#print axioms parser01
def cell02 : Array U8 16#usize := ⟨[158#u8,187#u8,150#u8,66#u8,22#u8,42#u8,149#u8,119#u8,53#u8,36#u8,105#u8,103#u8,109#u8,16#u8,92#u8,36#u8],by rfl⟩
def limbs02 : QM31Limbs := ![⟨1117174686,by change 1117174686<2147483647;omega⟩,⟨2006264342,by change 2006264342<2147483647;omega⟩,⟨1734943797,by change 1734943797<2147483647;omega⟩,⟨610013293,by change 610013293<2147483647;omega⟩]
theorem rawCell02 : (raw.drop 32).take 16=cell02.val := by
  simp only [raw,JFz_Scan56.data,JFz_Scan56.j00,JFz_Scan56.j01,JFz_Scan56.j02,JFz_Scan56.j03,JFz_Scan56.j04,JFz_Scan56.j05,JFz_Scan56.j06,JFz_Scan56.j07,JFz_Scan56.j08,JFz_Scan56.j09,JFz_Scan56.j10,JFz_Scan56.j11,JFz_Scan56.j12,JFz_Scan56.b00_length,JFz_Scan56.b01_length,JFz_Scan56.b02_length,JFz_Scan56.b03_length,JFz_Scan56.b04_length,JFz_Scan56.b05_length,JFz_Scan56.b06_length,JFz_Scan56.b07_length,JFz_Scan56.b08_length,JFz_Scan56.b09_length,JFz_Scan56.b10_length,JFz_Scan56.b11_length,JFz_Scan56.b12_length,JFz_Scan56.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell02
theorem encoded02 : CandidateParserByteOrder.arrayBytes16 cell02=encodeQM31LE limbs02 := by
  funext i
  fin_cases i <;> rfl
theorem parser02 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell02)=
    ok (some ⟨⟨1117174686#u32,2006264342#u32⟩,⟨1734943797#u32,610013293#u32⟩⟩) :=
  JFr_EncodedCell.parser cell02 limbs02 encoded02
#print axioms encoded02
#print axioms parser02
def cell03 : Array U8 16#usize := ⟨[142#u8,105#u8,170#u8,42#u8,111#u8,87#u8,89#u8,114#u8,22#u8,97#u8,76#u8,101#u8,142#u8,255#u8,220#u8,81#u8],by rfl⟩
def limbs03 : QM31Limbs := ![⟨715811214,by change 715811214<2147483647;omega⟩,⟨1918457711,by change 1918457711<2147483647;omega⟩,⟨1699504406,by change 1699504406<2147483647;omega⟩,⟨1373437838,by change 1373437838<2147483647;omega⟩]
theorem rawCell03 : (raw.drop 48).take 16=cell03.val := by
  simp only [raw,JFz_Scan56.data,JFz_Scan56.j00,JFz_Scan56.j01,JFz_Scan56.j02,JFz_Scan56.j03,JFz_Scan56.j04,JFz_Scan56.j05,JFz_Scan56.j06,JFz_Scan56.j07,JFz_Scan56.j08,JFz_Scan56.j09,JFz_Scan56.j10,JFz_Scan56.j11,JFz_Scan56.j12,JFz_Scan56.b00_length,JFz_Scan56.b01_length,JFz_Scan56.b02_length,JFz_Scan56.b03_length,JFz_Scan56.b04_length,JFz_Scan56.b05_length,JFz_Scan56.b06_length,JFz_Scan56.b07_length,JFz_Scan56.b08_length,JFz_Scan56.b09_length,JFz_Scan56.b10_length,JFz_Scan56.b11_length,JFz_Scan56.b12_length,JFz_Scan56.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell03
theorem encoded03 : CandidateParserByteOrder.arrayBytes16 cell03=encodeQM31LE limbs03 := by
  funext i
  fin_cases i <;> rfl
theorem parser03 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell03)=
    ok (some ⟨⟨715811214#u32,1918457711#u32⟩,⟨1699504406#u32,1373437838#u32⟩⟩) :=
  JFr_EncodedCell.parser cell03 limbs03 encoded03
#print axioms encoded03
#print axioms parser03
def cell04 : Array U8 16#usize := ⟨[193#u8,70#u8,231#u8,61#u8,117#u8,163#u8,163#u8,55#u8,47#u8,114#u8,86#u8,103#u8,53#u8,45#u8,155#u8,72#u8],by rfl⟩
def limbs04 : QM31Limbs := ![⟨1038567105,by change 1038567105<2147483647;omega⟩,⟨933471093,by change 933471093<2147483647;omega⟩,⟨1733718575,by change 1733718575<2147483647;omega⟩,⟨1218129205,by change 1218129205<2147483647;omega⟩]
theorem rawCell04 : (raw.drop 64).take 16=cell04.val := by
  simp only [raw,JFz_Scan56.data,JFz_Scan56.j00,JFz_Scan56.j01,JFz_Scan56.j02,JFz_Scan56.j03,JFz_Scan56.j04,JFz_Scan56.j05,JFz_Scan56.j06,JFz_Scan56.j07,JFz_Scan56.j08,JFz_Scan56.j09,JFz_Scan56.j10,JFz_Scan56.j11,JFz_Scan56.j12,JFz_Scan56.b00_length,JFz_Scan56.b01_length,JFz_Scan56.b02_length,JFz_Scan56.b03_length,JFz_Scan56.b04_length,JFz_Scan56.b05_length,JFz_Scan56.b06_length,JFz_Scan56.b07_length,JFz_Scan56.b08_length,JFz_Scan56.b09_length,JFz_Scan56.b10_length,JFz_Scan56.b11_length,JFz_Scan56.b12_length,JFz_Scan56.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell04
theorem encoded04 : CandidateParserByteOrder.arrayBytes16 cell04=encodeQM31LE limbs04 := by
  funext i
  fin_cases i <;> rfl
theorem parser04 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell04)=
    ok (some ⟨⟨1038567105#u32,933471093#u32⟩,⟨1733718575#u32,1218129205#u32⟩⟩) :=
  JFr_EncodedCell.parser cell04 limbs04 encoded04
#print axioms encoded04
#print axioms parser04
def cell05 : Array U8 16#usize := ⟨[145#u8,172#u8,12#u8,79#u8,70#u8,166#u8,140#u8,22#u8,174#u8,114#u8,191#u8,43#u8,114#u8,197#u8,22#u8,65#u8],by rfl⟩
def limbs05 : QM31Limbs := ![⟨1326230673,by change 1326230673<2147483647;omega⟩,⟨378316358,by change 378316358<2147483647;omega⟩,⟨733967022,by change 733967022<2147483647;omega⟩,⟨1092011378,by change 1092011378<2147483647;omega⟩]
theorem rawCell05 : (raw.drop 80).take 16=cell05.val := by
  simp only [raw,JFz_Scan56.data,JFz_Scan56.j00,JFz_Scan56.j01,JFz_Scan56.j02,JFz_Scan56.j03,JFz_Scan56.j04,JFz_Scan56.j05,JFz_Scan56.j06,JFz_Scan56.j07,JFz_Scan56.j08,JFz_Scan56.j09,JFz_Scan56.j10,JFz_Scan56.j11,JFz_Scan56.j12,JFz_Scan56.b00_length,JFz_Scan56.b01_length,JFz_Scan56.b02_length,JFz_Scan56.b03_length,JFz_Scan56.b04_length,JFz_Scan56.b05_length,JFz_Scan56.b06_length,JFz_Scan56.b07_length,JFz_Scan56.b08_length,JFz_Scan56.b09_length,JFz_Scan56.b10_length,JFz_Scan56.b11_length,JFz_Scan56.b12_length,JFz_Scan56.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell05
theorem encoded05 : CandidateParserByteOrder.arrayBytes16 cell05=encodeQM31LE limbs05 := by
  funext i
  fin_cases i <;> rfl
theorem parser05 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell05)=
    ok (some ⟨⟨1326230673#u32,378316358#u32⟩,⟨733967022#u32,1092011378#u32⟩⟩) :=
  JFr_EncodedCell.parser cell05 limbs05 encoded05
#print axioms encoded05
#print axioms parser05
def cell06 : Array U8 16#usize := ⟨[15#u8,118#u8,115#u8,45#u8,23#u8,41#u8,153#u8,41#u8,244#u8,77#u8,233#u8,79#u8,156#u8,146#u8,180#u8,51#u8],by rfl⟩
def limbs06 : QM31Limbs := ![⟨762541583,by change 762541583<2147483647;omega⟩,⟨697903383,by change 697903383<2147483647;omega⟩,⟨1340689908,by change 1340689908<2147483647;omega⟩,⟨867472028,by change 867472028<2147483647;omega⟩]
theorem rawCell06 : (raw.drop 96).take 16=cell06.val := by
  simp only [raw,JFz_Scan56.data,JFz_Scan56.j00,JFz_Scan56.j01,JFz_Scan56.j02,JFz_Scan56.j03,JFz_Scan56.j04,JFz_Scan56.j05,JFz_Scan56.j06,JFz_Scan56.j07,JFz_Scan56.j08,JFz_Scan56.j09,JFz_Scan56.j10,JFz_Scan56.j11,JFz_Scan56.j12,JFz_Scan56.b00_length,JFz_Scan56.b01_length,JFz_Scan56.b02_length,JFz_Scan56.b03_length,JFz_Scan56.b04_length,JFz_Scan56.b05_length,JFz_Scan56.b06_length,JFz_Scan56.b07_length,JFz_Scan56.b08_length,JFz_Scan56.b09_length,JFz_Scan56.b10_length,JFz_Scan56.b11_length,JFz_Scan56.b12_length,JFz_Scan56.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell06
theorem encoded06 : CandidateParserByteOrder.arrayBytes16 cell06=encodeQM31LE limbs06 := by
  funext i
  fin_cases i <;> rfl
theorem parser06 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell06)=
    ok (some ⟨⟨762541583#u32,697903383#u32⟩,⟨1340689908#u32,867472028#u32⟩⟩) :=
  JFr_EncodedCell.parser cell06 limbs06 encoded06
#print axioms encoded06
#print axioms parser06
def cell07 : Array U8 16#usize := ⟨[212#u8,93#u8,44#u8,114#u8,133#u8,34#u8,92#u8,46#u8,186#u8,93#u8,157#u8,56#u8,128#u8,147#u8,24#u8,72#u8],by rfl⟩
def limbs07 : QM31Limbs := ![⟨1915510228,by change 1915510228<2147483647;omega⟩,⟨777790085,by change 777790085<2147483647;omega⟩,⟨949837242,by change 949837242<2147483647;omega⟩,⟨1209570176,by change 1209570176<2147483647;omega⟩]
theorem rawCell07 : (raw.drop 112).take 16=cell07.val := by
  simp only [raw,JFz_Scan56.data,JFz_Scan56.j00,JFz_Scan56.j01,JFz_Scan56.j02,JFz_Scan56.j03,JFz_Scan56.j04,JFz_Scan56.j05,JFz_Scan56.j06,JFz_Scan56.j07,JFz_Scan56.j08,JFz_Scan56.j09,JFz_Scan56.j10,JFz_Scan56.j11,JFz_Scan56.j12,JFz_Scan56.b00_length,JFz_Scan56.b01_length,JFz_Scan56.b02_length,JFz_Scan56.b03_length,JFz_Scan56.b04_length,JFz_Scan56.b05_length,JFz_Scan56.b06_length,JFz_Scan56.b07_length,JFz_Scan56.b08_length,JFz_Scan56.b09_length,JFz_Scan56.b10_length,JFz_Scan56.b11_length,JFz_Scan56.b12_length,JFz_Scan56.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell07
theorem encoded07 : CandidateParserByteOrder.arrayBytes16 cell07=encodeQM31LE limbs07 := by
  funext i
  fin_cases i <;> rfl
theorem parser07 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell07)=
    ok (some ⟨⟨1915510228#u32,777790085#u32⟩,⟨949837242#u32,1209570176#u32⟩⟩) :=
  JFr_EncodedCell.parser cell07 limbs07 encoded07
#print axioms encoded07
#print axioms parser07
def cell08 : Array U8 16#usize := ⟨[109#u8,225#u8,69#u8,39#u8,29#u8,214#u8,120#u8,65#u8,163#u8,75#u8,17#u8,38#u8,163#u8,3#u8,161#u8,107#u8],by rfl⟩
def limbs08 : QM31Limbs := ![⟨658891117,by change 658891117<2147483647;omega⟩,⟨1098438173,by change 1098438173<2147483647;omega⟩,⟨638667683,by change 638667683<2147483647;omega⟩,⟨1805714339,by change 1805714339<2147483647;omega⟩]
theorem rawCell08 : (raw.drop 128).take 16=cell08.val := by
  simp only [raw,JFz_Scan56.data,JFz_Scan56.j00,JFz_Scan56.j01,JFz_Scan56.j02,JFz_Scan56.j03,JFz_Scan56.j04,JFz_Scan56.j05,JFz_Scan56.j06,JFz_Scan56.j07,JFz_Scan56.j08,JFz_Scan56.j09,JFz_Scan56.j10,JFz_Scan56.j11,JFz_Scan56.j12,JFz_Scan56.b00_length,JFz_Scan56.b01_length,JFz_Scan56.b02_length,JFz_Scan56.b03_length,JFz_Scan56.b04_length,JFz_Scan56.b05_length,JFz_Scan56.b06_length,JFz_Scan56.b07_length,JFz_Scan56.b08_length,JFz_Scan56.b09_length,JFz_Scan56.b10_length,JFz_Scan56.b11_length,JFz_Scan56.b12_length,JFz_Scan56.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell08
theorem encoded08 : CandidateParserByteOrder.arrayBytes16 cell08=encodeQM31LE limbs08 := by
  funext i
  fin_cases i <;> rfl
theorem parser08 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell08)=
    ok (some ⟨⟨658891117#u32,1098438173#u32⟩,⟨638667683#u32,1805714339#u32⟩⟩) :=
  JFr_EncodedCell.parser cell08 limbs08 encoded08
#print axioms encoded08
#print axioms parser08
def cell09 : Array U8 16#usize := ⟨[26#u8,142#u8,63#u8,16#u8,152#u8,249#u8,0#u8,28#u8,22#u8,49#u8,53#u8,94#u8,57#u8,195#u8,244#u8,57#u8],by rfl⟩
def limbs09 : QM31Limbs := ![⟨272600602,by change 272600602<2147483647;omega⟩,⟨469825944,by change 469825944<2147483647;omega⟩,⟨1580544278,by change 1580544278<2147483647;omega⟩,⟨972342073,by change 972342073<2147483647;omega⟩]
theorem rawCell09 : (raw.drop 144).take 16=cell09.val := by
  simp only [raw,JFz_Scan56.data,JFz_Scan56.j00,JFz_Scan56.j01,JFz_Scan56.j02,JFz_Scan56.j03,JFz_Scan56.j04,JFz_Scan56.j05,JFz_Scan56.j06,JFz_Scan56.j07,JFz_Scan56.j08,JFz_Scan56.j09,JFz_Scan56.j10,JFz_Scan56.j11,JFz_Scan56.j12,JFz_Scan56.b00_length,JFz_Scan56.b01_length,JFz_Scan56.b02_length,JFz_Scan56.b03_length,JFz_Scan56.b04_length,JFz_Scan56.b05_length,JFz_Scan56.b06_length,JFz_Scan56.b07_length,JFz_Scan56.b08_length,JFz_Scan56.b09_length,JFz_Scan56.b10_length,JFz_Scan56.b11_length,JFz_Scan56.b12_length,JFz_Scan56.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell09
theorem encoded09 : CandidateParserByteOrder.arrayBytes16 cell09=encodeQM31LE limbs09 := by
  funext i
  fin_cases i <;> rfl
theorem parser09 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell09)=
    ok (some ⟨⟨272600602#u32,469825944#u32⟩,⟨1580544278#u32,972342073#u32⟩⟩) :=
  JFr_EncodedCell.parser cell09 limbs09 encoded09
#print axioms encoded09
#print axioms parser09
def cell10 : Array U8 16#usize := ⟨[235#u8,236#u8,68#u8,116#u8,2#u8,250#u8,28#u8,28#u8,33#u8,41#u8,234#u8,16#u8,193#u8,87#u8,25#u8,122#u8],by rfl⟩
def limbs10 : QM31Limbs := ![⟨1950674155,by change 1950674155<2147483647;omega⟩,⟨471661058,by change 471661058<2147483647;omega⟩,⟨283781409,by change 283781409<2147483647;omega⟩,⟨2048481217,by change 2048481217<2147483647;omega⟩]
theorem rawCell10 : (raw.drop 160).take 16=cell10.val := by
  simp only [raw,JFz_Scan56.data,JFz_Scan56.j00,JFz_Scan56.j01,JFz_Scan56.j02,JFz_Scan56.j03,JFz_Scan56.j04,JFz_Scan56.j05,JFz_Scan56.j06,JFz_Scan56.j07,JFz_Scan56.j08,JFz_Scan56.j09,JFz_Scan56.j10,JFz_Scan56.j11,JFz_Scan56.j12,JFz_Scan56.b00_length,JFz_Scan56.b01_length,JFz_Scan56.b02_length,JFz_Scan56.b03_length,JFz_Scan56.b04_length,JFz_Scan56.b05_length,JFz_Scan56.b06_length,JFz_Scan56.b07_length,JFz_Scan56.b08_length,JFz_Scan56.b09_length,JFz_Scan56.b10_length,JFz_Scan56.b11_length,JFz_Scan56.b12_length,JFz_Scan56.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell10
theorem encoded10 : CandidateParserByteOrder.arrayBytes16 cell10=encodeQM31LE limbs10 := by
  funext i
  fin_cases i <;> rfl
theorem parser10 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell10)=
    ok (some ⟨⟨1950674155#u32,471661058#u32⟩,⟨283781409#u32,2048481217#u32⟩⟩) :=
  JFr_EncodedCell.parser cell10 limbs10 encoded10
#print axioms encoded10
#print axioms parser10
def cell11 : Array U8 16#usize := ⟨[122#u8,64#u8,238#u8,34#u8,184#u8,94#u8,248#u8,22#u8,153#u8,144#u8,160#u8,107#u8,47#u8,235#u8,75#u8,74#u8],by rfl⟩
def limbs11 : QM31Limbs := ![⟨586039418,by change 586039418<2147483647;omega⟩,⟨385375928,by change 385375928<2147483647;omega⟩,⟨1805684889,by change 1805684889<2147483647;omega⟩,⟨1246489391,by change 1246489391<2147483647;omega⟩]
theorem rawCell11 : (raw.drop 176).take 16=cell11.val := by
  simp only [raw,JFz_Scan56.data,JFz_Scan56.j00,JFz_Scan56.j01,JFz_Scan56.j02,JFz_Scan56.j03,JFz_Scan56.j04,JFz_Scan56.j05,JFz_Scan56.j06,JFz_Scan56.j07,JFz_Scan56.j08,JFz_Scan56.j09,JFz_Scan56.j10,JFz_Scan56.j11,JFz_Scan56.j12,JFz_Scan56.b00_length,JFz_Scan56.b01_length,JFz_Scan56.b02_length,JFz_Scan56.b03_length,JFz_Scan56.b04_length,JFz_Scan56.b05_length,JFz_Scan56.b06_length,JFz_Scan56.b07_length,JFz_Scan56.b08_length,JFz_Scan56.b09_length,JFz_Scan56.b10_length,JFz_Scan56.b11_length,JFz_Scan56.b12_length,JFz_Scan56.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell11
theorem encoded11 : CandidateParserByteOrder.arrayBytes16 cell11=encodeQM31LE limbs11 := by
  funext i
  fin_cases i <;> rfl
theorem parser11 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell11)=
    ok (some ⟨⟨586039418#u32,385375928#u32⟩,⟨1805684889#u32,1246489391#u32⟩⟩) :=
  JFr_EncodedCell.parser cell11 limbs11 encoded11
#print axioms encoded11
#print axioms parser11
def cell12 : Array U8 16#usize := ⟨[21#u8,85#u8,208#u8,78#u8,209#u8,97#u8,243#u8,108#u8,197#u8,40#u8,94#u8,59#u8,205#u8,155#u8,124#u8,9#u8],by rfl⟩
def limbs12 : QM31Limbs := ![⟨1322276117,by change 1322276117<2147483647;omega⟩,⟨1827889617,by change 1827889617<2147483647;omega⟩,⟨996026565,by change 996026565<2147483647;omega⟩,⟨159161293,by change 159161293<2147483647;omega⟩]
theorem rawCell12 : (raw.drop 192).take 16=cell12.val := by
  simp only [raw,JFz_Scan56.data,JFz_Scan56.j00,JFz_Scan56.j01,JFz_Scan56.j02,JFz_Scan56.j03,JFz_Scan56.j04,JFz_Scan56.j05,JFz_Scan56.j06,JFz_Scan56.j07,JFz_Scan56.j08,JFz_Scan56.j09,JFz_Scan56.j10,JFz_Scan56.j11,JFz_Scan56.j12,JFz_Scan56.b00_length,JFz_Scan56.b01_length,JFz_Scan56.b02_length,JFz_Scan56.b03_length,JFz_Scan56.b04_length,JFz_Scan56.b05_length,JFz_Scan56.b06_length,JFz_Scan56.b07_length,JFz_Scan56.b08_length,JFz_Scan56.b09_length,JFz_Scan56.b10_length,JFz_Scan56.b11_length,JFz_Scan56.b12_length,JFz_Scan56.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell12
theorem encoded12 : CandidateParserByteOrder.arrayBytes16 cell12=encodeQM31LE limbs12 := by
  funext i
  fin_cases i <;> rfl
theorem parser12 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell12)=
    ok (some ⟨⟨1322276117#u32,1827889617#u32⟩,⟨996026565#u32,159161293#u32⟩⟩) :=
  JFr_EncodedCell.parser cell12 limbs12 encoded12
#print axioms encoded12
#print axioms parser12
def cell13 : Array U8 16#usize := ⟨[66#u8,238#u8,107#u8,118#u8,200#u8,161#u8,234#u8,50#u8,22#u8,200#u8,47#u8,98#u8,111#u8,11#u8,21#u8,3#u8],by rfl⟩
def limbs13 : QM31Limbs := ![⟨1986784834,by change 1986784834<2147483647;omega⟩,⟨854237640,by change 854237640<2147483647;omega⟩,⟨1647298582,by change 1647298582<2147483647;omega⟩,⟨51710831,by change 51710831<2147483647;omega⟩]
theorem rawCell13 : (raw.drop 208).take 16=cell13.val := by
  simp only [raw,JFz_Scan56.data,JFz_Scan56.j00,JFz_Scan56.j01,JFz_Scan56.j02,JFz_Scan56.j03,JFz_Scan56.j04,JFz_Scan56.j05,JFz_Scan56.j06,JFz_Scan56.j07,JFz_Scan56.j08,JFz_Scan56.j09,JFz_Scan56.j10,JFz_Scan56.j11,JFz_Scan56.j12,JFz_Scan56.b00_length,JFz_Scan56.b01_length,JFz_Scan56.b02_length,JFz_Scan56.b03_length,JFz_Scan56.b04_length,JFz_Scan56.b05_length,JFz_Scan56.b06_length,JFz_Scan56.b07_length,JFz_Scan56.b08_length,JFz_Scan56.b09_length,JFz_Scan56.b10_length,JFz_Scan56.b11_length,JFz_Scan56.b12_length,JFz_Scan56.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell13
theorem encoded13 : CandidateParserByteOrder.arrayBytes16 cell13=encodeQM31LE limbs13 := by
  funext i
  fin_cases i <;> rfl
theorem parser13 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell13)=
    ok (some ⟨⟨1986784834#u32,854237640#u32⟩,⟨1647298582#u32,51710831#u32⟩⟩) :=
  JFr_EncodedCell.parser cell13 limbs13 encoded13
#print axioms encoded13
#print axioms parser13
def cell14 : Array U8 16#usize := ⟨[87#u8,241#u8,94#u8,46#u8,207#u8,246#u8,84#u8,83#u8,230#u8,209#u8,129#u8,127#u8,213#u8,150#u8,110#u8,35#u8],by rfl⟩
def limbs14 : QM31Limbs := ![⟨777974103,by change 777974103<2147483647;omega⟩,⟨1398077135,by change 1398077135<2147483647;omega⟩,⟨2139214310,by change 2139214310<2147483647;omega⟩,⟨594450133,by change 594450133<2147483647;omega⟩]
theorem rawCell14 : (raw.drop 224).take 16=cell14.val := by
  simp only [raw,JFz_Scan56.data,JFz_Scan56.j00,JFz_Scan56.j01,JFz_Scan56.j02,JFz_Scan56.j03,JFz_Scan56.j04,JFz_Scan56.j05,JFz_Scan56.j06,JFz_Scan56.j07,JFz_Scan56.j08,JFz_Scan56.j09,JFz_Scan56.j10,JFz_Scan56.j11,JFz_Scan56.j12,JFz_Scan56.b00_length,JFz_Scan56.b01_length,JFz_Scan56.b02_length,JFz_Scan56.b03_length,JFz_Scan56.b04_length,JFz_Scan56.b05_length,JFz_Scan56.b06_length,JFz_Scan56.b07_length,JFz_Scan56.b08_length,JFz_Scan56.b09_length,JFz_Scan56.b10_length,JFz_Scan56.b11_length,JFz_Scan56.b12_length,JFz_Scan56.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell14
theorem encoded14 : CandidateParserByteOrder.arrayBytes16 cell14=encodeQM31LE limbs14 := by
  funext i
  fin_cases i <;> rfl
theorem parser14 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell14)=
    ok (some ⟨⟨777974103#u32,1398077135#u32⟩,⟨2139214310#u32,594450133#u32⟩⟩) :=
  JFr_EncodedCell.parser cell14 limbs14 encoded14
#print axioms encoded14
#print axioms parser14
def cell15 : Array U8 16#usize := ⟨[43#u8,253#u8,113#u8,4#u8,103#u8,129#u8,191#u8,56#u8,168#u8,230#u8,97#u8,74#u8,78#u8,134#u8,225#u8,58#u8],by rfl⟩
def limbs15 : QM31Limbs := ![⟨74579243,by change 74579243<2147483647;omega⟩,⟨952074599,by change 952074599<2147483647;omega⟩,⟨1247930024,by change 1247930024<2147483647;omega⟩,⟨987858510,by change 987858510<2147483647;omega⟩]
theorem rawCell15 : (raw.drop 240).take 16=cell15.val := by
  simp only [raw,JFz_Scan56.data,JFz_Scan56.j00,JFz_Scan56.j01,JFz_Scan56.j02,JFz_Scan56.j03,JFz_Scan56.j04,JFz_Scan56.j05,JFz_Scan56.j06,JFz_Scan56.j07,JFz_Scan56.j08,JFz_Scan56.j09,JFz_Scan56.j10,JFz_Scan56.j11,JFz_Scan56.j12,JFz_Scan56.b00_length,JFz_Scan56.b01_length,JFz_Scan56.b02_length,JFz_Scan56.b03_length,JFz_Scan56.b04_length,JFz_Scan56.b05_length,JFz_Scan56.b06_length,JFz_Scan56.b07_length,JFz_Scan56.b08_length,JFz_Scan56.b09_length,JFz_Scan56.b10_length,JFz_Scan56.b11_length,JFz_Scan56.b12_length,JFz_Scan56.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell15
theorem encoded15 : CandidateParserByteOrder.arrayBytes16 cell15=encodeQM31LE limbs15 := by
  funext i
  fin_cases i <;> rfl
theorem parser15 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell15)=
    ok (some ⟨⟨74579243#u32,952074599#u32⟩,⟨1247930024#u32,987858510#u32⟩⟩) :=
  JFr_EncodedCell.parser cell15 limbs15 encoded15
#print axioms encoded15
#print axioms parser15
def cell16 : Array U8 16#usize := ⟨[52#u8,121#u8,76#u8,23#u8,144#u8,57#u8,187#u8,16#u8,46#u8,189#u8,236#u8,66#u8,77#u8,101#u8,187#u8,13#u8],by rfl⟩
def limbs16 : QM31Limbs := ![⟨390887732,by change 390887732<2147483647;omega⟩,⟨280705424,by change 280705424<2147483647;omega⟩,⟨1122811182,by change 1122811182<2147483647;omega⟩,⟨230384973,by change 230384973<2147483647;omega⟩]
theorem rawCell16 : (raw.drop 256).take 16=cell16.val := by
  simp only [raw,JFz_Scan56.data,JFz_Scan56.j00,JFz_Scan56.j01,JFz_Scan56.j02,JFz_Scan56.j03,JFz_Scan56.j04,JFz_Scan56.j05,JFz_Scan56.j06,JFz_Scan56.j07,JFz_Scan56.j08,JFz_Scan56.j09,JFz_Scan56.j10,JFz_Scan56.j11,JFz_Scan56.j12,JFz_Scan56.b00_length,JFz_Scan56.b01_length,JFz_Scan56.b02_length,JFz_Scan56.b03_length,JFz_Scan56.b04_length,JFz_Scan56.b05_length,JFz_Scan56.b06_length,JFz_Scan56.b07_length,JFz_Scan56.b08_length,JFz_Scan56.b09_length,JFz_Scan56.b10_length,JFz_Scan56.b11_length,JFz_Scan56.b12_length,JFz_Scan56.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell16
theorem encoded16 : CandidateParserByteOrder.arrayBytes16 cell16=encodeQM31LE limbs16 := by
  funext i
  fin_cases i <;> rfl
theorem parser16 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell16)=
    ok (some ⟨⟨390887732#u32,280705424#u32⟩,⟨1122811182#u32,230384973#u32⟩⟩) :=
  JFr_EncodedCell.parser cell16 limbs16 encoded16
#print axioms encoded16
#print axioms parser16
def cell17 : Array U8 16#usize := ⟨[189#u8,192#u8,240#u8,64#u8,127#u8,102#u8,158#u8,90#u8,169#u8,116#u8,255#u8,10#u8,111#u8,234#u8,241#u8,39#u8],by rfl⟩
def limbs17 : QM31Limbs := ![⟨1089519805,by change 1089519805<2147483647;omega⟩,⟨1520330367,by change 1520330367<2147483647;omega⟩,⟨184513705,by change 184513705<2147483647;omega⟩,⟨670165615,by change 670165615<2147483647;omega⟩]
theorem rawCell17 : (raw.drop 272).take 16=cell17.val := by
  simp only [raw,JFz_Scan56.data,JFz_Scan56.j00,JFz_Scan56.j01,JFz_Scan56.j02,JFz_Scan56.j03,JFz_Scan56.j04,JFz_Scan56.j05,JFz_Scan56.j06,JFz_Scan56.j07,JFz_Scan56.j08,JFz_Scan56.j09,JFz_Scan56.j10,JFz_Scan56.j11,JFz_Scan56.j12,JFz_Scan56.b00_length,JFz_Scan56.b01_length,JFz_Scan56.b02_length,JFz_Scan56.b03_length,JFz_Scan56.b04_length,JFz_Scan56.b05_length,JFz_Scan56.b06_length,JFz_Scan56.b07_length,JFz_Scan56.b08_length,JFz_Scan56.b09_length,JFz_Scan56.b10_length,JFz_Scan56.b11_length,JFz_Scan56.b12_length,JFz_Scan56.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell17
theorem encoded17 : CandidateParserByteOrder.arrayBytes16 cell17=encodeQM31LE limbs17 := by
  funext i
  fin_cases i <;> rfl
theorem parser17 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell17)=
    ok (some ⟨⟨1089519805#u32,1520330367#u32⟩,⟨184513705#u32,670165615#u32⟩⟩) :=
  JFr_EncodedCell.parser cell17 limbs17 encoded17
#print axioms encoded17
#print axioms parser17
def cell18 : Array U8 16#usize := ⟨[99#u8,84#u8,144#u8,53#u8,171#u8,197#u8,129#u8,111#u8,226#u8,236#u8,75#u8,8#u8,161#u8,203#u8,130#u8,36#u8],by rfl⟩
def limbs18 : QM31Limbs := ![⟨898651235,by change 898651235<2147483647;omega⟩,⟨1870775723,by change 1870775723<2147483647;omega⟩,⟨139193570,by change 139193570<2147483647;omega⟩,⟨612551585,by change 612551585<2147483647;omega⟩]
theorem rawCell18 : (raw.drop 288).take 16=cell18.val := by
  simp only [raw,JFz_Scan56.data,JFz_Scan56.j00,JFz_Scan56.j01,JFz_Scan56.j02,JFz_Scan56.j03,JFz_Scan56.j04,JFz_Scan56.j05,JFz_Scan56.j06,JFz_Scan56.j07,JFz_Scan56.j08,JFz_Scan56.j09,JFz_Scan56.j10,JFz_Scan56.j11,JFz_Scan56.j12,JFz_Scan56.b00_length,JFz_Scan56.b01_length,JFz_Scan56.b02_length,JFz_Scan56.b03_length,JFz_Scan56.b04_length,JFz_Scan56.b05_length,JFz_Scan56.b06_length,JFz_Scan56.b07_length,JFz_Scan56.b08_length,JFz_Scan56.b09_length,JFz_Scan56.b10_length,JFz_Scan56.b11_length,JFz_Scan56.b12_length,JFz_Scan56.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell18
theorem encoded18 : CandidateParserByteOrder.arrayBytes16 cell18=encodeQM31LE limbs18 := by
  funext i
  fin_cases i <;> rfl
theorem parser18 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell18)=
    ok (some ⟨⟨898651235#u32,1870775723#u32⟩,⟨139193570#u32,612551585#u32⟩⟩) :=
  JFr_EncodedCell.parser cell18 limbs18 encoded18
#print axioms encoded18
#print axioms parser18
def cell19 : Array U8 16#usize := ⟨[82#u8,72#u8,240#u8,5#u8,124#u8,29#u8,76#u8,85#u8,164#u8,66#u8,146#u8,66#u8,13#u8,233#u8,119#u8,107#u8],by rfl⟩
def limbs19 : QM31Limbs := ![⟨99633234,by change 99633234<2147483647;omega⟩,⟨1431051644,by change 1431051644<2147483647;omega⟩,⟨1116881572,by change 1116881572<2147483647;omega⟩,⟨1803020557,by change 1803020557<2147483647;omega⟩]
theorem rawCell19 : (raw.drop 304).take 16=cell19.val := by
  simp only [raw,JFz_Scan56.data,JFz_Scan56.j00,JFz_Scan56.j01,JFz_Scan56.j02,JFz_Scan56.j03,JFz_Scan56.j04,JFz_Scan56.j05,JFz_Scan56.j06,JFz_Scan56.j07,JFz_Scan56.j08,JFz_Scan56.j09,JFz_Scan56.j10,JFz_Scan56.j11,JFz_Scan56.j12,JFz_Scan56.b00_length,JFz_Scan56.b01_length,JFz_Scan56.b02_length,JFz_Scan56.b03_length,JFz_Scan56.b04_length,JFz_Scan56.b05_length,JFz_Scan56.b06_length,JFz_Scan56.b07_length,JFz_Scan56.b08_length,JFz_Scan56.b09_length,JFz_Scan56.b10_length,JFz_Scan56.b11_length,JFz_Scan56.b12_length,JFz_Scan56.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell19
theorem encoded19 : CandidateParserByteOrder.arrayBytes16 cell19=encodeQM31LE limbs19 := by
  funext i
  fin_cases i <;> rfl
theorem parser19 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell19)=
    ok (some ⟨⟨99633234#u32,1431051644#u32⟩,⟨1116881572#u32,1803020557#u32⟩⟩) :=
  JFr_EncodedCell.parser cell19 limbs19 encoded19
#print axioms encoded19
#print axioms parser19
def cell20 : Array U8 16#usize := ⟨[215#u8,54#u8,118#u8,125#u8,83#u8,199#u8,208#u8,114#u8,163#u8,145#u8,72#u8,90#u8,122#u8,243#u8,80#u8,42#u8],by rfl⟩
def limbs20 : QM31Limbs := ![⟨2104899287,by change 2104899287<2147483647;omega⟩,⟨1926285139,by change 1926285139<2147483647;omega⟩,⟨1514705315,by change 1514705315<2147483647;omega⟩,⟨709948282,by change 709948282<2147483647;omega⟩]
theorem rawCell20 : (raw.drop 320).take 16=cell20.val := by
  simp only [raw,JFz_Scan56.data,JFz_Scan56.j00,JFz_Scan56.j01,JFz_Scan56.j02,JFz_Scan56.j03,JFz_Scan56.j04,JFz_Scan56.j05,JFz_Scan56.j06,JFz_Scan56.j07,JFz_Scan56.j08,JFz_Scan56.j09,JFz_Scan56.j10,JFz_Scan56.j11,JFz_Scan56.j12,JFz_Scan56.b00_length,JFz_Scan56.b01_length,JFz_Scan56.b02_length,JFz_Scan56.b03_length,JFz_Scan56.b04_length,JFz_Scan56.b05_length,JFz_Scan56.b06_length,JFz_Scan56.b07_length,JFz_Scan56.b08_length,JFz_Scan56.b09_length,JFz_Scan56.b10_length,JFz_Scan56.b11_length,JFz_Scan56.b12_length,JFz_Scan56.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell20
theorem encoded20 : CandidateParserByteOrder.arrayBytes16 cell20=encodeQM31LE limbs20 := by
  funext i
  fin_cases i <;> rfl
theorem parser20 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell20)=
    ok (some ⟨⟨2104899287#u32,1926285139#u32⟩,⟨1514705315#u32,709948282#u32⟩⟩) :=
  JFr_EncodedCell.parser cell20 limbs20 encoded20
#print axioms encoded20
#print axioms parser20
def cell21 : Array U8 16#usize := ⟨[56#u8,155#u8,231#u8,109#u8,163#u8,19#u8,37#u8,59#u8,241#u8,197#u8,20#u8,36#u8,228#u8,21#u8,103#u8,0#u8],by rfl⟩
def limbs21 : QM31Limbs := ![⟨1843895096,by change 1843895096<2147483647;omega⟩,⟨992285603,by change 992285603<2147483647;omega⟩,⟨605341169,by change 605341169<2147483647;omega⟩,⟨6755812,by change 6755812<2147483647;omega⟩]
theorem rawCell21 : (raw.drop 336).take 16=cell21.val := by
  simp only [raw,JFz_Scan56.data,JFz_Scan56.j00,JFz_Scan56.j01,JFz_Scan56.j02,JFz_Scan56.j03,JFz_Scan56.j04,JFz_Scan56.j05,JFz_Scan56.j06,JFz_Scan56.j07,JFz_Scan56.j08,JFz_Scan56.j09,JFz_Scan56.j10,JFz_Scan56.j11,JFz_Scan56.j12,JFz_Scan56.b00_length,JFz_Scan56.b01_length,JFz_Scan56.b02_length,JFz_Scan56.b03_length,JFz_Scan56.b04_length,JFz_Scan56.b05_length,JFz_Scan56.b06_length,JFz_Scan56.b07_length,JFz_Scan56.b08_length,JFz_Scan56.b09_length,JFz_Scan56.b10_length,JFz_Scan56.b11_length,JFz_Scan56.b12_length,JFz_Scan56.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell21
theorem encoded21 : CandidateParserByteOrder.arrayBytes16 cell21=encodeQM31LE limbs21 := by
  funext i
  fin_cases i <;> rfl
theorem parser21 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell21)=
    ok (some ⟨⟨1843895096#u32,992285603#u32⟩,⟨605341169#u32,6755812#u32⟩⟩) :=
  JFr_EncodedCell.parser cell21 limbs21 encoded21
#print axioms encoded21
#print axioms parser21
def cell22 : Array U8 16#usize := ⟨[59#u8,36#u8,225#u8,1#u8,48#u8,6#u8,171#u8,98#u8,95#u8,218#u8,17#u8,105#u8,154#u8,153#u8,67#u8,36#u8],by rfl⟩
def limbs22 : QM31Limbs := ![⟨31532091,by change 31532091<2147483647;omega⟩,⟨1655375408,by change 1655375408<2147483647;omega⟩,⟨1762777695,by change 1762777695<2147483647;omega⟩,⟨608410010,by change 608410010<2147483647;omega⟩]
theorem rawCell22 : (raw.drop 352).take 16=cell22.val := by
  simp only [raw,JFz_Scan56.data,JFz_Scan56.j00,JFz_Scan56.j01,JFz_Scan56.j02,JFz_Scan56.j03,JFz_Scan56.j04,JFz_Scan56.j05,JFz_Scan56.j06,JFz_Scan56.j07,JFz_Scan56.j08,JFz_Scan56.j09,JFz_Scan56.j10,JFz_Scan56.j11,JFz_Scan56.j12,JFz_Scan56.b00_length,JFz_Scan56.b01_length,JFz_Scan56.b02_length,JFz_Scan56.b03_length,JFz_Scan56.b04_length,JFz_Scan56.b05_length,JFz_Scan56.b06_length,JFz_Scan56.b07_length,JFz_Scan56.b08_length,JFz_Scan56.b09_length,JFz_Scan56.b10_length,JFz_Scan56.b11_length,JFz_Scan56.b12_length,JFz_Scan56.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell22
theorem encoded22 : CandidateParserByteOrder.arrayBytes16 cell22=encodeQM31LE limbs22 := by
  funext i
  fin_cases i <;> rfl
theorem parser22 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell22)=
    ok (some ⟨⟨31532091#u32,1655375408#u32⟩,⟨1762777695#u32,608410010#u32⟩⟩) :=
  JFr_EncodedCell.parser cell22 limbs22 encoded22
#print axioms encoded22
#print axioms parser22
def cell23 : Array U8 16#usize := ⟨[216#u8,148#u8,165#u8,44#u8,100#u8,78#u8,57#u8,114#u8,139#u8,144#u8,43#u8,39#u8,177#u8,214#u8,136#u8,56#u8],by rfl⟩
def limbs23 : QM31Limbs := ![⟨749049048,by change 749049048<2147483647;omega⟩,⟨1916358244,by change 1916358244<2147483647;omega⟩,⟨657166475,by change 657166475<2147483647;omega⟩,⟨948491953,by change 948491953<2147483647;omega⟩]
theorem rawCell23 : (raw.drop 368).take 16=cell23.val := by
  simp only [raw,JFz_Scan56.data,JFz_Scan56.j00,JFz_Scan56.j01,JFz_Scan56.j02,JFz_Scan56.j03,JFz_Scan56.j04,JFz_Scan56.j05,JFz_Scan56.j06,JFz_Scan56.j07,JFz_Scan56.j08,JFz_Scan56.j09,JFz_Scan56.j10,JFz_Scan56.j11,JFz_Scan56.j12,JFz_Scan56.b00_length,JFz_Scan56.b01_length,JFz_Scan56.b02_length,JFz_Scan56.b03_length,JFz_Scan56.b04_length,JFz_Scan56.b05_length,JFz_Scan56.b06_length,JFz_Scan56.b07_length,JFz_Scan56.b08_length,JFz_Scan56.b09_length,JFz_Scan56.b10_length,JFz_Scan56.b11_length,JFz_Scan56.b12_length,JFz_Scan56.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell23
theorem encoded23 : CandidateParserByteOrder.arrayBytes16 cell23=encodeQM31LE limbs23 := by
  funext i
  fin_cases i <;> rfl
theorem parser23 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell23)=
    ok (some ⟨⟨749049048#u32,1916358244#u32⟩,⟨657166475#u32,948491953#u32⟩⟩) :=
  JFr_EncodedCell.parser cell23 limbs23 encoded23
#print axioms encoded23
#print axioms parser23
def cell24 : Array U8 16#usize := ⟨[140#u8,171#u8,109#u8,122#u8,83#u8,210#u8,179#u8,75#u8,91#u8,133#u8,62#u8,40#u8,187#u8,1#u8,254#u8,36#u8],by rfl⟩
def limbs24 : QM31Limbs := ![⟨2054007692,by change 2054007692<2147483647;omega⟩,⟨1270075987,by change 1270075987<2147483647;omega⟩,⟨675186011,by change 675186011<2147483647;omega⟩,⟨620626363,by change 620626363<2147483647;omega⟩]
theorem rawCell24 : (raw.drop 384).take 16=cell24.val := by
  simp only [raw,JFz_Scan56.data,JFz_Scan56.j00,JFz_Scan56.j01,JFz_Scan56.j02,JFz_Scan56.j03,JFz_Scan56.j04,JFz_Scan56.j05,JFz_Scan56.j06,JFz_Scan56.j07,JFz_Scan56.j08,JFz_Scan56.j09,JFz_Scan56.j10,JFz_Scan56.j11,JFz_Scan56.j12,JFz_Scan56.b00_length,JFz_Scan56.b01_length,JFz_Scan56.b02_length,JFz_Scan56.b03_length,JFz_Scan56.b04_length,JFz_Scan56.b05_length,JFz_Scan56.b06_length,JFz_Scan56.b07_length,JFz_Scan56.b08_length,JFz_Scan56.b09_length,JFz_Scan56.b10_length,JFz_Scan56.b11_length,JFz_Scan56.b12_length,JFz_Scan56.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell24
theorem encoded24 : CandidateParserByteOrder.arrayBytes16 cell24=encodeQM31LE limbs24 := by
  funext i
  fin_cases i <;> rfl
theorem parser24 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell24)=
    ok (some ⟨⟨2054007692#u32,1270075987#u32⟩,⟨675186011#u32,620626363#u32⟩⟩) :=
  JFr_EncodedCell.parser cell24 limbs24 encoded24
#print axioms encoded24
#print axioms parser24
def cell25 : Array U8 16#usize := ⟨[143#u8,41#u8,36#u8,15#u8,26#u8,115#u8,42#u8,55#u8,231#u8,121#u8,238#u8,5#u8,66#u8,225#u8,156#u8,65#u8],by rfl⟩
def limbs25 : QM31Limbs := ![⟨254028175,by change 254028175<2147483647;omega⟩,⟨925528858,by change 925528858<2147483647;omega⟩,⟨99514855,by change 99514855<2147483647;omega⟩,⟨1100800322,by change 1100800322<2147483647;omega⟩]
theorem rawCell25 : (raw.drop 400).take 16=cell25.val := by
  simp only [raw,JFz_Scan56.data,JFz_Scan56.j00,JFz_Scan56.j01,JFz_Scan56.j02,JFz_Scan56.j03,JFz_Scan56.j04,JFz_Scan56.j05,JFz_Scan56.j06,JFz_Scan56.j07,JFz_Scan56.j08,JFz_Scan56.j09,JFz_Scan56.j10,JFz_Scan56.j11,JFz_Scan56.j12,JFz_Scan56.b00_length,JFz_Scan56.b01_length,JFz_Scan56.b02_length,JFz_Scan56.b03_length,JFz_Scan56.b04_length,JFz_Scan56.b05_length,JFz_Scan56.b06_length,JFz_Scan56.b07_length,JFz_Scan56.b08_length,JFz_Scan56.b09_length,JFz_Scan56.b10_length,JFz_Scan56.b11_length,JFz_Scan56.b12_length,JFz_Scan56.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell25
theorem encoded25 : CandidateParserByteOrder.arrayBytes16 cell25=encodeQM31LE limbs25 := by
  funext i
  fin_cases i <;> rfl
theorem parser25 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell25)=
    ok (some ⟨⟨254028175#u32,925528858#u32⟩,⟨99514855#u32,1100800322#u32⟩⟩) :=
  JFr_EncodedCell.parser cell25 limbs25 encoded25
#print axioms encoded25
#print axioms parser25
def cell26 : Array U8 16#usize := ⟨[48#u8,218#u8,43#u8,41#u8,26#u8,173#u8,112#u8,41#u8,14#u8,153#u8,35#u8,22#u8,109#u8,248#u8,96#u8,39#u8],by rfl⟩
def limbs26 : QM31Limbs := ![⟨690739760,by change 690739760<2147483647;omega⟩,⟨695250202,by change 695250202<2147483647;omega⟩,⟨371431694,by change 371431694<2147483647;omega⟩,⟨660666477,by change 660666477<2147483647;omega⟩]
theorem rawCell26 : (raw.drop 416).take 16=cell26.val := by
  simp only [raw,JFz_Scan56.data,JFz_Scan56.j00,JFz_Scan56.j01,JFz_Scan56.j02,JFz_Scan56.j03,JFz_Scan56.j04,JFz_Scan56.j05,JFz_Scan56.j06,JFz_Scan56.j07,JFz_Scan56.j08,JFz_Scan56.j09,JFz_Scan56.j10,JFz_Scan56.j11,JFz_Scan56.j12,JFz_Scan56.b00_length,JFz_Scan56.b01_length,JFz_Scan56.b02_length,JFz_Scan56.b03_length,JFz_Scan56.b04_length,JFz_Scan56.b05_length,JFz_Scan56.b06_length,JFz_Scan56.b07_length,JFz_Scan56.b08_length,JFz_Scan56.b09_length,JFz_Scan56.b10_length,JFz_Scan56.b11_length,JFz_Scan56.b12_length,JFz_Scan56.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell26
theorem encoded26 : CandidateParserByteOrder.arrayBytes16 cell26=encodeQM31LE limbs26 := by
  funext i
  fin_cases i <;> rfl
theorem parser26 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell26)=
    ok (some ⟨⟨690739760#u32,695250202#u32⟩,⟨371431694#u32,660666477#u32⟩⟩) :=
  JFr_EncodedCell.parser cell26 limbs26 encoded26
#print axioms encoded26
#print axioms parser26
def cell27 : Array U8 16#usize := ⟨[78#u8,24#u8,188#u8,101#u8,188#u8,35#u8,161#u8,92#u8,47#u8,104#u8,134#u8,19#u8,60#u8,190#u8,59#u8,83#u8],by rfl⟩
def limbs27 : QM31Limbs := ![⟨1706825806,by change 1706825806<2147483647;omega⟩,⟨1554064316,by change 1554064316<2147483647;omega⟩,⟨327575599,by change 327575599<2147483647;omega⟩,⟨1396424252,by change 1396424252<2147483647;omega⟩]
theorem rawCell27 : (raw.drop 432).take 16=cell27.val := by
  simp only [raw,JFz_Scan56.data,JFz_Scan56.j00,JFz_Scan56.j01,JFz_Scan56.j02,JFz_Scan56.j03,JFz_Scan56.j04,JFz_Scan56.j05,JFz_Scan56.j06,JFz_Scan56.j07,JFz_Scan56.j08,JFz_Scan56.j09,JFz_Scan56.j10,JFz_Scan56.j11,JFz_Scan56.j12,JFz_Scan56.b00_length,JFz_Scan56.b01_length,JFz_Scan56.b02_length,JFz_Scan56.b03_length,JFz_Scan56.b04_length,JFz_Scan56.b05_length,JFz_Scan56.b06_length,JFz_Scan56.b07_length,JFz_Scan56.b08_length,JFz_Scan56.b09_length,JFz_Scan56.b10_length,JFz_Scan56.b11_length,JFz_Scan56.b12_length,JFz_Scan56.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell27
theorem encoded27 : CandidateParserByteOrder.arrayBytes16 cell27=encodeQM31LE limbs27 := by
  funext i
  fin_cases i <;> rfl
theorem parser27 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell27)=
    ok (some ⟨⟨1706825806#u32,1554064316#u32⟩,⟨327575599#u32,1396424252#u32⟩⟩) :=
  JFr_EncodedCell.parser cell27 limbs27 encoded27
#print axioms encoded27
#print axioms parser27
end AspisR1.JFr_Bytes08
