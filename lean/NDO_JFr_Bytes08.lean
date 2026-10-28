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
def cell00 : Array U8 16#usize := ⟨[34#u8,75#u8,193#u8,88#u8,124#u8,131#u8,225#u8,51#u8,92#u8,162#u8,255#u8,52#u8,219#u8,46#u8,149#u8,106#u8],by rfl⟩
def limbs00 : QM31Limbs := ![⟨1489062690,by change 1489062690<2147483647;omega⟩,⟨870417276,by change 870417276<2147483647;omega⟩,⟨889168476,by change 889168476<2147483647;omega⟩,⟨1788161755,by change 1788161755<2147483647;omega⟩]
theorem rawCell00 : (raw.drop 0).take 16=cell00.val := by
  simp only [raw,JFz_Scan56.data,JFz_Scan56.j00,JFz_Scan56.j01,JFz_Scan56.j02,JFz_Scan56.j03,JFz_Scan56.j04,JFz_Scan56.j05,JFz_Scan56.j06,JFz_Scan56.j07,JFz_Scan56.j08,JFz_Scan56.j09,JFz_Scan56.j10,JFz_Scan56.j11,JFz_Scan56.j12,JFz_Scan56.b00_length,JFz_Scan56.b01_length,JFz_Scan56.b02_length,JFz_Scan56.b03_length,JFz_Scan56.b04_length,JFz_Scan56.b05_length,JFz_Scan56.b06_length,JFz_Scan56.b07_length,JFz_Scan56.b08_length,JFz_Scan56.b09_length,JFz_Scan56.b10_length,JFz_Scan56.b11_length,JFz_Scan56.b12_length,JFz_Scan56.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell00
theorem encoded00 : CandidateParserByteOrder.arrayBytes16 cell00=encodeQM31LE limbs00 := by
  funext i
  fin_cases i <;> rfl
theorem parser00 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell00)=
    ok (some ⟨⟨1489062690#u32,870417276#u32⟩,⟨889168476#u32,1788161755#u32⟩⟩) :=
  JFr_EncodedCell.parser cell00 limbs00 encoded00
#print axioms encoded00
#print axioms parser00
def cell01 : Array U8 16#usize := ⟨[17#u8,36#u8,14#u8,64#u8,216#u8,182#u8,228#u8,25#u8,88#u8,81#u8,71#u8,53#u8,232#u8,141#u8,153#u8,21#u8],by rfl⟩
def limbs01 : QM31Limbs := ![⟨1074668561,by change 1074668561<2147483647;omega⟩,⟨434419416,by change 434419416<2147483647;omega⟩,⟨893866328,by change 893866328<2147483647;omega⟩,⟨362384872,by change 362384872<2147483647;omega⟩]
theorem rawCell01 : (raw.drop 16).take 16=cell01.val := by
  simp only [raw,JFz_Scan56.data,JFz_Scan56.j00,JFz_Scan56.j01,JFz_Scan56.j02,JFz_Scan56.j03,JFz_Scan56.j04,JFz_Scan56.j05,JFz_Scan56.j06,JFz_Scan56.j07,JFz_Scan56.j08,JFz_Scan56.j09,JFz_Scan56.j10,JFz_Scan56.j11,JFz_Scan56.j12,JFz_Scan56.b00_length,JFz_Scan56.b01_length,JFz_Scan56.b02_length,JFz_Scan56.b03_length,JFz_Scan56.b04_length,JFz_Scan56.b05_length,JFz_Scan56.b06_length,JFz_Scan56.b07_length,JFz_Scan56.b08_length,JFz_Scan56.b09_length,JFz_Scan56.b10_length,JFz_Scan56.b11_length,JFz_Scan56.b12_length,JFz_Scan56.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell01
theorem encoded01 : CandidateParserByteOrder.arrayBytes16 cell01=encodeQM31LE limbs01 := by
  funext i
  fin_cases i <;> rfl
theorem parser01 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell01)=
    ok (some ⟨⟨1074668561#u32,434419416#u32⟩,⟨893866328#u32,362384872#u32⟩⟩) :=
  JFr_EncodedCell.parser cell01 limbs01 encoded01
#print axioms encoded01
#print axioms parser01
def cell02 : Array U8 16#usize := ⟨[62#u8,186#u8,164#u8,76#u8,3#u8,248#u8,136#u8,75#u8,85#u8,107#u8,210#u8,16#u8,177#u8,147#u8,120#u8,45#u8],by rfl⟩
def limbs02 : QM31Limbs := ![⟨1285863998,by change 1285863998<2147483647;omega⟩,⟨1267267587,by change 1267267587<2147483647;omega⟩,⟨282225493,by change 282225493<2147483647;omega⟩,⟨762876849,by change 762876849<2147483647;omega⟩]
theorem rawCell02 : (raw.drop 32).take 16=cell02.val := by
  simp only [raw,JFz_Scan56.data,JFz_Scan56.j00,JFz_Scan56.j01,JFz_Scan56.j02,JFz_Scan56.j03,JFz_Scan56.j04,JFz_Scan56.j05,JFz_Scan56.j06,JFz_Scan56.j07,JFz_Scan56.j08,JFz_Scan56.j09,JFz_Scan56.j10,JFz_Scan56.j11,JFz_Scan56.j12,JFz_Scan56.b00_length,JFz_Scan56.b01_length,JFz_Scan56.b02_length,JFz_Scan56.b03_length,JFz_Scan56.b04_length,JFz_Scan56.b05_length,JFz_Scan56.b06_length,JFz_Scan56.b07_length,JFz_Scan56.b08_length,JFz_Scan56.b09_length,JFz_Scan56.b10_length,JFz_Scan56.b11_length,JFz_Scan56.b12_length,JFz_Scan56.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell02
theorem encoded02 : CandidateParserByteOrder.arrayBytes16 cell02=encodeQM31LE limbs02 := by
  funext i
  fin_cases i <;> rfl
theorem parser02 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell02)=
    ok (some ⟨⟨1285863998#u32,1267267587#u32⟩,⟨282225493#u32,762876849#u32⟩⟩) :=
  JFr_EncodedCell.parser cell02 limbs02 encoded02
#print axioms encoded02
#print axioms parser02
def cell03 : Array U8 16#usize := ⟨[118#u8,92#u8,240#u8,65#u8,249#u8,219#u8,183#u8,3#u8,160#u8,24#u8,13#u8,112#u8,48#u8,245#u8,182#u8,92#u8],by rfl⟩
def limbs03 : QM31Limbs := ![⟨1106271350,by change 1106271350<2147483647;omega⟩,⟨62381049,by change 62381049<2147483647;omega⟩,⟨1879906464,by change 1879906464<2147483647;omega⟩,⟨1555494192,by change 1555494192<2147483647;omega⟩]
theorem rawCell03 : (raw.drop 48).take 16=cell03.val := by
  simp only [raw,JFz_Scan56.data,JFz_Scan56.j00,JFz_Scan56.j01,JFz_Scan56.j02,JFz_Scan56.j03,JFz_Scan56.j04,JFz_Scan56.j05,JFz_Scan56.j06,JFz_Scan56.j07,JFz_Scan56.j08,JFz_Scan56.j09,JFz_Scan56.j10,JFz_Scan56.j11,JFz_Scan56.j12,JFz_Scan56.b00_length,JFz_Scan56.b01_length,JFz_Scan56.b02_length,JFz_Scan56.b03_length,JFz_Scan56.b04_length,JFz_Scan56.b05_length,JFz_Scan56.b06_length,JFz_Scan56.b07_length,JFz_Scan56.b08_length,JFz_Scan56.b09_length,JFz_Scan56.b10_length,JFz_Scan56.b11_length,JFz_Scan56.b12_length,JFz_Scan56.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell03
theorem encoded03 : CandidateParserByteOrder.arrayBytes16 cell03=encodeQM31LE limbs03 := by
  funext i
  fin_cases i <;> rfl
theorem parser03 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell03)=
    ok (some ⟨⟨1106271350#u32,62381049#u32⟩,⟨1879906464#u32,1555494192#u32⟩⟩) :=
  JFr_EncodedCell.parser cell03 limbs03 encoded03
#print axioms encoded03
#print axioms parser03
def cell04 : Array U8 16#usize := ⟨[10#u8,124#u8,252#u8,30#u8,162#u8,192#u8,87#u8,47#u8,3#u8,48#u8,67#u8,54#u8,184#u8,6#u8,205#u8,120#u8],by rfl⟩
def limbs04 : QM31Limbs := ![⟨519863306,by change 519863306<2147483647;omega⟩,⟨794280098,by change 794280098<2147483647;omega⟩,⟨910372867,by change 910372867<2147483647;omega⟩,⟨2026702520,by change 2026702520<2147483647;omega⟩]
theorem rawCell04 : (raw.drop 64).take 16=cell04.val := by
  simp only [raw,JFz_Scan56.data,JFz_Scan56.j00,JFz_Scan56.j01,JFz_Scan56.j02,JFz_Scan56.j03,JFz_Scan56.j04,JFz_Scan56.j05,JFz_Scan56.j06,JFz_Scan56.j07,JFz_Scan56.j08,JFz_Scan56.j09,JFz_Scan56.j10,JFz_Scan56.j11,JFz_Scan56.j12,JFz_Scan56.b00_length,JFz_Scan56.b01_length,JFz_Scan56.b02_length,JFz_Scan56.b03_length,JFz_Scan56.b04_length,JFz_Scan56.b05_length,JFz_Scan56.b06_length,JFz_Scan56.b07_length,JFz_Scan56.b08_length,JFz_Scan56.b09_length,JFz_Scan56.b10_length,JFz_Scan56.b11_length,JFz_Scan56.b12_length,JFz_Scan56.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell04
theorem encoded04 : CandidateParserByteOrder.arrayBytes16 cell04=encodeQM31LE limbs04 := by
  funext i
  fin_cases i <;> rfl
theorem parser04 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell04)=
    ok (some ⟨⟨519863306#u32,794280098#u32⟩,⟨910372867#u32,2026702520#u32⟩⟩) :=
  JFr_EncodedCell.parser cell04 limbs04 encoded04
#print axioms encoded04
#print axioms parser04
def cell05 : Array U8 16#usize := ⟨[54#u8,93#u8,121#u8,101#u8,242#u8,164#u8,219#u8,52#u8,101#u8,181#u8,121#u8,84#u8,105#u8,124#u8,111#u8,59#u8],by rfl⟩
def limbs05 : QM31Limbs := ![⟨1702452534,by change 1702452534<2147483647;omega⟩,⟨886809842,by change 886809842<2147483647;omega⟩,⟨1417262437,by change 1417262437<2147483647;omega⟩,⟨997162089,by change 997162089<2147483647;omega⟩]
theorem rawCell05 : (raw.drop 80).take 16=cell05.val := by
  simp only [raw,JFz_Scan56.data,JFz_Scan56.j00,JFz_Scan56.j01,JFz_Scan56.j02,JFz_Scan56.j03,JFz_Scan56.j04,JFz_Scan56.j05,JFz_Scan56.j06,JFz_Scan56.j07,JFz_Scan56.j08,JFz_Scan56.j09,JFz_Scan56.j10,JFz_Scan56.j11,JFz_Scan56.j12,JFz_Scan56.b00_length,JFz_Scan56.b01_length,JFz_Scan56.b02_length,JFz_Scan56.b03_length,JFz_Scan56.b04_length,JFz_Scan56.b05_length,JFz_Scan56.b06_length,JFz_Scan56.b07_length,JFz_Scan56.b08_length,JFz_Scan56.b09_length,JFz_Scan56.b10_length,JFz_Scan56.b11_length,JFz_Scan56.b12_length,JFz_Scan56.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell05
theorem encoded05 : CandidateParserByteOrder.arrayBytes16 cell05=encodeQM31LE limbs05 := by
  funext i
  fin_cases i <;> rfl
theorem parser05 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell05)=
    ok (some ⟨⟨1702452534#u32,886809842#u32⟩,⟨1417262437#u32,997162089#u32⟩⟩) :=
  JFr_EncodedCell.parser cell05 limbs05 encoded05
#print axioms encoded05
#print axioms parser05
def cell06 : Array U8 16#usize := ⟨[204#u8,224#u8,128#u8,126#u8,176#u8,175#u8,56#u8,48#u8,176#u8,160#u8,248#u8,70#u8,239#u8,157#u8,247#u8,82#u8],by rfl⟩
def limbs06 : QM31Limbs := ![⟨2122375372,by change 2122375372<2147483647;omega⟩,⟨809021360,by change 809021360<2147483647;omega⟩,⟨1190699184,by change 1190699184<2147483647;omega⟩,⟨1391959535,by change 1391959535<2147483647;omega⟩]
theorem rawCell06 : (raw.drop 96).take 16=cell06.val := by
  simp only [raw,JFz_Scan56.data,JFz_Scan56.j00,JFz_Scan56.j01,JFz_Scan56.j02,JFz_Scan56.j03,JFz_Scan56.j04,JFz_Scan56.j05,JFz_Scan56.j06,JFz_Scan56.j07,JFz_Scan56.j08,JFz_Scan56.j09,JFz_Scan56.j10,JFz_Scan56.j11,JFz_Scan56.j12,JFz_Scan56.b00_length,JFz_Scan56.b01_length,JFz_Scan56.b02_length,JFz_Scan56.b03_length,JFz_Scan56.b04_length,JFz_Scan56.b05_length,JFz_Scan56.b06_length,JFz_Scan56.b07_length,JFz_Scan56.b08_length,JFz_Scan56.b09_length,JFz_Scan56.b10_length,JFz_Scan56.b11_length,JFz_Scan56.b12_length,JFz_Scan56.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell06
theorem encoded06 : CandidateParserByteOrder.arrayBytes16 cell06=encodeQM31LE limbs06 := by
  funext i
  fin_cases i <;> rfl
theorem parser06 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell06)=
    ok (some ⟨⟨2122375372#u32,809021360#u32⟩,⟨1190699184#u32,1391959535#u32⟩⟩) :=
  JFr_EncodedCell.parser cell06 limbs06 encoded06
#print axioms encoded06
#print axioms parser06
def cell07 : Array U8 16#usize := ⟨[148#u8,48#u8,73#u8,86#u8,201#u8,2#u8,4#u8,112#u8,254#u8,124#u8,135#u8,122#u8,6#u8,214#u8,24#u8,115#u8],by rfl⟩
def limbs07 : QM31Limbs := ![⟨1447637140,by change 1447637140<2147483647;omega⟩,⟨1879311049,by change 1879311049<2147483647;omega⟩,⟨2055699710,by change 2055699710<2147483647;omega⟩,⟨1931007494,by change 1931007494<2147483647;omega⟩]
theorem rawCell07 : (raw.drop 112).take 16=cell07.val := by
  simp only [raw,JFz_Scan56.data,JFz_Scan56.j00,JFz_Scan56.j01,JFz_Scan56.j02,JFz_Scan56.j03,JFz_Scan56.j04,JFz_Scan56.j05,JFz_Scan56.j06,JFz_Scan56.j07,JFz_Scan56.j08,JFz_Scan56.j09,JFz_Scan56.j10,JFz_Scan56.j11,JFz_Scan56.j12,JFz_Scan56.b00_length,JFz_Scan56.b01_length,JFz_Scan56.b02_length,JFz_Scan56.b03_length,JFz_Scan56.b04_length,JFz_Scan56.b05_length,JFz_Scan56.b06_length,JFz_Scan56.b07_length,JFz_Scan56.b08_length,JFz_Scan56.b09_length,JFz_Scan56.b10_length,JFz_Scan56.b11_length,JFz_Scan56.b12_length,JFz_Scan56.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell07
theorem encoded07 : CandidateParserByteOrder.arrayBytes16 cell07=encodeQM31LE limbs07 := by
  funext i
  fin_cases i <;> rfl
theorem parser07 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell07)=
    ok (some ⟨⟨1447637140#u32,1879311049#u32⟩,⟨2055699710#u32,1931007494#u32⟩⟩) :=
  JFr_EncodedCell.parser cell07 limbs07 encoded07
#print axioms encoded07
#print axioms parser07
def cell08 : Array U8 16#usize := ⟨[47#u8,186#u8,116#u8,2#u8,167#u8,3#u8,7#u8,68#u8,220#u8,99#u8,95#u8,72#u8,40#u8,61#u8,55#u8,126#u8],by rfl⟩
def limbs08 : QM31Limbs := ![⟨41204271,by change 41204271<2147483647;omega⟩,⟨1141310375,by change 1141310375<2147483647;omega⟩,⟨1214211036,by change 1214211036<2147483647;omega⟩,⟨2117549352,by change 2117549352<2147483647;omega⟩]
theorem rawCell08 : (raw.drop 128).take 16=cell08.val := by
  simp only [raw,JFz_Scan56.data,JFz_Scan56.j00,JFz_Scan56.j01,JFz_Scan56.j02,JFz_Scan56.j03,JFz_Scan56.j04,JFz_Scan56.j05,JFz_Scan56.j06,JFz_Scan56.j07,JFz_Scan56.j08,JFz_Scan56.j09,JFz_Scan56.j10,JFz_Scan56.j11,JFz_Scan56.j12,JFz_Scan56.b00_length,JFz_Scan56.b01_length,JFz_Scan56.b02_length,JFz_Scan56.b03_length,JFz_Scan56.b04_length,JFz_Scan56.b05_length,JFz_Scan56.b06_length,JFz_Scan56.b07_length,JFz_Scan56.b08_length,JFz_Scan56.b09_length,JFz_Scan56.b10_length,JFz_Scan56.b11_length,JFz_Scan56.b12_length,JFz_Scan56.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell08
theorem encoded08 : CandidateParserByteOrder.arrayBytes16 cell08=encodeQM31LE limbs08 := by
  funext i
  fin_cases i <;> rfl
theorem parser08 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell08)=
    ok (some ⟨⟨41204271#u32,1141310375#u32⟩,⟨1214211036#u32,2117549352#u32⟩⟩) :=
  JFr_EncodedCell.parser cell08 limbs08 encoded08
#print axioms encoded08
#print axioms parser08
def cell09 : Array U8 16#usize := ⟨[242#u8,240#u8,247#u8,12#u8,162#u8,121#u8,102#u8,94#u8,237#u8,254#u8,165#u8,71#u8,235#u8,50#u8,107#u8,29#u8],by rfl⟩
def limbs09 : QM31Limbs := ![⟨217575666,by change 217575666<2147483647;omega⟩,⟨1583774114,by change 1583774114<2147483647;omega⟩,⟨1202061037,by change 1202061037<2147483647;omega⟩,⟨493564651,by change 493564651<2147483647;omega⟩]
theorem rawCell09 : (raw.drop 144).take 16=cell09.val := by
  simp only [raw,JFz_Scan56.data,JFz_Scan56.j00,JFz_Scan56.j01,JFz_Scan56.j02,JFz_Scan56.j03,JFz_Scan56.j04,JFz_Scan56.j05,JFz_Scan56.j06,JFz_Scan56.j07,JFz_Scan56.j08,JFz_Scan56.j09,JFz_Scan56.j10,JFz_Scan56.j11,JFz_Scan56.j12,JFz_Scan56.b00_length,JFz_Scan56.b01_length,JFz_Scan56.b02_length,JFz_Scan56.b03_length,JFz_Scan56.b04_length,JFz_Scan56.b05_length,JFz_Scan56.b06_length,JFz_Scan56.b07_length,JFz_Scan56.b08_length,JFz_Scan56.b09_length,JFz_Scan56.b10_length,JFz_Scan56.b11_length,JFz_Scan56.b12_length,JFz_Scan56.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell09
theorem encoded09 : CandidateParserByteOrder.arrayBytes16 cell09=encodeQM31LE limbs09 := by
  funext i
  fin_cases i <;> rfl
theorem parser09 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell09)=
    ok (some ⟨⟨217575666#u32,1583774114#u32⟩,⟨1202061037#u32,493564651#u32⟩⟩) :=
  JFr_EncodedCell.parser cell09 limbs09 encoded09
#print axioms encoded09
#print axioms parser09
def cell10 : Array U8 16#usize := ⟨[165#u8,250#u8,246#u8,26#u8,87#u8,167#u8,222#u8,107#u8,52#u8,62#u8,24#u8,98#u8,185#u8,182#u8,112#u8,54#u8],by rfl⟩
def limbs10 : QM31Limbs := ![⟨452393637,by change 452393637<2147483647;omega⟩,⟨1809753943,by change 1809753943<2147483647;omega⟩,⟨1645755956,by change 1645755956<2147483647;omega⟩,⟨913356473,by change 913356473<2147483647;omega⟩]
theorem rawCell10 : (raw.drop 160).take 16=cell10.val := by
  simp only [raw,JFz_Scan56.data,JFz_Scan56.j00,JFz_Scan56.j01,JFz_Scan56.j02,JFz_Scan56.j03,JFz_Scan56.j04,JFz_Scan56.j05,JFz_Scan56.j06,JFz_Scan56.j07,JFz_Scan56.j08,JFz_Scan56.j09,JFz_Scan56.j10,JFz_Scan56.j11,JFz_Scan56.j12,JFz_Scan56.b00_length,JFz_Scan56.b01_length,JFz_Scan56.b02_length,JFz_Scan56.b03_length,JFz_Scan56.b04_length,JFz_Scan56.b05_length,JFz_Scan56.b06_length,JFz_Scan56.b07_length,JFz_Scan56.b08_length,JFz_Scan56.b09_length,JFz_Scan56.b10_length,JFz_Scan56.b11_length,JFz_Scan56.b12_length,JFz_Scan56.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell10
theorem encoded10 : CandidateParserByteOrder.arrayBytes16 cell10=encodeQM31LE limbs10 := by
  funext i
  fin_cases i <;> rfl
theorem parser10 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell10)=
    ok (some ⟨⟨452393637#u32,1809753943#u32⟩,⟨1645755956#u32,913356473#u32⟩⟩) :=
  JFr_EncodedCell.parser cell10 limbs10 encoded10
#print axioms encoded10
#print axioms parser10
def cell11 : Array U8 16#usize := ⟨[143#u8,70#u8,218#u8,127#u8,77#u8,230#u8,185#u8,24#u8,30#u8,91#u8,113#u8,64#u8,54#u8,133#u8,16#u8,104#u8],by rfl⟩
def limbs11 : QM31Limbs := ![⟨2145011343,by change 2145011343<2147483647;omega⟩,⟨414836301,by change 414836301<2147483647;omega⟩,⟨1081170718,by change 1081170718<2147483647;omega⟩,⟨1745913142,by change 1745913142<2147483647;omega⟩]
theorem rawCell11 : (raw.drop 176).take 16=cell11.val := by
  simp only [raw,JFz_Scan56.data,JFz_Scan56.j00,JFz_Scan56.j01,JFz_Scan56.j02,JFz_Scan56.j03,JFz_Scan56.j04,JFz_Scan56.j05,JFz_Scan56.j06,JFz_Scan56.j07,JFz_Scan56.j08,JFz_Scan56.j09,JFz_Scan56.j10,JFz_Scan56.j11,JFz_Scan56.j12,JFz_Scan56.b00_length,JFz_Scan56.b01_length,JFz_Scan56.b02_length,JFz_Scan56.b03_length,JFz_Scan56.b04_length,JFz_Scan56.b05_length,JFz_Scan56.b06_length,JFz_Scan56.b07_length,JFz_Scan56.b08_length,JFz_Scan56.b09_length,JFz_Scan56.b10_length,JFz_Scan56.b11_length,JFz_Scan56.b12_length,JFz_Scan56.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell11
theorem encoded11 : CandidateParserByteOrder.arrayBytes16 cell11=encodeQM31LE limbs11 := by
  funext i
  fin_cases i <;> rfl
theorem parser11 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell11)=
    ok (some ⟨⟨2145011343#u32,414836301#u32⟩,⟨1081170718#u32,1745913142#u32⟩⟩) :=
  JFr_EncodedCell.parser cell11 limbs11 encoded11
#print axioms encoded11
#print axioms parser11
def cell12 : Array U8 16#usize := ⟨[30#u8,103#u8,105#u8,15#u8,12#u8,232#u8,159#u8,62#u8,207#u8,172#u8,88#u8,101#u8,62#u8,193#u8,122#u8,20#u8],by rfl⟩
def limbs12 : QM31Limbs := ![⟨258565918,by change 258565918<2147483647;omega⟩,⟨1050667020,by change 1050667020<2147483647;omega⟩,⟨1700310223,by change 1700310223<2147483647;omega⟩,⟨343589182,by change 343589182<2147483647;omega⟩]
theorem rawCell12 : (raw.drop 192).take 16=cell12.val := by
  simp only [raw,JFz_Scan56.data,JFz_Scan56.j00,JFz_Scan56.j01,JFz_Scan56.j02,JFz_Scan56.j03,JFz_Scan56.j04,JFz_Scan56.j05,JFz_Scan56.j06,JFz_Scan56.j07,JFz_Scan56.j08,JFz_Scan56.j09,JFz_Scan56.j10,JFz_Scan56.j11,JFz_Scan56.j12,JFz_Scan56.b00_length,JFz_Scan56.b01_length,JFz_Scan56.b02_length,JFz_Scan56.b03_length,JFz_Scan56.b04_length,JFz_Scan56.b05_length,JFz_Scan56.b06_length,JFz_Scan56.b07_length,JFz_Scan56.b08_length,JFz_Scan56.b09_length,JFz_Scan56.b10_length,JFz_Scan56.b11_length,JFz_Scan56.b12_length,JFz_Scan56.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell12
theorem encoded12 : CandidateParserByteOrder.arrayBytes16 cell12=encodeQM31LE limbs12 := by
  funext i
  fin_cases i <;> rfl
theorem parser12 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell12)=
    ok (some ⟨⟨258565918#u32,1050667020#u32⟩,⟨1700310223#u32,343589182#u32⟩⟩) :=
  JFr_EncodedCell.parser cell12 limbs12 encoded12
#print axioms encoded12
#print axioms parser12
def cell13 : Array U8 16#usize := ⟨[94#u8,180#u8,49#u8,36#u8,193#u8,155#u8,180#u8,19#u8,115#u8,19#u8,196#u8,21#u8,91#u8,114#u8,222#u8,7#u8],by rfl⟩
def limbs13 : QM31Limbs := ![⟨607237214,by change 607237214<2147483647;omega⟩,⟨330603457,by change 330603457<2147483647;omega⟩,⟨365171571,by change 365171571<2147483647;omega⟩,⟨132018779,by change 132018779<2147483647;omega⟩]
theorem rawCell13 : (raw.drop 208).take 16=cell13.val := by
  simp only [raw,JFz_Scan56.data,JFz_Scan56.j00,JFz_Scan56.j01,JFz_Scan56.j02,JFz_Scan56.j03,JFz_Scan56.j04,JFz_Scan56.j05,JFz_Scan56.j06,JFz_Scan56.j07,JFz_Scan56.j08,JFz_Scan56.j09,JFz_Scan56.j10,JFz_Scan56.j11,JFz_Scan56.j12,JFz_Scan56.b00_length,JFz_Scan56.b01_length,JFz_Scan56.b02_length,JFz_Scan56.b03_length,JFz_Scan56.b04_length,JFz_Scan56.b05_length,JFz_Scan56.b06_length,JFz_Scan56.b07_length,JFz_Scan56.b08_length,JFz_Scan56.b09_length,JFz_Scan56.b10_length,JFz_Scan56.b11_length,JFz_Scan56.b12_length,JFz_Scan56.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell13
theorem encoded13 : CandidateParserByteOrder.arrayBytes16 cell13=encodeQM31LE limbs13 := by
  funext i
  fin_cases i <;> rfl
theorem parser13 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell13)=
    ok (some ⟨⟨607237214#u32,330603457#u32⟩,⟨365171571#u32,132018779#u32⟩⟩) :=
  JFr_EncodedCell.parser cell13 limbs13 encoded13
#print axioms encoded13
#print axioms parser13
def cell14 : Array U8 16#usize := ⟨[113#u8,27#u8,201#u8,61#u8,163#u8,119#u8,80#u8,90#u8,227#u8,30#u8,121#u8,53#u8,76#u8,223#u8,184#u8,11#u8],by rfl⟩
def limbs14 : QM31Limbs := ![⟨1036589937,by change 1036589937<2147483647;omega⟩,⟨1515222947,by change 1515222947<2147483647;omega⟩,⟨897130211,by change 897130211<2147483647;omega⟩,⟨196665164,by change 196665164<2147483647;omega⟩]
theorem rawCell14 : (raw.drop 224).take 16=cell14.val := by
  simp only [raw,JFz_Scan56.data,JFz_Scan56.j00,JFz_Scan56.j01,JFz_Scan56.j02,JFz_Scan56.j03,JFz_Scan56.j04,JFz_Scan56.j05,JFz_Scan56.j06,JFz_Scan56.j07,JFz_Scan56.j08,JFz_Scan56.j09,JFz_Scan56.j10,JFz_Scan56.j11,JFz_Scan56.j12,JFz_Scan56.b00_length,JFz_Scan56.b01_length,JFz_Scan56.b02_length,JFz_Scan56.b03_length,JFz_Scan56.b04_length,JFz_Scan56.b05_length,JFz_Scan56.b06_length,JFz_Scan56.b07_length,JFz_Scan56.b08_length,JFz_Scan56.b09_length,JFz_Scan56.b10_length,JFz_Scan56.b11_length,JFz_Scan56.b12_length,JFz_Scan56.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell14
theorem encoded14 : CandidateParserByteOrder.arrayBytes16 cell14=encodeQM31LE limbs14 := by
  funext i
  fin_cases i <;> rfl
theorem parser14 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell14)=
    ok (some ⟨⟨1036589937#u32,1515222947#u32⟩,⟨897130211#u32,196665164#u32⟩⟩) :=
  JFr_EncodedCell.parser cell14 limbs14 encoded14
#print axioms encoded14
#print axioms parser14
def cell15 : Array U8 16#usize := ⟨[46#u8,105#u8,254#u8,0#u8,24#u8,3#u8,100#u8,86#u8,29#u8,173#u8,167#u8,77#u8,205#u8,140#u8,221#u8,81#u8],by rfl⟩
def limbs15 : QM31Limbs := ![⟨16673070,by change 16673070<2147483647;omega⟩,⟨1449394968,by change 1449394968<2147483647;omega⟩,⟨1302834461,by change 1302834461<2147483647;omega⟩,⟨1373473997,by change 1373473997<2147483647;omega⟩]
theorem rawCell15 : (raw.drop 240).take 16=cell15.val := by
  simp only [raw,JFz_Scan56.data,JFz_Scan56.j00,JFz_Scan56.j01,JFz_Scan56.j02,JFz_Scan56.j03,JFz_Scan56.j04,JFz_Scan56.j05,JFz_Scan56.j06,JFz_Scan56.j07,JFz_Scan56.j08,JFz_Scan56.j09,JFz_Scan56.j10,JFz_Scan56.j11,JFz_Scan56.j12,JFz_Scan56.b00_length,JFz_Scan56.b01_length,JFz_Scan56.b02_length,JFz_Scan56.b03_length,JFz_Scan56.b04_length,JFz_Scan56.b05_length,JFz_Scan56.b06_length,JFz_Scan56.b07_length,JFz_Scan56.b08_length,JFz_Scan56.b09_length,JFz_Scan56.b10_length,JFz_Scan56.b11_length,JFz_Scan56.b12_length,JFz_Scan56.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell15
theorem encoded15 : CandidateParserByteOrder.arrayBytes16 cell15=encodeQM31LE limbs15 := by
  funext i
  fin_cases i <;> rfl
theorem parser15 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell15)=
    ok (some ⟨⟨16673070#u32,1449394968#u32⟩,⟨1302834461#u32,1373473997#u32⟩⟩) :=
  JFr_EncodedCell.parser cell15 limbs15 encoded15
#print axioms encoded15
#print axioms parser15
def cell16 : Array U8 16#usize := ⟨[32#u8,85#u8,230#u8,5#u8,36#u8,5#u8,75#u8,98#u8,183#u8,237#u8,44#u8,74#u8,93#u8,130#u8,108#u8,51#u8],by rfl⟩
def limbs16 : QM31Limbs := ![⟨98981152,by change 98981152<2147483647;omega⟩,⟨1649083684,by change 1649083684<2147483647;omega⟩,⟨1244458423,by change 1244458423<2147483647;omega⟩,⟨862749277,by change 862749277<2147483647;omega⟩]
theorem rawCell16 : (raw.drop 256).take 16=cell16.val := by
  simp only [raw,JFz_Scan56.data,JFz_Scan56.j00,JFz_Scan56.j01,JFz_Scan56.j02,JFz_Scan56.j03,JFz_Scan56.j04,JFz_Scan56.j05,JFz_Scan56.j06,JFz_Scan56.j07,JFz_Scan56.j08,JFz_Scan56.j09,JFz_Scan56.j10,JFz_Scan56.j11,JFz_Scan56.j12,JFz_Scan56.b00_length,JFz_Scan56.b01_length,JFz_Scan56.b02_length,JFz_Scan56.b03_length,JFz_Scan56.b04_length,JFz_Scan56.b05_length,JFz_Scan56.b06_length,JFz_Scan56.b07_length,JFz_Scan56.b08_length,JFz_Scan56.b09_length,JFz_Scan56.b10_length,JFz_Scan56.b11_length,JFz_Scan56.b12_length,JFz_Scan56.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell16
theorem encoded16 : CandidateParserByteOrder.arrayBytes16 cell16=encodeQM31LE limbs16 := by
  funext i
  fin_cases i <;> rfl
theorem parser16 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell16)=
    ok (some ⟨⟨98981152#u32,1649083684#u32⟩,⟨1244458423#u32,862749277#u32⟩⟩) :=
  JFr_EncodedCell.parser cell16 limbs16 encoded16
#print axioms encoded16
#print axioms parser16
def cell17 : Array U8 16#usize := ⟨[148#u8,55#u8,10#u8,77#u8,210#u8,102#u8,30#u8,20#u8,49#u8,95#u8,117#u8,23#u8,228#u8,215#u8,253#u8,74#u8],by rfl⟩
def limbs17 : QM31Limbs := ![⟨1292515220,by change 1292515220<2147483647;omega⟩,⟨337536722,by change 337536722<2147483647;omega⟩,⟨393568049,by change 393568049<2147483647;omega⟩,⟨1258149860,by change 1258149860<2147483647;omega⟩]
theorem rawCell17 : (raw.drop 272).take 16=cell17.val := by
  simp only [raw,JFz_Scan56.data,JFz_Scan56.j00,JFz_Scan56.j01,JFz_Scan56.j02,JFz_Scan56.j03,JFz_Scan56.j04,JFz_Scan56.j05,JFz_Scan56.j06,JFz_Scan56.j07,JFz_Scan56.j08,JFz_Scan56.j09,JFz_Scan56.j10,JFz_Scan56.j11,JFz_Scan56.j12,JFz_Scan56.b00_length,JFz_Scan56.b01_length,JFz_Scan56.b02_length,JFz_Scan56.b03_length,JFz_Scan56.b04_length,JFz_Scan56.b05_length,JFz_Scan56.b06_length,JFz_Scan56.b07_length,JFz_Scan56.b08_length,JFz_Scan56.b09_length,JFz_Scan56.b10_length,JFz_Scan56.b11_length,JFz_Scan56.b12_length,JFz_Scan56.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell17
theorem encoded17 : CandidateParserByteOrder.arrayBytes16 cell17=encodeQM31LE limbs17 := by
  funext i
  fin_cases i <;> rfl
theorem parser17 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell17)=
    ok (some ⟨⟨1292515220#u32,337536722#u32⟩,⟨393568049#u32,1258149860#u32⟩⟩) :=
  JFr_EncodedCell.parser cell17 limbs17 encoded17
#print axioms encoded17
#print axioms parser17
def cell18 : Array U8 16#usize := ⟨[22#u8,186#u8,154#u8,72#u8,118#u8,20#u8,132#u8,57#u8,84#u8,255#u8,133#u8,19#u8,53#u8,118#u8,2#u8,106#u8],by rfl⟩
def limbs18 : QM31Limbs := ![⟨1218099734,by change 1218099734<2147483647;omega⟩,⟨964957302,by change 964957302<2147483647;omega⟩,⟨327548756,by change 327548756<2147483647;omega⟩,⟨1778546229,by change 1778546229<2147483647;omega⟩]
theorem rawCell18 : (raw.drop 288).take 16=cell18.val := by
  simp only [raw,JFz_Scan56.data,JFz_Scan56.j00,JFz_Scan56.j01,JFz_Scan56.j02,JFz_Scan56.j03,JFz_Scan56.j04,JFz_Scan56.j05,JFz_Scan56.j06,JFz_Scan56.j07,JFz_Scan56.j08,JFz_Scan56.j09,JFz_Scan56.j10,JFz_Scan56.j11,JFz_Scan56.j12,JFz_Scan56.b00_length,JFz_Scan56.b01_length,JFz_Scan56.b02_length,JFz_Scan56.b03_length,JFz_Scan56.b04_length,JFz_Scan56.b05_length,JFz_Scan56.b06_length,JFz_Scan56.b07_length,JFz_Scan56.b08_length,JFz_Scan56.b09_length,JFz_Scan56.b10_length,JFz_Scan56.b11_length,JFz_Scan56.b12_length,JFz_Scan56.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell18
theorem encoded18 : CandidateParserByteOrder.arrayBytes16 cell18=encodeQM31LE limbs18 := by
  funext i
  fin_cases i <;> rfl
theorem parser18 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell18)=
    ok (some ⟨⟨1218099734#u32,964957302#u32⟩,⟨327548756#u32,1778546229#u32⟩⟩) :=
  JFr_EncodedCell.parser cell18 limbs18 encoded18
#print axioms encoded18
#print axioms parser18
def cell19 : Array U8 16#usize := ⟨[149#u8,167#u8,153#u8,25#u8,107#u8,154#u8,48#u8,106#u8,230#u8,55#u8,23#u8,55#u8,137#u8,129#u8,198#u8,99#u8],by rfl⟩
def limbs19 : QM31Limbs := ![⟨429500309,by change 429500309<2147483647;omega⟩,⟨1781570155,by change 1781570155<2147483647;omega⟩,⟨924268518,by change 924268518<2147483647;omega⟩,⟨1673953673,by change 1673953673<2147483647;omega⟩]
theorem rawCell19 : (raw.drop 304).take 16=cell19.val := by
  simp only [raw,JFz_Scan56.data,JFz_Scan56.j00,JFz_Scan56.j01,JFz_Scan56.j02,JFz_Scan56.j03,JFz_Scan56.j04,JFz_Scan56.j05,JFz_Scan56.j06,JFz_Scan56.j07,JFz_Scan56.j08,JFz_Scan56.j09,JFz_Scan56.j10,JFz_Scan56.j11,JFz_Scan56.j12,JFz_Scan56.b00_length,JFz_Scan56.b01_length,JFz_Scan56.b02_length,JFz_Scan56.b03_length,JFz_Scan56.b04_length,JFz_Scan56.b05_length,JFz_Scan56.b06_length,JFz_Scan56.b07_length,JFz_Scan56.b08_length,JFz_Scan56.b09_length,JFz_Scan56.b10_length,JFz_Scan56.b11_length,JFz_Scan56.b12_length,JFz_Scan56.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell19
theorem encoded19 : CandidateParserByteOrder.arrayBytes16 cell19=encodeQM31LE limbs19 := by
  funext i
  fin_cases i <;> rfl
theorem parser19 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell19)=
    ok (some ⟨⟨429500309#u32,1781570155#u32⟩,⟨924268518#u32,1673953673#u32⟩⟩) :=
  JFr_EncodedCell.parser cell19 limbs19 encoded19
#print axioms encoded19
#print axioms parser19
def cell20 : Array U8 16#usize := ⟨[204#u8,123#u8,18#u8,18#u8,242#u8,8#u8,37#u8,13#u8,111#u8,104#u8,184#u8,100#u8,55#u8,42#u8,189#u8,70#u8],by rfl⟩
def limbs20 : QM31Limbs := ![⟨303201228,by change 303201228<2147483647;omega⟩,⟨220530930,by change 220530930<2147483647;omega⟩,⟨1689806959,by change 1689806959<2147483647;omega⟩,⟨1186802231,by change 1186802231<2147483647;omega⟩]
theorem rawCell20 : (raw.drop 320).take 16=cell20.val := by
  simp only [raw,JFz_Scan56.data,JFz_Scan56.j00,JFz_Scan56.j01,JFz_Scan56.j02,JFz_Scan56.j03,JFz_Scan56.j04,JFz_Scan56.j05,JFz_Scan56.j06,JFz_Scan56.j07,JFz_Scan56.j08,JFz_Scan56.j09,JFz_Scan56.j10,JFz_Scan56.j11,JFz_Scan56.j12,JFz_Scan56.b00_length,JFz_Scan56.b01_length,JFz_Scan56.b02_length,JFz_Scan56.b03_length,JFz_Scan56.b04_length,JFz_Scan56.b05_length,JFz_Scan56.b06_length,JFz_Scan56.b07_length,JFz_Scan56.b08_length,JFz_Scan56.b09_length,JFz_Scan56.b10_length,JFz_Scan56.b11_length,JFz_Scan56.b12_length,JFz_Scan56.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell20
theorem encoded20 : CandidateParserByteOrder.arrayBytes16 cell20=encodeQM31LE limbs20 := by
  funext i
  fin_cases i <;> rfl
theorem parser20 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell20)=
    ok (some ⟨⟨303201228#u32,220530930#u32⟩,⟨1689806959#u32,1186802231#u32⟩⟩) :=
  JFr_EncodedCell.parser cell20 limbs20 encoded20
#print axioms encoded20
#print axioms parser20
def cell21 : Array U8 16#usize := ⟨[74#u8,9#u8,130#u8,118#u8,31#u8,208#u8,165#u8,53#u8,255#u8,57#u8,50#u8,46#u8,52#u8,210#u8,157#u8,53#u8],by rfl⟩
def limbs21 : QM31Limbs := ![⟨1988233546,by change 1988233546<2147483647;omega⟩,⟨900059167,by change 900059167<2147483647;omega⟩,⟨775043583,by change 775043583<2147483647;omega⟩,⟨899535412,by change 899535412<2147483647;omega⟩]
theorem rawCell21 : (raw.drop 336).take 16=cell21.val := by
  simp only [raw,JFz_Scan56.data,JFz_Scan56.j00,JFz_Scan56.j01,JFz_Scan56.j02,JFz_Scan56.j03,JFz_Scan56.j04,JFz_Scan56.j05,JFz_Scan56.j06,JFz_Scan56.j07,JFz_Scan56.j08,JFz_Scan56.j09,JFz_Scan56.j10,JFz_Scan56.j11,JFz_Scan56.j12,JFz_Scan56.b00_length,JFz_Scan56.b01_length,JFz_Scan56.b02_length,JFz_Scan56.b03_length,JFz_Scan56.b04_length,JFz_Scan56.b05_length,JFz_Scan56.b06_length,JFz_Scan56.b07_length,JFz_Scan56.b08_length,JFz_Scan56.b09_length,JFz_Scan56.b10_length,JFz_Scan56.b11_length,JFz_Scan56.b12_length,JFz_Scan56.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell21
theorem encoded21 : CandidateParserByteOrder.arrayBytes16 cell21=encodeQM31LE limbs21 := by
  funext i
  fin_cases i <;> rfl
theorem parser21 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell21)=
    ok (some ⟨⟨1988233546#u32,900059167#u32⟩,⟨775043583#u32,899535412#u32⟩⟩) :=
  JFr_EncodedCell.parser cell21 limbs21 encoded21
#print axioms encoded21
#print axioms parser21
def cell22 : Array U8 16#usize := ⟨[186#u8,62#u8,184#u8,60#u8,105#u8,215#u8,40#u8,72#u8,227#u8,198#u8,25#u8,47#u8,93#u8,188#u8,169#u8,117#u8],by rfl⟩
def limbs22 : QM31Limbs := ![⟨1018707642,by change 1018707642<2147483647;omega⟩,⟨1210636137,by change 1210636137<2147483647;omega⟩,⟨790218467,by change 790218467<2147483647;omega⟩,⟨1974058077,by change 1974058077<2147483647;omega⟩]
theorem rawCell22 : (raw.drop 352).take 16=cell22.val := by
  simp only [raw,JFz_Scan56.data,JFz_Scan56.j00,JFz_Scan56.j01,JFz_Scan56.j02,JFz_Scan56.j03,JFz_Scan56.j04,JFz_Scan56.j05,JFz_Scan56.j06,JFz_Scan56.j07,JFz_Scan56.j08,JFz_Scan56.j09,JFz_Scan56.j10,JFz_Scan56.j11,JFz_Scan56.j12,JFz_Scan56.b00_length,JFz_Scan56.b01_length,JFz_Scan56.b02_length,JFz_Scan56.b03_length,JFz_Scan56.b04_length,JFz_Scan56.b05_length,JFz_Scan56.b06_length,JFz_Scan56.b07_length,JFz_Scan56.b08_length,JFz_Scan56.b09_length,JFz_Scan56.b10_length,JFz_Scan56.b11_length,JFz_Scan56.b12_length,JFz_Scan56.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell22
theorem encoded22 : CandidateParserByteOrder.arrayBytes16 cell22=encodeQM31LE limbs22 := by
  funext i
  fin_cases i <;> rfl
theorem parser22 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell22)=
    ok (some ⟨⟨1018707642#u32,1210636137#u32⟩,⟨790218467#u32,1974058077#u32⟩⟩) :=
  JFr_EncodedCell.parser cell22 limbs22 encoded22
#print axioms encoded22
#print axioms parser22
def cell23 : Array U8 16#usize := ⟨[15#u8,33#u8,216#u8,109#u8,218#u8,44#u8,155#u8,78#u8,44#u8,6#u8,119#u8,94#u8,41#u8,128#u8,226#u8,57#u8],by rfl⟩
def limbs23 : QM31Limbs := ![⟨1842880783,by change 1842880783<2147483647;omega⟩,⟨1318792410,by change 1318792410<2147483647;omega⟩,⟨1584858668,by change 1584858668<2147483647;omega⟩,⟨971145257,by change 971145257<2147483647;omega⟩]
theorem rawCell23 : (raw.drop 368).take 16=cell23.val := by
  simp only [raw,JFz_Scan56.data,JFz_Scan56.j00,JFz_Scan56.j01,JFz_Scan56.j02,JFz_Scan56.j03,JFz_Scan56.j04,JFz_Scan56.j05,JFz_Scan56.j06,JFz_Scan56.j07,JFz_Scan56.j08,JFz_Scan56.j09,JFz_Scan56.j10,JFz_Scan56.j11,JFz_Scan56.j12,JFz_Scan56.b00_length,JFz_Scan56.b01_length,JFz_Scan56.b02_length,JFz_Scan56.b03_length,JFz_Scan56.b04_length,JFz_Scan56.b05_length,JFz_Scan56.b06_length,JFz_Scan56.b07_length,JFz_Scan56.b08_length,JFz_Scan56.b09_length,JFz_Scan56.b10_length,JFz_Scan56.b11_length,JFz_Scan56.b12_length,JFz_Scan56.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell23
theorem encoded23 : CandidateParserByteOrder.arrayBytes16 cell23=encodeQM31LE limbs23 := by
  funext i
  fin_cases i <;> rfl
theorem parser23 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell23)=
    ok (some ⟨⟨1842880783#u32,1318792410#u32⟩,⟨1584858668#u32,971145257#u32⟩⟩) :=
  JFr_EncodedCell.parser cell23 limbs23 encoded23
#print axioms encoded23
#print axioms parser23
def cell24 : Array U8 16#usize := ⟨[78#u8,33#u8,157#u8,81#u8,149#u8,176#u8,228#u8,119#u8,74#u8,75#u8,10#u8,28#u8,43#u8,138#u8,73#u8,41#u8],by rfl⟩
def limbs24 : QM31Limbs := ![⟨1369252174,by change 1369252174<2147483647;omega⟩,⟨2011476117,by change 2011476117<2147483647;omega⟩,⟨470436682,by change 470436682<2147483647;omega⟩,⟨692685355,by change 692685355<2147483647;omega⟩]
theorem rawCell24 : (raw.drop 384).take 16=cell24.val := by
  simp only [raw,JFz_Scan56.data,JFz_Scan56.j00,JFz_Scan56.j01,JFz_Scan56.j02,JFz_Scan56.j03,JFz_Scan56.j04,JFz_Scan56.j05,JFz_Scan56.j06,JFz_Scan56.j07,JFz_Scan56.j08,JFz_Scan56.j09,JFz_Scan56.j10,JFz_Scan56.j11,JFz_Scan56.j12,JFz_Scan56.b00_length,JFz_Scan56.b01_length,JFz_Scan56.b02_length,JFz_Scan56.b03_length,JFz_Scan56.b04_length,JFz_Scan56.b05_length,JFz_Scan56.b06_length,JFz_Scan56.b07_length,JFz_Scan56.b08_length,JFz_Scan56.b09_length,JFz_Scan56.b10_length,JFz_Scan56.b11_length,JFz_Scan56.b12_length,JFz_Scan56.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell24
theorem encoded24 : CandidateParserByteOrder.arrayBytes16 cell24=encodeQM31LE limbs24 := by
  funext i
  fin_cases i <;> rfl
theorem parser24 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell24)=
    ok (some ⟨⟨1369252174#u32,2011476117#u32⟩,⟨470436682#u32,692685355#u32⟩⟩) :=
  JFr_EncodedCell.parser cell24 limbs24 encoded24
#print axioms encoded24
#print axioms parser24
def cell25 : Array U8 16#usize := ⟨[53#u8,90#u8,74#u8,5#u8,61#u8,217#u8,204#u8,60#u8,108#u8,229#u8,173#u8,66#u8,67#u8,27#u8,228#u8,86#u8],by rfl⟩
def limbs25 : QM31Limbs := ![⟨88758837,by change 88758837<2147483647;omega⟩,⟨1020057917,by change 1020057917<2147483647;omega⟩,⟨1118692716,by change 1118692716<2147483647;omega⟩,⟨1457789763,by change 1457789763<2147483647;omega⟩]
theorem rawCell25 : (raw.drop 400).take 16=cell25.val := by
  simp only [raw,JFz_Scan56.data,JFz_Scan56.j00,JFz_Scan56.j01,JFz_Scan56.j02,JFz_Scan56.j03,JFz_Scan56.j04,JFz_Scan56.j05,JFz_Scan56.j06,JFz_Scan56.j07,JFz_Scan56.j08,JFz_Scan56.j09,JFz_Scan56.j10,JFz_Scan56.j11,JFz_Scan56.j12,JFz_Scan56.b00_length,JFz_Scan56.b01_length,JFz_Scan56.b02_length,JFz_Scan56.b03_length,JFz_Scan56.b04_length,JFz_Scan56.b05_length,JFz_Scan56.b06_length,JFz_Scan56.b07_length,JFz_Scan56.b08_length,JFz_Scan56.b09_length,JFz_Scan56.b10_length,JFz_Scan56.b11_length,JFz_Scan56.b12_length,JFz_Scan56.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell25
theorem encoded25 : CandidateParserByteOrder.arrayBytes16 cell25=encodeQM31LE limbs25 := by
  funext i
  fin_cases i <;> rfl
theorem parser25 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell25)=
    ok (some ⟨⟨88758837#u32,1020057917#u32⟩,⟨1118692716#u32,1457789763#u32⟩⟩) :=
  JFr_EncodedCell.parser cell25 limbs25 encoded25
#print axioms encoded25
#print axioms parser25
def cell26 : Array U8 16#usize := ⟨[144#u8,11#u8,148#u8,121#u8,175#u8,230#u8,40#u8,94#u8,180#u8,174#u8,154#u8,43#u8,101#u8,39#u8,107#u8,126#u8],by rfl⟩
def limbs26 : QM31Limbs := ![⟨2039745424,by change 2039745424<2147483647;omega⟩,⟨1579738799,by change 1579738799<2147483647;omega⟩,⟨731557556,by change 731557556<2147483647;omega⟩,⟨2120951653,by change 2120951653<2147483647;omega⟩]
theorem rawCell26 : (raw.drop 416).take 16=cell26.val := by
  simp only [raw,JFz_Scan56.data,JFz_Scan56.j00,JFz_Scan56.j01,JFz_Scan56.j02,JFz_Scan56.j03,JFz_Scan56.j04,JFz_Scan56.j05,JFz_Scan56.j06,JFz_Scan56.j07,JFz_Scan56.j08,JFz_Scan56.j09,JFz_Scan56.j10,JFz_Scan56.j11,JFz_Scan56.j12,JFz_Scan56.b00_length,JFz_Scan56.b01_length,JFz_Scan56.b02_length,JFz_Scan56.b03_length,JFz_Scan56.b04_length,JFz_Scan56.b05_length,JFz_Scan56.b06_length,JFz_Scan56.b07_length,JFz_Scan56.b08_length,JFz_Scan56.b09_length,JFz_Scan56.b10_length,JFz_Scan56.b11_length,JFz_Scan56.b12_length,JFz_Scan56.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell26
theorem encoded26 : CandidateParserByteOrder.arrayBytes16 cell26=encodeQM31LE limbs26 := by
  funext i
  fin_cases i <;> rfl
theorem parser26 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell26)=
    ok (some ⟨⟨2039745424#u32,1579738799#u32⟩,⟨731557556#u32,2120951653#u32⟩⟩) :=
  JFr_EncodedCell.parser cell26 limbs26 encoded26
#print axioms encoded26
#print axioms parser26
def cell27 : Array U8 16#usize := ⟨[226#u8,151#u8,214#u8,94#u8,203#u8,244#u8,72#u8,40#u8,214#u8,133#u8,121#u8,9#u8,151#u8,223#u8,108#u8,9#u8],by rfl⟩
def limbs27 : QM31Limbs := ![⟨1591121890,by change 1591121890<2147483647;omega⟩,⟨675869899,by change 675869899<2147483647;omega⟩,⟨158959062,by change 158959062<2147483647;omega⟩,⟨158130071,by change 158130071<2147483647;omega⟩]
theorem rawCell27 : (raw.drop 432).take 16=cell27.val := by
  simp only [raw,JFz_Scan56.data,JFz_Scan56.j00,JFz_Scan56.j01,JFz_Scan56.j02,JFz_Scan56.j03,JFz_Scan56.j04,JFz_Scan56.j05,JFz_Scan56.j06,JFz_Scan56.j07,JFz_Scan56.j08,JFz_Scan56.j09,JFz_Scan56.j10,JFz_Scan56.j11,JFz_Scan56.j12,JFz_Scan56.b00_length,JFz_Scan56.b01_length,JFz_Scan56.b02_length,JFz_Scan56.b03_length,JFz_Scan56.b04_length,JFz_Scan56.b05_length,JFz_Scan56.b06_length,JFz_Scan56.b07_length,JFz_Scan56.b08_length,JFz_Scan56.b09_length,JFz_Scan56.b10_length,JFz_Scan56.b11_length,JFz_Scan56.b12_length,JFz_Scan56.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell27
theorem encoded27 : CandidateParserByteOrder.arrayBytes16 cell27=encodeQM31LE limbs27 := by
  funext i
  fin_cases i <;> rfl
theorem parser27 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell27)=
    ok (some ⟨⟨1591121890#u32,675869899#u32⟩,⟨158959062#u32,158130071#u32⟩⟩) :=
  JFr_EncodedCell.parser cell27 limbs27 encoded27
#print axioms encoded27
#print axioms parser27
end AspisR1.JFr_Bytes08
