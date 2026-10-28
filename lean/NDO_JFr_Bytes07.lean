import NDO_JFr_Data07
import NDO_JFr_EncodedCell
import NDO_JFz_Scan55
set_option autoImplicit false
namespace AspisR1.JFr_Bytes07
open Aeneas Aeneas.Std Result RetainedFieldByteCodec
open AspisR1PublicPreparation
open AspisS1ExtractedRoundChildren
def raw : List U8 := JFz_Scan55.data
theorem rawLength : raw.length=448 := JFz_Scan55.length
#print axioms rawLength
theorem selected : (JFx_NativeBytes.proof.val.drop 3347).take 448=raw := JFz_Scan55.selected
#print axioms selected
def cell00 : Array U8 16#usize := ⟨[234#u8,46#u8,62#u8,7#u8,37#u8,196#u8,33#u8,126#u8,26#u8,78#u8,53#u8,6#u8,88#u8,231#u8,135#u8,63#u8],by rfl⟩
def limbs00 : QM31Limbs := ![⟨121515754,by change 121515754<2147483647;omega⟩,⟨2116142117,by change 2116142117<2147483647;omega⟩,⟨104156698,by change 104156698<2147483647;omega⟩,⟨1065871192,by change 1065871192<2147483647;omega⟩]
theorem rawCell00 : (raw.drop 0).take 16=cell00.val := by
  simp only [raw,JFz_Scan55.data,JFz_Scan55.j00,JFz_Scan55.j01,JFz_Scan55.j02,JFz_Scan55.j03,JFz_Scan55.j04,JFz_Scan55.j05,JFz_Scan55.j06,JFz_Scan55.j07,JFz_Scan55.j08,JFz_Scan55.j09,JFz_Scan55.j10,JFz_Scan55.j11,JFz_Scan55.j12,JFz_Scan55.b00_length,JFz_Scan55.b01_length,JFz_Scan55.b02_length,JFz_Scan55.b03_length,JFz_Scan55.b04_length,JFz_Scan55.b05_length,JFz_Scan55.b06_length,JFz_Scan55.b07_length,JFz_Scan55.b08_length,JFz_Scan55.b09_length,JFz_Scan55.b10_length,JFz_Scan55.b11_length,JFz_Scan55.b12_length,JFz_Scan55.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell00
theorem encoded00 : CandidateParserByteOrder.arrayBytes16 cell00=encodeQM31LE limbs00 := by
  funext i
  fin_cases i <;> rfl
theorem parser00 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell00)=
    ok (some ⟨⟨121515754#u32,2116142117#u32⟩,⟨104156698#u32,1065871192#u32⟩⟩) :=
  JFr_EncodedCell.parser cell00 limbs00 encoded00
#print axioms encoded00
#print axioms parser00
def cell01 : Array U8 16#usize := ⟨[75#u8,255#u8,250#u8,93#u8,221#u8,241#u8,242#u8,5#u8,155#u8,249#u8,253#u8,64#u8,29#u8,218#u8,242#u8,82#u8],by rfl⟩
def limbs01 : QM31Limbs := ![⟨1576730443,by change 1576730443<2147483647;omega⟩,⟨99807709,by change 99807709<2147483647;omega⟩,⟨1090386331,by change 1090386331<2147483647;omega⟩,⟨1391647261,by change 1391647261<2147483647;omega⟩]
theorem rawCell01 : (raw.drop 16).take 16=cell01.val := by
  simp only [raw,JFz_Scan55.data,JFz_Scan55.j00,JFz_Scan55.j01,JFz_Scan55.j02,JFz_Scan55.j03,JFz_Scan55.j04,JFz_Scan55.j05,JFz_Scan55.j06,JFz_Scan55.j07,JFz_Scan55.j08,JFz_Scan55.j09,JFz_Scan55.j10,JFz_Scan55.j11,JFz_Scan55.j12,JFz_Scan55.b00_length,JFz_Scan55.b01_length,JFz_Scan55.b02_length,JFz_Scan55.b03_length,JFz_Scan55.b04_length,JFz_Scan55.b05_length,JFz_Scan55.b06_length,JFz_Scan55.b07_length,JFz_Scan55.b08_length,JFz_Scan55.b09_length,JFz_Scan55.b10_length,JFz_Scan55.b11_length,JFz_Scan55.b12_length,JFz_Scan55.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell01
theorem encoded01 : CandidateParserByteOrder.arrayBytes16 cell01=encodeQM31LE limbs01 := by
  funext i
  fin_cases i <;> rfl
theorem parser01 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell01)=
    ok (some ⟨⟨1576730443#u32,99807709#u32⟩,⟨1090386331#u32,1391647261#u32⟩⟩) :=
  JFr_EncodedCell.parser cell01 limbs01 encoded01
#print axioms encoded01
#print axioms parser01
def cell02 : Array U8 16#usize := ⟨[54#u8,13#u8,226#u8,4#u8,152#u8,195#u8,18#u8,37#u8,81#u8,110#u8,200#u8,61#u8,75#u8,94#u8,220#u8,9#u8],by rfl⟩
def limbs02 : QM31Limbs := ![⟨81923382,by change 81923382<2147483647;omega⟩,⟨621986712,by change 621986712<2147483647;omega⟩,⟨1036545617,by change 1036545617<2147483647;omega⟩,⟨165437003,by change 165437003<2147483647;omega⟩]
theorem rawCell02 : (raw.drop 32).take 16=cell02.val := by
  simp only [raw,JFz_Scan55.data,JFz_Scan55.j00,JFz_Scan55.j01,JFz_Scan55.j02,JFz_Scan55.j03,JFz_Scan55.j04,JFz_Scan55.j05,JFz_Scan55.j06,JFz_Scan55.j07,JFz_Scan55.j08,JFz_Scan55.j09,JFz_Scan55.j10,JFz_Scan55.j11,JFz_Scan55.j12,JFz_Scan55.b00_length,JFz_Scan55.b01_length,JFz_Scan55.b02_length,JFz_Scan55.b03_length,JFz_Scan55.b04_length,JFz_Scan55.b05_length,JFz_Scan55.b06_length,JFz_Scan55.b07_length,JFz_Scan55.b08_length,JFz_Scan55.b09_length,JFz_Scan55.b10_length,JFz_Scan55.b11_length,JFz_Scan55.b12_length,JFz_Scan55.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell02
theorem encoded02 : CandidateParserByteOrder.arrayBytes16 cell02=encodeQM31LE limbs02 := by
  funext i
  fin_cases i <;> rfl
theorem parser02 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell02)=
    ok (some ⟨⟨81923382#u32,621986712#u32⟩,⟨1036545617#u32,165437003#u32⟩⟩) :=
  JFr_EncodedCell.parser cell02 limbs02 encoded02
#print axioms encoded02
#print axioms parser02
def cell03 : Array U8 16#usize := ⟨[88#u8,213#u8,82#u8,77#u8,247#u8,82#u8,10#u8,99#u8,117#u8,208#u8,87#u8,121#u8,174#u8,34#u8,58#u8,17#u8],by rfl⟩
def limbs03 : QM31Limbs := ![⟨1297274200,by change 1297274200<2147483647;omega⟩,⟨1661620983,by change 1661620983<2147483647;omega⟩,⟨2035798133,by change 2035798133<2147483647;omega⟩,⟨289022638,by change 289022638<2147483647;omega⟩]
theorem rawCell03 : (raw.drop 48).take 16=cell03.val := by
  simp only [raw,JFz_Scan55.data,JFz_Scan55.j00,JFz_Scan55.j01,JFz_Scan55.j02,JFz_Scan55.j03,JFz_Scan55.j04,JFz_Scan55.j05,JFz_Scan55.j06,JFz_Scan55.j07,JFz_Scan55.j08,JFz_Scan55.j09,JFz_Scan55.j10,JFz_Scan55.j11,JFz_Scan55.j12,JFz_Scan55.b00_length,JFz_Scan55.b01_length,JFz_Scan55.b02_length,JFz_Scan55.b03_length,JFz_Scan55.b04_length,JFz_Scan55.b05_length,JFz_Scan55.b06_length,JFz_Scan55.b07_length,JFz_Scan55.b08_length,JFz_Scan55.b09_length,JFz_Scan55.b10_length,JFz_Scan55.b11_length,JFz_Scan55.b12_length,JFz_Scan55.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell03
theorem encoded03 : CandidateParserByteOrder.arrayBytes16 cell03=encodeQM31LE limbs03 := by
  funext i
  fin_cases i <;> rfl
theorem parser03 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell03)=
    ok (some ⟨⟨1297274200#u32,1661620983#u32⟩,⟨2035798133#u32,289022638#u32⟩⟩) :=
  JFr_EncodedCell.parser cell03 limbs03 encoded03
#print axioms encoded03
#print axioms parser03
def cell04 : Array U8 16#usize := ⟨[5#u8,199#u8,148#u8,119#u8,217#u8,160#u8,113#u8,21#u8,37#u8,133#u8,234#u8,27#u8,150#u8,219#u8,26#u8,34#u8],by rfl⟩
def limbs04 : QM31Limbs := ![⟨2006238981,by change 2006238981<2147483647;omega⟩,⟨359768281,by change 359768281<2147483647;omega⟩,⟨468354341,by change 468354341<2147483647;omega⟩,⟨572185494,by change 572185494<2147483647;omega⟩]
theorem rawCell04 : (raw.drop 64).take 16=cell04.val := by
  simp only [raw,JFz_Scan55.data,JFz_Scan55.j00,JFz_Scan55.j01,JFz_Scan55.j02,JFz_Scan55.j03,JFz_Scan55.j04,JFz_Scan55.j05,JFz_Scan55.j06,JFz_Scan55.j07,JFz_Scan55.j08,JFz_Scan55.j09,JFz_Scan55.j10,JFz_Scan55.j11,JFz_Scan55.j12,JFz_Scan55.b00_length,JFz_Scan55.b01_length,JFz_Scan55.b02_length,JFz_Scan55.b03_length,JFz_Scan55.b04_length,JFz_Scan55.b05_length,JFz_Scan55.b06_length,JFz_Scan55.b07_length,JFz_Scan55.b08_length,JFz_Scan55.b09_length,JFz_Scan55.b10_length,JFz_Scan55.b11_length,JFz_Scan55.b12_length,JFz_Scan55.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell04
theorem encoded04 : CandidateParserByteOrder.arrayBytes16 cell04=encodeQM31LE limbs04 := by
  funext i
  fin_cases i <;> rfl
theorem parser04 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell04)=
    ok (some ⟨⟨2006238981#u32,359768281#u32⟩,⟨468354341#u32,572185494#u32⟩⟩) :=
  JFr_EncodedCell.parser cell04 limbs04 encoded04
#print axioms encoded04
#print axioms parser04
def cell05 : Array U8 16#usize := ⟨[251#u8,112#u8,255#u8,125#u8,151#u8,161#u8,30#u8,110#u8,71#u8,26#u8,142#u8,12#u8,202#u8,6#u8,21#u8,21#u8],by rfl⟩
def limbs05 : QM31Limbs := ![⟨2113892603,by change 2113892603<2147483647;omega⟩,⟨1847501207,by change 1847501207<2147483647;omega⟩,⟨210639431,by change 210639431<2147483647;omega⟩,⟨353699530,by change 353699530<2147483647;omega⟩]
theorem rawCell05 : (raw.drop 80).take 16=cell05.val := by
  simp only [raw,JFz_Scan55.data,JFz_Scan55.j00,JFz_Scan55.j01,JFz_Scan55.j02,JFz_Scan55.j03,JFz_Scan55.j04,JFz_Scan55.j05,JFz_Scan55.j06,JFz_Scan55.j07,JFz_Scan55.j08,JFz_Scan55.j09,JFz_Scan55.j10,JFz_Scan55.j11,JFz_Scan55.j12,JFz_Scan55.b00_length,JFz_Scan55.b01_length,JFz_Scan55.b02_length,JFz_Scan55.b03_length,JFz_Scan55.b04_length,JFz_Scan55.b05_length,JFz_Scan55.b06_length,JFz_Scan55.b07_length,JFz_Scan55.b08_length,JFz_Scan55.b09_length,JFz_Scan55.b10_length,JFz_Scan55.b11_length,JFz_Scan55.b12_length,JFz_Scan55.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell05
theorem encoded05 : CandidateParserByteOrder.arrayBytes16 cell05=encodeQM31LE limbs05 := by
  funext i
  fin_cases i <;> rfl
theorem parser05 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell05)=
    ok (some ⟨⟨2113892603#u32,1847501207#u32⟩,⟨210639431#u32,353699530#u32⟩⟩) :=
  JFr_EncodedCell.parser cell05 limbs05 encoded05
#print axioms encoded05
#print axioms parser05
def cell06 : Array U8 16#usize := ⟨[223#u8,198#u8,135#u8,118#u8,144#u8,10#u8,61#u8,58#u8,176#u8,254#u8,71#u8,63#u8,151#u8,223#u8,249#u8,105#u8],by rfl⟩
def limbs06 : QM31Limbs := ![⟨1988609759,by change 1988609759<2147483647;omega⟩,⟨977078928,by change 977078928<2147483647;omega⟩,⟨1061682864,by change 1061682864<2147483647;omega⟩,⟨1777983383,by change 1777983383<2147483647;omega⟩]
theorem rawCell06 : (raw.drop 96).take 16=cell06.val := by
  simp only [raw,JFz_Scan55.data,JFz_Scan55.j00,JFz_Scan55.j01,JFz_Scan55.j02,JFz_Scan55.j03,JFz_Scan55.j04,JFz_Scan55.j05,JFz_Scan55.j06,JFz_Scan55.j07,JFz_Scan55.j08,JFz_Scan55.j09,JFz_Scan55.j10,JFz_Scan55.j11,JFz_Scan55.j12,JFz_Scan55.b00_length,JFz_Scan55.b01_length,JFz_Scan55.b02_length,JFz_Scan55.b03_length,JFz_Scan55.b04_length,JFz_Scan55.b05_length,JFz_Scan55.b06_length,JFz_Scan55.b07_length,JFz_Scan55.b08_length,JFz_Scan55.b09_length,JFz_Scan55.b10_length,JFz_Scan55.b11_length,JFz_Scan55.b12_length,JFz_Scan55.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell06
theorem encoded06 : CandidateParserByteOrder.arrayBytes16 cell06=encodeQM31LE limbs06 := by
  funext i
  fin_cases i <;> rfl
theorem parser06 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell06)=
    ok (some ⟨⟨1988609759#u32,977078928#u32⟩,⟨1061682864#u32,1777983383#u32⟩⟩) :=
  JFr_EncodedCell.parser cell06 limbs06 encoded06
#print axioms encoded06
#print axioms parser06
def cell07 : Array U8 16#usize := ⟨[169#u8,16#u8,137#u8,90#u8,26#u8,223#u8,229#u8,7#u8,242#u8,126#u8,67#u8,75#u8,246#u8,98#u8,75#u8,90#u8],by rfl⟩
def limbs07 : QM31Limbs := ![⟨1518932137,by change 1518932137<2147483647;omega⟩,⟨132505370,by change 132505370<2147483647;omega⟩,⟨1262714610,by change 1262714610<2147483647;omega⟩,⟨1514889974,by change 1514889974<2147483647;omega⟩]
theorem rawCell07 : (raw.drop 112).take 16=cell07.val := by
  simp only [raw,JFz_Scan55.data,JFz_Scan55.j00,JFz_Scan55.j01,JFz_Scan55.j02,JFz_Scan55.j03,JFz_Scan55.j04,JFz_Scan55.j05,JFz_Scan55.j06,JFz_Scan55.j07,JFz_Scan55.j08,JFz_Scan55.j09,JFz_Scan55.j10,JFz_Scan55.j11,JFz_Scan55.j12,JFz_Scan55.b00_length,JFz_Scan55.b01_length,JFz_Scan55.b02_length,JFz_Scan55.b03_length,JFz_Scan55.b04_length,JFz_Scan55.b05_length,JFz_Scan55.b06_length,JFz_Scan55.b07_length,JFz_Scan55.b08_length,JFz_Scan55.b09_length,JFz_Scan55.b10_length,JFz_Scan55.b11_length,JFz_Scan55.b12_length,JFz_Scan55.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell07
theorem encoded07 : CandidateParserByteOrder.arrayBytes16 cell07=encodeQM31LE limbs07 := by
  funext i
  fin_cases i <;> rfl
theorem parser07 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell07)=
    ok (some ⟨⟨1518932137#u32,132505370#u32⟩,⟨1262714610#u32,1514889974#u32⟩⟩) :=
  JFr_EncodedCell.parser cell07 limbs07 encoded07
#print axioms encoded07
#print axioms parser07
def cell08 : Array U8 16#usize := ⟨[95#u8,201#u8,51#u8,89#u8,216#u8,146#u8,129#u8,60#u8,245#u8,188#u8,133#u8,47#u8,176#u8,36#u8,84#u8,23#u8],by rfl⟩
def limbs08 : QM31Limbs := ![⟨1496566111,by change 1496566111<2147483647;omega⟩,⟨1015124696,by change 1015124696<2147483647;omega⟩,⟨797293813,by change 797293813<2147483647;omega⟩,⟨391390384,by change 391390384<2147483647;omega⟩]
theorem rawCell08 : (raw.drop 128).take 16=cell08.val := by
  simp only [raw,JFz_Scan55.data,JFz_Scan55.j00,JFz_Scan55.j01,JFz_Scan55.j02,JFz_Scan55.j03,JFz_Scan55.j04,JFz_Scan55.j05,JFz_Scan55.j06,JFz_Scan55.j07,JFz_Scan55.j08,JFz_Scan55.j09,JFz_Scan55.j10,JFz_Scan55.j11,JFz_Scan55.j12,JFz_Scan55.b00_length,JFz_Scan55.b01_length,JFz_Scan55.b02_length,JFz_Scan55.b03_length,JFz_Scan55.b04_length,JFz_Scan55.b05_length,JFz_Scan55.b06_length,JFz_Scan55.b07_length,JFz_Scan55.b08_length,JFz_Scan55.b09_length,JFz_Scan55.b10_length,JFz_Scan55.b11_length,JFz_Scan55.b12_length,JFz_Scan55.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell08
theorem encoded08 : CandidateParserByteOrder.arrayBytes16 cell08=encodeQM31LE limbs08 := by
  funext i
  fin_cases i <;> rfl
theorem parser08 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell08)=
    ok (some ⟨⟨1496566111#u32,1015124696#u32⟩,⟨797293813#u32,391390384#u32⟩⟩) :=
  JFr_EncodedCell.parser cell08 limbs08 encoded08
#print axioms encoded08
#print axioms parser08
def cell09 : Array U8 16#usize := ⟨[238#u8,49#u8,180#u8,109#u8,92#u8,34#u8,123#u8,82#u8,235#u8,99#u8,198#u8,108#u8,12#u8,123#u8,241#u8,117#u8],by rfl⟩
def limbs09 : QM31Limbs := ![⟨1840525806,by change 1840525806<2147483647;omega⟩,⟨1383801436,by change 1383801436<2147483647;omega⟩,⟨1824941035,by change 1824941035<2147483647;omega⟩,⟨1978759948,by change 1978759948<2147483647;omega⟩]
theorem rawCell09 : (raw.drop 144).take 16=cell09.val := by
  simp only [raw,JFz_Scan55.data,JFz_Scan55.j00,JFz_Scan55.j01,JFz_Scan55.j02,JFz_Scan55.j03,JFz_Scan55.j04,JFz_Scan55.j05,JFz_Scan55.j06,JFz_Scan55.j07,JFz_Scan55.j08,JFz_Scan55.j09,JFz_Scan55.j10,JFz_Scan55.j11,JFz_Scan55.j12,JFz_Scan55.b00_length,JFz_Scan55.b01_length,JFz_Scan55.b02_length,JFz_Scan55.b03_length,JFz_Scan55.b04_length,JFz_Scan55.b05_length,JFz_Scan55.b06_length,JFz_Scan55.b07_length,JFz_Scan55.b08_length,JFz_Scan55.b09_length,JFz_Scan55.b10_length,JFz_Scan55.b11_length,JFz_Scan55.b12_length,JFz_Scan55.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell09
theorem encoded09 : CandidateParserByteOrder.arrayBytes16 cell09=encodeQM31LE limbs09 := by
  funext i
  fin_cases i <;> rfl
theorem parser09 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell09)=
    ok (some ⟨⟨1840525806#u32,1383801436#u32⟩,⟨1824941035#u32,1978759948#u32⟩⟩) :=
  JFr_EncodedCell.parser cell09 limbs09 encoded09
#print axioms encoded09
#print axioms parser09
def cell10 : Array U8 16#usize := ⟨[254#u8,165#u8,243#u8,110#u8,226#u8,68#u8,9#u8,56#u8,16#u8,220#u8,213#u8,49#u8,204#u8,53#u8,34#u8,32#u8],by rfl⟩
def limbs10 : QM31Limbs := ![⟨1861461502,by change 1861461502<2147483647;omega⟩,⟨940131554,by change 940131554<2147483647;omega⟩,⟨836099088,by change 836099088<2147483647;omega⟩,⟨539112908,by change 539112908<2147483647;omega⟩]
theorem rawCell10 : (raw.drop 160).take 16=cell10.val := by
  simp only [raw,JFz_Scan55.data,JFz_Scan55.j00,JFz_Scan55.j01,JFz_Scan55.j02,JFz_Scan55.j03,JFz_Scan55.j04,JFz_Scan55.j05,JFz_Scan55.j06,JFz_Scan55.j07,JFz_Scan55.j08,JFz_Scan55.j09,JFz_Scan55.j10,JFz_Scan55.j11,JFz_Scan55.j12,JFz_Scan55.b00_length,JFz_Scan55.b01_length,JFz_Scan55.b02_length,JFz_Scan55.b03_length,JFz_Scan55.b04_length,JFz_Scan55.b05_length,JFz_Scan55.b06_length,JFz_Scan55.b07_length,JFz_Scan55.b08_length,JFz_Scan55.b09_length,JFz_Scan55.b10_length,JFz_Scan55.b11_length,JFz_Scan55.b12_length,JFz_Scan55.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell10
theorem encoded10 : CandidateParserByteOrder.arrayBytes16 cell10=encodeQM31LE limbs10 := by
  funext i
  fin_cases i <;> rfl
theorem parser10 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell10)=
    ok (some ⟨⟨1861461502#u32,940131554#u32⟩,⟨836099088#u32,539112908#u32⟩⟩) :=
  JFr_EncodedCell.parser cell10 limbs10 encoded10
#print axioms encoded10
#print axioms parser10
def cell11 : Array U8 16#usize := ⟨[33#u8,11#u8,126#u8,96#u8,7#u8,18#u8,182#u8,22#u8,8#u8,70#u8,167#u8,42#u8,90#u8,4#u8,23#u8,70#u8],by rfl⟩
def limbs11 : QM31Limbs := ![⟨1618873121,by change 1618873121<2147483647;omega⟩,⟨381030919,by change 381030919<2147483647;omega⟩,⟨715605512,by change 715605512<2147483647;omega⟩,⟨1175913562,by change 1175913562<2147483647;omega⟩]
theorem rawCell11 : (raw.drop 176).take 16=cell11.val := by
  simp only [raw,JFz_Scan55.data,JFz_Scan55.j00,JFz_Scan55.j01,JFz_Scan55.j02,JFz_Scan55.j03,JFz_Scan55.j04,JFz_Scan55.j05,JFz_Scan55.j06,JFz_Scan55.j07,JFz_Scan55.j08,JFz_Scan55.j09,JFz_Scan55.j10,JFz_Scan55.j11,JFz_Scan55.j12,JFz_Scan55.b00_length,JFz_Scan55.b01_length,JFz_Scan55.b02_length,JFz_Scan55.b03_length,JFz_Scan55.b04_length,JFz_Scan55.b05_length,JFz_Scan55.b06_length,JFz_Scan55.b07_length,JFz_Scan55.b08_length,JFz_Scan55.b09_length,JFz_Scan55.b10_length,JFz_Scan55.b11_length,JFz_Scan55.b12_length,JFz_Scan55.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell11
theorem encoded11 : CandidateParserByteOrder.arrayBytes16 cell11=encodeQM31LE limbs11 := by
  funext i
  fin_cases i <;> rfl
theorem parser11 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell11)=
    ok (some ⟨⟨1618873121#u32,381030919#u32⟩,⟨715605512#u32,1175913562#u32⟩⟩) :=
  JFr_EncodedCell.parser cell11 limbs11 encoded11
#print axioms encoded11
#print axioms parser11
def cell12 : Array U8 16#usize := ⟨[55#u8,118#u8,243#u8,93#u8,250#u8,219#u8,68#u8,102#u8,200#u8,173#u8,230#u8,27#u8,8#u8,220#u8,225#u8,28#u8],by rfl⟩
def limbs12 : QM31Limbs := ![⟨1576236599,by change 1576236599<2147483647;omega⟩,⟨1715788794,by change 1715788794<2147483647;omega⟩,⟨468102600,by change 468102600<2147483647;omega⟩,⟨484563976,by change 484563976<2147483647;omega⟩]
theorem rawCell12 : (raw.drop 192).take 16=cell12.val := by
  simp only [raw,JFz_Scan55.data,JFz_Scan55.j00,JFz_Scan55.j01,JFz_Scan55.j02,JFz_Scan55.j03,JFz_Scan55.j04,JFz_Scan55.j05,JFz_Scan55.j06,JFz_Scan55.j07,JFz_Scan55.j08,JFz_Scan55.j09,JFz_Scan55.j10,JFz_Scan55.j11,JFz_Scan55.j12,JFz_Scan55.b00_length,JFz_Scan55.b01_length,JFz_Scan55.b02_length,JFz_Scan55.b03_length,JFz_Scan55.b04_length,JFz_Scan55.b05_length,JFz_Scan55.b06_length,JFz_Scan55.b07_length,JFz_Scan55.b08_length,JFz_Scan55.b09_length,JFz_Scan55.b10_length,JFz_Scan55.b11_length,JFz_Scan55.b12_length,JFz_Scan55.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell12
theorem encoded12 : CandidateParserByteOrder.arrayBytes16 cell12=encodeQM31LE limbs12 := by
  funext i
  fin_cases i <;> rfl
theorem parser12 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell12)=
    ok (some ⟨⟨1576236599#u32,1715788794#u32⟩,⟨468102600#u32,484563976#u32⟩⟩) :=
  JFr_EncodedCell.parser cell12 limbs12 encoded12
#print axioms encoded12
#print axioms parser12
def cell13 : Array U8 16#usize := ⟨[68#u8,146#u8,92#u8,123#u8,45#u8,214#u8,197#u8,89#u8,159#u8,179#u8,140#u8,91#u8,225#u8,8#u8,25#u8,4#u8],by rfl⟩
def limbs13 : QM31Limbs := ![⟨2069664324,by change 2069664324<2147483647;omega⟩,⟨1506137645,by change 1506137645<2147483647;omega⟩,⟨1535947679,by change 1535947679<2147483647;omega⟩,⟨68749537,by change 68749537<2147483647;omega⟩]
theorem rawCell13 : (raw.drop 208).take 16=cell13.val := by
  simp only [raw,JFz_Scan55.data,JFz_Scan55.j00,JFz_Scan55.j01,JFz_Scan55.j02,JFz_Scan55.j03,JFz_Scan55.j04,JFz_Scan55.j05,JFz_Scan55.j06,JFz_Scan55.j07,JFz_Scan55.j08,JFz_Scan55.j09,JFz_Scan55.j10,JFz_Scan55.j11,JFz_Scan55.j12,JFz_Scan55.b00_length,JFz_Scan55.b01_length,JFz_Scan55.b02_length,JFz_Scan55.b03_length,JFz_Scan55.b04_length,JFz_Scan55.b05_length,JFz_Scan55.b06_length,JFz_Scan55.b07_length,JFz_Scan55.b08_length,JFz_Scan55.b09_length,JFz_Scan55.b10_length,JFz_Scan55.b11_length,JFz_Scan55.b12_length,JFz_Scan55.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell13
theorem encoded13 : CandidateParserByteOrder.arrayBytes16 cell13=encodeQM31LE limbs13 := by
  funext i
  fin_cases i <;> rfl
theorem parser13 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell13)=
    ok (some ⟨⟨2069664324#u32,1506137645#u32⟩,⟨1535947679#u32,68749537#u32⟩⟩) :=
  JFr_EncodedCell.parser cell13 limbs13 encoded13
#print axioms encoded13
#print axioms parser13
def cell14 : Array U8 16#usize := ⟨[235#u8,62#u8,167#u8,75#u8,226#u8,71#u8,109#u8,41#u8,255#u8,73#u8,175#u8,117#u8,20#u8,192#u8,56#u8,93#u8],by rfl⟩
def limbs14 : QM31Limbs := ![⟨1269251819,by change 1269251819<2147483647;omega⟩,⟨695027682,by change 695027682<2147483647;omega⟩,⟨1974422015,by change 1974422015<2147483647;omega⟩,⟨1564000276,by change 1564000276<2147483647;omega⟩]
theorem rawCell14 : (raw.drop 224).take 16=cell14.val := by
  simp only [raw,JFz_Scan55.data,JFz_Scan55.j00,JFz_Scan55.j01,JFz_Scan55.j02,JFz_Scan55.j03,JFz_Scan55.j04,JFz_Scan55.j05,JFz_Scan55.j06,JFz_Scan55.j07,JFz_Scan55.j08,JFz_Scan55.j09,JFz_Scan55.j10,JFz_Scan55.j11,JFz_Scan55.j12,JFz_Scan55.b00_length,JFz_Scan55.b01_length,JFz_Scan55.b02_length,JFz_Scan55.b03_length,JFz_Scan55.b04_length,JFz_Scan55.b05_length,JFz_Scan55.b06_length,JFz_Scan55.b07_length,JFz_Scan55.b08_length,JFz_Scan55.b09_length,JFz_Scan55.b10_length,JFz_Scan55.b11_length,JFz_Scan55.b12_length,JFz_Scan55.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell14
theorem encoded14 : CandidateParserByteOrder.arrayBytes16 cell14=encodeQM31LE limbs14 := by
  funext i
  fin_cases i <;> rfl
theorem parser14 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell14)=
    ok (some ⟨⟨1269251819#u32,695027682#u32⟩,⟨1974422015#u32,1564000276#u32⟩⟩) :=
  JFr_EncodedCell.parser cell14 limbs14 encoded14
#print axioms encoded14
#print axioms parser14
def cell15 : Array U8 16#usize := ⟨[187#u8,25#u8,233#u8,27#u8,233#u8,190#u8,37#u8,67#u8,2#u8,205#u8,252#u8,47#u8,96#u8,48#u8,221#u8,23#u8],by rfl⟩
def limbs15 : QM31Limbs := ![⟨468261307,by change 468261307<2147483647;omega⟩,⟨1126547177,by change 1126547177<2147483647;omega⟩,⟨805096706,by change 805096706<2147483647;omega⟩,⟨400371808,by change 400371808<2147483647;omega⟩]
theorem rawCell15 : (raw.drop 240).take 16=cell15.val := by
  simp only [raw,JFz_Scan55.data,JFz_Scan55.j00,JFz_Scan55.j01,JFz_Scan55.j02,JFz_Scan55.j03,JFz_Scan55.j04,JFz_Scan55.j05,JFz_Scan55.j06,JFz_Scan55.j07,JFz_Scan55.j08,JFz_Scan55.j09,JFz_Scan55.j10,JFz_Scan55.j11,JFz_Scan55.j12,JFz_Scan55.b00_length,JFz_Scan55.b01_length,JFz_Scan55.b02_length,JFz_Scan55.b03_length,JFz_Scan55.b04_length,JFz_Scan55.b05_length,JFz_Scan55.b06_length,JFz_Scan55.b07_length,JFz_Scan55.b08_length,JFz_Scan55.b09_length,JFz_Scan55.b10_length,JFz_Scan55.b11_length,JFz_Scan55.b12_length,JFz_Scan55.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell15
theorem encoded15 : CandidateParserByteOrder.arrayBytes16 cell15=encodeQM31LE limbs15 := by
  funext i
  fin_cases i <;> rfl
theorem parser15 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell15)=
    ok (some ⟨⟨468261307#u32,1126547177#u32⟩,⟨805096706#u32,400371808#u32⟩⟩) :=
  JFr_EncodedCell.parser cell15 limbs15 encoded15
#print axioms encoded15
#print axioms parser15
def cell16 : Array U8 16#usize := ⟨[0#u8,57#u8,193#u8,17#u8,25#u8,155#u8,173#u8,81#u8,215#u8,243#u8,206#u8,114#u8,47#u8,107#u8,12#u8,56#u8],by rfl⟩
def limbs16 : QM31Limbs := ![⟨297875712,by change 297875712<2147483647;omega⟩,⟨1370331929,by change 1370331929<2147483647;omega⟩,⟨1926165463,by change 1926165463<2147483647;omega⟩,⟨940337967,by change 940337967<2147483647;omega⟩]
theorem rawCell16 : (raw.drop 256).take 16=cell16.val := by
  simp only [raw,JFz_Scan55.data,JFz_Scan55.j00,JFz_Scan55.j01,JFz_Scan55.j02,JFz_Scan55.j03,JFz_Scan55.j04,JFz_Scan55.j05,JFz_Scan55.j06,JFz_Scan55.j07,JFz_Scan55.j08,JFz_Scan55.j09,JFz_Scan55.j10,JFz_Scan55.j11,JFz_Scan55.j12,JFz_Scan55.b00_length,JFz_Scan55.b01_length,JFz_Scan55.b02_length,JFz_Scan55.b03_length,JFz_Scan55.b04_length,JFz_Scan55.b05_length,JFz_Scan55.b06_length,JFz_Scan55.b07_length,JFz_Scan55.b08_length,JFz_Scan55.b09_length,JFz_Scan55.b10_length,JFz_Scan55.b11_length,JFz_Scan55.b12_length,JFz_Scan55.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell16
theorem encoded16 : CandidateParserByteOrder.arrayBytes16 cell16=encodeQM31LE limbs16 := by
  funext i
  fin_cases i <;> rfl
theorem parser16 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell16)=
    ok (some ⟨⟨297875712#u32,1370331929#u32⟩,⟨1926165463#u32,940337967#u32⟩⟩) :=
  JFr_EncodedCell.parser cell16 limbs16 encoded16
#print axioms encoded16
#print axioms parser16
def cell17 : Array U8 16#usize := ⟨[163#u8,55#u8,26#u8,55#u8,214#u8,229#u8,156#u8,28#u8,210#u8,96#u8,154#u8,97#u8,231#u8,118#u8,217#u8,71#u8],by rfl⟩
def limbs17 : QM31Limbs := ![⟨924465059,by change 924465059<2147483647;omega⟩,⟨480044502,by change 480044502<2147483647;omega⟩,⟨1637507282,by change 1637507282<2147483647;omega⟩,⟨1205434087,by change 1205434087<2147483647;omega⟩]
theorem rawCell17 : (raw.drop 272).take 16=cell17.val := by
  simp only [raw,JFz_Scan55.data,JFz_Scan55.j00,JFz_Scan55.j01,JFz_Scan55.j02,JFz_Scan55.j03,JFz_Scan55.j04,JFz_Scan55.j05,JFz_Scan55.j06,JFz_Scan55.j07,JFz_Scan55.j08,JFz_Scan55.j09,JFz_Scan55.j10,JFz_Scan55.j11,JFz_Scan55.j12,JFz_Scan55.b00_length,JFz_Scan55.b01_length,JFz_Scan55.b02_length,JFz_Scan55.b03_length,JFz_Scan55.b04_length,JFz_Scan55.b05_length,JFz_Scan55.b06_length,JFz_Scan55.b07_length,JFz_Scan55.b08_length,JFz_Scan55.b09_length,JFz_Scan55.b10_length,JFz_Scan55.b11_length,JFz_Scan55.b12_length,JFz_Scan55.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell17
theorem encoded17 : CandidateParserByteOrder.arrayBytes16 cell17=encodeQM31LE limbs17 := by
  funext i
  fin_cases i <;> rfl
theorem parser17 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell17)=
    ok (some ⟨⟨924465059#u32,480044502#u32⟩,⟨1637507282#u32,1205434087#u32⟩⟩) :=
  JFr_EncodedCell.parser cell17 limbs17 encoded17
#print axioms encoded17
#print axioms parser17
def cell18 : Array U8 16#usize := ⟨[152#u8,18#u8,55#u8,74#u8,79#u8,111#u8,207#u8,64#u8,211#u8,225#u8,7#u8,4#u8,29#u8,161#u8,99#u8,71#u8],by rfl⟩
def limbs18 : QM31Limbs := ![⟨1245123224,by change 1245123224<2147483647;omega⟩,⟨1087336271,by change 1087336271<2147483647;omega⟩,⟨67625427,by change 67625427<2147483647;omega⟩,⟨1197711645,by change 1197711645<2147483647;omega⟩]
theorem rawCell18 : (raw.drop 288).take 16=cell18.val := by
  simp only [raw,JFz_Scan55.data,JFz_Scan55.j00,JFz_Scan55.j01,JFz_Scan55.j02,JFz_Scan55.j03,JFz_Scan55.j04,JFz_Scan55.j05,JFz_Scan55.j06,JFz_Scan55.j07,JFz_Scan55.j08,JFz_Scan55.j09,JFz_Scan55.j10,JFz_Scan55.j11,JFz_Scan55.j12,JFz_Scan55.b00_length,JFz_Scan55.b01_length,JFz_Scan55.b02_length,JFz_Scan55.b03_length,JFz_Scan55.b04_length,JFz_Scan55.b05_length,JFz_Scan55.b06_length,JFz_Scan55.b07_length,JFz_Scan55.b08_length,JFz_Scan55.b09_length,JFz_Scan55.b10_length,JFz_Scan55.b11_length,JFz_Scan55.b12_length,JFz_Scan55.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell18
theorem encoded18 : CandidateParserByteOrder.arrayBytes16 cell18=encodeQM31LE limbs18 := by
  funext i
  fin_cases i <;> rfl
theorem parser18 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell18)=
    ok (some ⟨⟨1245123224#u32,1087336271#u32⟩,⟨67625427#u32,1197711645#u32⟩⟩) :=
  JFr_EncodedCell.parser cell18 limbs18 encoded18
#print axioms encoded18
#print axioms parser18
def cell19 : Array U8 16#usize := ⟨[8#u8,97#u8,42#u8,113#u8,209#u8,124#u8,176#u8,85#u8,161#u8,166#u8,108#u8,18#u8,144#u8,120#u8,50#u8,89#u8],by rfl⟩
def limbs19 : QM31Limbs := ![⟨1898602760,by change 1898602760<2147483647;omega⟩,⟨1437629649,by change 1437629649<2147483647;omega⟩,⟨309110433,by change 309110433<2147483647;omega⟩,⟨1496479888,by change 1496479888<2147483647;omega⟩]
theorem rawCell19 : (raw.drop 304).take 16=cell19.val := by
  simp only [raw,JFz_Scan55.data,JFz_Scan55.j00,JFz_Scan55.j01,JFz_Scan55.j02,JFz_Scan55.j03,JFz_Scan55.j04,JFz_Scan55.j05,JFz_Scan55.j06,JFz_Scan55.j07,JFz_Scan55.j08,JFz_Scan55.j09,JFz_Scan55.j10,JFz_Scan55.j11,JFz_Scan55.j12,JFz_Scan55.b00_length,JFz_Scan55.b01_length,JFz_Scan55.b02_length,JFz_Scan55.b03_length,JFz_Scan55.b04_length,JFz_Scan55.b05_length,JFz_Scan55.b06_length,JFz_Scan55.b07_length,JFz_Scan55.b08_length,JFz_Scan55.b09_length,JFz_Scan55.b10_length,JFz_Scan55.b11_length,JFz_Scan55.b12_length,JFz_Scan55.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell19
theorem encoded19 : CandidateParserByteOrder.arrayBytes16 cell19=encodeQM31LE limbs19 := by
  funext i
  fin_cases i <;> rfl
theorem parser19 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell19)=
    ok (some ⟨⟨1898602760#u32,1437629649#u32⟩,⟨309110433#u32,1496479888#u32⟩⟩) :=
  JFr_EncodedCell.parser cell19 limbs19 encoded19
#print axioms encoded19
#print axioms parser19
def cell20 : Array U8 16#usize := ⟨[145#u8,151#u8,105#u8,31#u8,34#u8,24#u8,26#u8,55#u8,201#u8,18#u8,213#u8,38#u8,245#u8,224#u8,14#u8,79#u8],by rfl⟩
def limbs20 : QM31Limbs := ![⟨527013777,by change 527013777<2147483647;omega⟩,⟨924456994,by change 924456994<2147483647;omega⟩,⟨651498185,by change 651498185<2147483647;omega⟩,⟨1326375157,by change 1326375157<2147483647;omega⟩]
theorem rawCell20 : (raw.drop 320).take 16=cell20.val := by
  simp only [raw,JFz_Scan55.data,JFz_Scan55.j00,JFz_Scan55.j01,JFz_Scan55.j02,JFz_Scan55.j03,JFz_Scan55.j04,JFz_Scan55.j05,JFz_Scan55.j06,JFz_Scan55.j07,JFz_Scan55.j08,JFz_Scan55.j09,JFz_Scan55.j10,JFz_Scan55.j11,JFz_Scan55.j12,JFz_Scan55.b00_length,JFz_Scan55.b01_length,JFz_Scan55.b02_length,JFz_Scan55.b03_length,JFz_Scan55.b04_length,JFz_Scan55.b05_length,JFz_Scan55.b06_length,JFz_Scan55.b07_length,JFz_Scan55.b08_length,JFz_Scan55.b09_length,JFz_Scan55.b10_length,JFz_Scan55.b11_length,JFz_Scan55.b12_length,JFz_Scan55.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell20
theorem encoded20 : CandidateParserByteOrder.arrayBytes16 cell20=encodeQM31LE limbs20 := by
  funext i
  fin_cases i <;> rfl
theorem parser20 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell20)=
    ok (some ⟨⟨527013777#u32,924456994#u32⟩,⟨651498185#u32,1326375157#u32⟩⟩) :=
  JFr_EncodedCell.parser cell20 limbs20 encoded20
#print axioms encoded20
#print axioms parser20
def cell21 : Array U8 16#usize := ⟨[240#u8,106#u8,159#u8,88#u8,79#u8,93#u8,39#u8,95#u8,90#u8,18#u8,213#u8,9#u8,90#u8,131#u8,201#u8,61#u8],by rfl⟩
def limbs21 : QM31Limbs := ![⟨1486842608,by change 1486842608<2147483647;omega⟩,⟨1596415311,by change 1596415311<2147483647;omega⟩,⟨164958810,by change 164958810<2147483647;omega⟩,⟨1036616538,by change 1036616538<2147483647;omega⟩]
theorem rawCell21 : (raw.drop 336).take 16=cell21.val := by
  simp only [raw,JFz_Scan55.data,JFz_Scan55.j00,JFz_Scan55.j01,JFz_Scan55.j02,JFz_Scan55.j03,JFz_Scan55.j04,JFz_Scan55.j05,JFz_Scan55.j06,JFz_Scan55.j07,JFz_Scan55.j08,JFz_Scan55.j09,JFz_Scan55.j10,JFz_Scan55.j11,JFz_Scan55.j12,JFz_Scan55.b00_length,JFz_Scan55.b01_length,JFz_Scan55.b02_length,JFz_Scan55.b03_length,JFz_Scan55.b04_length,JFz_Scan55.b05_length,JFz_Scan55.b06_length,JFz_Scan55.b07_length,JFz_Scan55.b08_length,JFz_Scan55.b09_length,JFz_Scan55.b10_length,JFz_Scan55.b11_length,JFz_Scan55.b12_length,JFz_Scan55.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell21
theorem encoded21 : CandidateParserByteOrder.arrayBytes16 cell21=encodeQM31LE limbs21 := by
  funext i
  fin_cases i <;> rfl
theorem parser21 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell21)=
    ok (some ⟨⟨1486842608#u32,1596415311#u32⟩,⟨164958810#u32,1036616538#u32⟩⟩) :=
  JFr_EncodedCell.parser cell21 limbs21 encoded21
#print axioms encoded21
#print axioms parser21
def cell22 : Array U8 16#usize := ⟨[12#u8,185#u8,163#u8,30#u8,164#u8,88#u8,62#u8,106#u8,250#u8,238#u8,141#u8,88#u8,247#u8,30#u8,198#u8,54#u8],by rfl⟩
def limbs22 : QM31Limbs := ![⟨514046220,by change 514046220<2147483647;omega⟩,⟨1782470820,by change 1782470820<2147483647;omega⟩,⟨1485696762,by change 1485696762<2147483647;omega⟩,⟨918953719,by change 918953719<2147483647;omega⟩]
theorem rawCell22 : (raw.drop 352).take 16=cell22.val := by
  simp only [raw,JFz_Scan55.data,JFz_Scan55.j00,JFz_Scan55.j01,JFz_Scan55.j02,JFz_Scan55.j03,JFz_Scan55.j04,JFz_Scan55.j05,JFz_Scan55.j06,JFz_Scan55.j07,JFz_Scan55.j08,JFz_Scan55.j09,JFz_Scan55.j10,JFz_Scan55.j11,JFz_Scan55.j12,JFz_Scan55.b00_length,JFz_Scan55.b01_length,JFz_Scan55.b02_length,JFz_Scan55.b03_length,JFz_Scan55.b04_length,JFz_Scan55.b05_length,JFz_Scan55.b06_length,JFz_Scan55.b07_length,JFz_Scan55.b08_length,JFz_Scan55.b09_length,JFz_Scan55.b10_length,JFz_Scan55.b11_length,JFz_Scan55.b12_length,JFz_Scan55.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell22
theorem encoded22 : CandidateParserByteOrder.arrayBytes16 cell22=encodeQM31LE limbs22 := by
  funext i
  fin_cases i <;> rfl
theorem parser22 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell22)=
    ok (some ⟨⟨514046220#u32,1782470820#u32⟩,⟨1485696762#u32,918953719#u32⟩⟩) :=
  JFr_EncodedCell.parser cell22 limbs22 encoded22
#print axioms encoded22
#print axioms parser22
def cell23 : Array U8 16#usize := ⟨[45#u8,187#u8,157#u8,65#u8,119#u8,140#u8,129#u8,120#u8,128#u8,21#u8,225#u8,35#u8,170#u8,203#u8,20#u8,51#u8],by rfl⟩
def limbs23 : QM31Limbs := ![⟨1100856109,by change 1100856109<2147483647;omega⟩,⟨2021756023,by change 2021756023<2147483647;omega⟩,⟨601953664,by change 601953664<2147483647;omega⟩,⟨857000874,by change 857000874<2147483647;omega⟩]
theorem rawCell23 : (raw.drop 368).take 16=cell23.val := by
  simp only [raw,JFz_Scan55.data,JFz_Scan55.j00,JFz_Scan55.j01,JFz_Scan55.j02,JFz_Scan55.j03,JFz_Scan55.j04,JFz_Scan55.j05,JFz_Scan55.j06,JFz_Scan55.j07,JFz_Scan55.j08,JFz_Scan55.j09,JFz_Scan55.j10,JFz_Scan55.j11,JFz_Scan55.j12,JFz_Scan55.b00_length,JFz_Scan55.b01_length,JFz_Scan55.b02_length,JFz_Scan55.b03_length,JFz_Scan55.b04_length,JFz_Scan55.b05_length,JFz_Scan55.b06_length,JFz_Scan55.b07_length,JFz_Scan55.b08_length,JFz_Scan55.b09_length,JFz_Scan55.b10_length,JFz_Scan55.b11_length,JFz_Scan55.b12_length,JFz_Scan55.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell23
theorem encoded23 : CandidateParserByteOrder.arrayBytes16 cell23=encodeQM31LE limbs23 := by
  funext i
  fin_cases i <;> rfl
theorem parser23 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell23)=
    ok (some ⟨⟨1100856109#u32,2021756023#u32⟩,⟨601953664#u32,857000874#u32⟩⟩) :=
  JFr_EncodedCell.parser cell23 limbs23 encoded23
#print axioms encoded23
#print axioms parser23
def cell24 : Array U8 16#usize := ⟨[206#u8,205#u8,3#u8,29#u8,70#u8,101#u8,13#u8,39#u8,71#u8,111#u8,107#u8,115#u8,231#u8,40#u8,28#u8,7#u8],by rfl⟩
def limbs24 : QM31Limbs := ![⟨486788558,by change 486788558<2147483647;omega⟩,⟨655189318,by change 655189318<2147483647;omega⟩,⟨1936420679,by change 1936420679<2147483647;omega⟩,⟨119285991,by change 119285991<2147483647;omega⟩]
theorem rawCell24 : (raw.drop 384).take 16=cell24.val := by
  simp only [raw,JFz_Scan55.data,JFz_Scan55.j00,JFz_Scan55.j01,JFz_Scan55.j02,JFz_Scan55.j03,JFz_Scan55.j04,JFz_Scan55.j05,JFz_Scan55.j06,JFz_Scan55.j07,JFz_Scan55.j08,JFz_Scan55.j09,JFz_Scan55.j10,JFz_Scan55.j11,JFz_Scan55.j12,JFz_Scan55.b00_length,JFz_Scan55.b01_length,JFz_Scan55.b02_length,JFz_Scan55.b03_length,JFz_Scan55.b04_length,JFz_Scan55.b05_length,JFz_Scan55.b06_length,JFz_Scan55.b07_length,JFz_Scan55.b08_length,JFz_Scan55.b09_length,JFz_Scan55.b10_length,JFz_Scan55.b11_length,JFz_Scan55.b12_length,JFz_Scan55.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell24
theorem encoded24 : CandidateParserByteOrder.arrayBytes16 cell24=encodeQM31LE limbs24 := by
  funext i
  fin_cases i <;> rfl
theorem parser24 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell24)=
    ok (some ⟨⟨486788558#u32,655189318#u32⟩,⟨1936420679#u32,119285991#u32⟩⟩) :=
  JFr_EncodedCell.parser cell24 limbs24 encoded24
#print axioms encoded24
#print axioms parser24
def cell25 : Array U8 16#usize := ⟨[144#u8,83#u8,21#u8,9#u8,55#u8,66#u8,76#u8,59#u8,90#u8,52#u8,87#u8,6#u8,142#u8,104#u8,169#u8,79#u8],by rfl⟩
def limbs25 : QM31Limbs := ![⟨152392592,by change 152392592<2147483647;omega⟩,⟨994853431,by change 994853431<2147483647;omega⟩,⟨106378330,by change 106378330<2147483647;omega⟩,⟨1336502414,by change 1336502414<2147483647;omega⟩]
theorem rawCell25 : (raw.drop 400).take 16=cell25.val := by
  simp only [raw,JFz_Scan55.data,JFz_Scan55.j00,JFz_Scan55.j01,JFz_Scan55.j02,JFz_Scan55.j03,JFz_Scan55.j04,JFz_Scan55.j05,JFz_Scan55.j06,JFz_Scan55.j07,JFz_Scan55.j08,JFz_Scan55.j09,JFz_Scan55.j10,JFz_Scan55.j11,JFz_Scan55.j12,JFz_Scan55.b00_length,JFz_Scan55.b01_length,JFz_Scan55.b02_length,JFz_Scan55.b03_length,JFz_Scan55.b04_length,JFz_Scan55.b05_length,JFz_Scan55.b06_length,JFz_Scan55.b07_length,JFz_Scan55.b08_length,JFz_Scan55.b09_length,JFz_Scan55.b10_length,JFz_Scan55.b11_length,JFz_Scan55.b12_length,JFz_Scan55.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell25
theorem encoded25 : CandidateParserByteOrder.arrayBytes16 cell25=encodeQM31LE limbs25 := by
  funext i
  fin_cases i <;> rfl
theorem parser25 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell25)=
    ok (some ⟨⟨152392592#u32,994853431#u32⟩,⟨106378330#u32,1336502414#u32⟩⟩) :=
  JFr_EncodedCell.parser cell25 limbs25 encoded25
#print axioms encoded25
#print axioms parser25
def cell26 : Array U8 16#usize := ⟨[44#u8,22#u8,246#u8,2#u8,90#u8,173#u8,193#u8,70#u8,145#u8,79#u8,59#u8,95#u8,109#u8,128#u8,29#u8,121#u8],by rfl⟩
def limbs26 : QM31Limbs := ![⟨49681964,by change 49681964<2147483647;omega⟩,⟨1187097946,by change 1187097946<2147483647;omega⟩,⟨1597722513,by change 1597722513<2147483647;omega⟩,⟨2031976557,by change 2031976557<2147483647;omega⟩]
theorem rawCell26 : (raw.drop 416).take 16=cell26.val := by
  simp only [raw,JFz_Scan55.data,JFz_Scan55.j00,JFz_Scan55.j01,JFz_Scan55.j02,JFz_Scan55.j03,JFz_Scan55.j04,JFz_Scan55.j05,JFz_Scan55.j06,JFz_Scan55.j07,JFz_Scan55.j08,JFz_Scan55.j09,JFz_Scan55.j10,JFz_Scan55.j11,JFz_Scan55.j12,JFz_Scan55.b00_length,JFz_Scan55.b01_length,JFz_Scan55.b02_length,JFz_Scan55.b03_length,JFz_Scan55.b04_length,JFz_Scan55.b05_length,JFz_Scan55.b06_length,JFz_Scan55.b07_length,JFz_Scan55.b08_length,JFz_Scan55.b09_length,JFz_Scan55.b10_length,JFz_Scan55.b11_length,JFz_Scan55.b12_length,JFz_Scan55.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell26
theorem encoded26 : CandidateParserByteOrder.arrayBytes16 cell26=encodeQM31LE limbs26 := by
  funext i
  fin_cases i <;> rfl
theorem parser26 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell26)=
    ok (some ⟨⟨49681964#u32,1187097946#u32⟩,⟨1597722513#u32,2031976557#u32⟩⟩) :=
  JFr_EncodedCell.parser cell26 limbs26 encoded26
#print axioms encoded26
#print axioms parser26
def cell27 : Array U8 16#usize := ⟨[23#u8,254#u8,169#u8,7#u8,27#u8,255#u8,70#u8,47#u8,0#u8,102#u8,218#u8,122#u8,174#u8,176#u8,187#u8,109#u8],by rfl⟩
def limbs27 : QM31Limbs := ![⟨128581143,by change 128581143<2147483647;omega⟩,⟨793181979,by change 793181979<2147483647;omega⟩,⟨2061133312,by change 2061133312<2147483647;omega⟩,⟨1841017006,by change 1841017006<2147483647;omega⟩]
theorem rawCell27 : (raw.drop 432).take 16=cell27.val := by
  simp only [raw,JFz_Scan55.data,JFz_Scan55.j00,JFz_Scan55.j01,JFz_Scan55.j02,JFz_Scan55.j03,JFz_Scan55.j04,JFz_Scan55.j05,JFz_Scan55.j06,JFz_Scan55.j07,JFz_Scan55.j08,JFz_Scan55.j09,JFz_Scan55.j10,JFz_Scan55.j11,JFz_Scan55.j12,JFz_Scan55.b00_length,JFz_Scan55.b01_length,JFz_Scan55.b02_length,JFz_Scan55.b03_length,JFz_Scan55.b04_length,JFz_Scan55.b05_length,JFz_Scan55.b06_length,JFz_Scan55.b07_length,JFz_Scan55.b08_length,JFz_Scan55.b09_length,JFz_Scan55.b10_length,JFz_Scan55.b11_length,JFz_Scan55.b12_length,JFz_Scan55.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell27
theorem encoded27 : CandidateParserByteOrder.arrayBytes16 cell27=encodeQM31LE limbs27 := by
  funext i
  fin_cases i <;> rfl
theorem parser27 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell27)=
    ok (some ⟨⟨128581143#u32,793181979#u32⟩,⟨2061133312#u32,1841017006#u32⟩⟩) :=
  JFr_EncodedCell.parser cell27 limbs27 encoded27
#print axioms encoded27
#print axioms parser27
end AspisR1.JFr_Bytes07
