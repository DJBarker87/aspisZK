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
def cell00 : Array U8 16#usize := ⟨[71#u8,142#u8,58#u8,65#u8,176#u8,132#u8,160#u8,71#u8,195#u8,164#u8,53#u8,99#u8,240#u8,197#u8,109#u8,104#u8],by rfl⟩
def limbs00 : QM31Limbs := ![⟨1094356551,by change 1094356551<2147483647;omega⟩,⟨1201702064,by change 1201702064<2147483647;omega⟩,⟨1664459971,by change 1664459971<2147483647;omega⟩,⟨1752024560,by change 1752024560<2147483647;omega⟩]
theorem rawCell00 : (raw.drop 0).take 16=cell00.val := by
  simp only [raw,JFz_Scan51.data,JFz_Scan51.j00,JFz_Scan51.j01,JFz_Scan51.j02,JFz_Scan51.j03,JFz_Scan51.j04,JFz_Scan51.j05,JFz_Scan51.j06,JFz_Scan51.j07,JFz_Scan51.j08,JFz_Scan51.j09,JFz_Scan51.j10,JFz_Scan51.j11,JFz_Scan51.j12,JFz_Scan51.b00_length,JFz_Scan51.b01_length,JFz_Scan51.b02_length,JFz_Scan51.b03_length,JFz_Scan51.b04_length,JFz_Scan51.b05_length,JFz_Scan51.b06_length,JFz_Scan51.b07_length,JFz_Scan51.b08_length,JFz_Scan51.b09_length,JFz_Scan51.b10_length,JFz_Scan51.b11_length,JFz_Scan51.b12_length,JFz_Scan51.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell00
theorem encoded00 : CandidateParserByteOrder.arrayBytes16 cell00=encodeQM31LE limbs00 := by
  funext i
  fin_cases i <;> rfl
theorem parser00 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell00)=
    ok (some ⟨⟨1094356551#u32,1201702064#u32⟩,⟨1664459971#u32,1752024560#u32⟩⟩) :=
  JFr_EncodedCell.parser cell00 limbs00 encoded00
#print axioms encoded00
#print axioms parser00
def cell01 : Array U8 16#usize := ⟨[204#u8,229#u8,168#u8,95#u8,233#u8,3#u8,79#u8,25#u8,102#u8,253#u8,251#u8,86#u8,17#u8,61#u8,43#u8,43#u8],by rfl⟩
def limbs01 : QM31Limbs := ![⟨1604904396,by change 1604904396<2147483647;omega⟩,⟨424608745,by change 424608745<2147483647;omega⟩,⟨1459354982,by change 1459354982<2147483647;omega⟩,⟨724253969,by change 724253969<2147483647;omega⟩]
theorem rawCell01 : (raw.drop 16).take 16=cell01.val := by
  simp only [raw,JFz_Scan51.data,JFz_Scan51.j00,JFz_Scan51.j01,JFz_Scan51.j02,JFz_Scan51.j03,JFz_Scan51.j04,JFz_Scan51.j05,JFz_Scan51.j06,JFz_Scan51.j07,JFz_Scan51.j08,JFz_Scan51.j09,JFz_Scan51.j10,JFz_Scan51.j11,JFz_Scan51.j12,JFz_Scan51.b00_length,JFz_Scan51.b01_length,JFz_Scan51.b02_length,JFz_Scan51.b03_length,JFz_Scan51.b04_length,JFz_Scan51.b05_length,JFz_Scan51.b06_length,JFz_Scan51.b07_length,JFz_Scan51.b08_length,JFz_Scan51.b09_length,JFz_Scan51.b10_length,JFz_Scan51.b11_length,JFz_Scan51.b12_length,JFz_Scan51.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell01
theorem encoded01 : CandidateParserByteOrder.arrayBytes16 cell01=encodeQM31LE limbs01 := by
  funext i
  fin_cases i <;> rfl
theorem parser01 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell01)=
    ok (some ⟨⟨1604904396#u32,424608745#u32⟩,⟨1459354982#u32,724253969#u32⟩⟩) :=
  JFr_EncodedCell.parser cell01 limbs01 encoded01
#print axioms encoded01
#print axioms parser01
def cell02 : Array U8 16#usize := ⟨[125#u8,218#u8,108#u8,119#u8,18#u8,58#u8,141#u8,21#u8,29#u8,99#u8,16#u8,111#u8,229#u8,117#u8,39#u8,100#u8],by rfl⟩
def limbs02 : QM31Limbs := ![⟨2003622525,by change 2003622525<2147483647;omega⟩,⟨361576978,by change 361576978<2147483647;omega⟩,⟨1863344925,by change 1863344925<2147483647;omega⟩,⟨1680307685,by change 1680307685<2147483647;omega⟩]
theorem rawCell02 : (raw.drop 32).take 16=cell02.val := by
  simp only [raw,JFz_Scan51.data,JFz_Scan51.j00,JFz_Scan51.j01,JFz_Scan51.j02,JFz_Scan51.j03,JFz_Scan51.j04,JFz_Scan51.j05,JFz_Scan51.j06,JFz_Scan51.j07,JFz_Scan51.j08,JFz_Scan51.j09,JFz_Scan51.j10,JFz_Scan51.j11,JFz_Scan51.j12,JFz_Scan51.b00_length,JFz_Scan51.b01_length,JFz_Scan51.b02_length,JFz_Scan51.b03_length,JFz_Scan51.b04_length,JFz_Scan51.b05_length,JFz_Scan51.b06_length,JFz_Scan51.b07_length,JFz_Scan51.b08_length,JFz_Scan51.b09_length,JFz_Scan51.b10_length,JFz_Scan51.b11_length,JFz_Scan51.b12_length,JFz_Scan51.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell02
theorem encoded02 : CandidateParserByteOrder.arrayBytes16 cell02=encodeQM31LE limbs02 := by
  funext i
  fin_cases i <;> rfl
theorem parser02 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell02)=
    ok (some ⟨⟨2003622525#u32,361576978#u32⟩,⟨1863344925#u32,1680307685#u32⟩⟩) :=
  JFr_EncodedCell.parser cell02 limbs02 encoded02
#print axioms encoded02
#print axioms parser02
def cell03 : Array U8 16#usize := ⟨[99#u8,94#u8,138#u8,97#u8,33#u8,125#u8,101#u8,61#u8,47#u8,43#u8,172#u8,46#u8,49#u8,16#u8,132#u8,62#u8],by rfl⟩
def limbs03 : QM31Limbs := ![⟨1636458083,by change 1636458083<2147483647;omega⟩,⟨1030061345,by change 1030061345<2147483647;omega⟩,⟨783035183,by change 783035183<2147483647;omega⟩,⟨1048842289,by change 1048842289<2147483647;omega⟩]
theorem rawCell03 : (raw.drop 48).take 16=cell03.val := by
  simp only [raw,JFz_Scan51.data,JFz_Scan51.j00,JFz_Scan51.j01,JFz_Scan51.j02,JFz_Scan51.j03,JFz_Scan51.j04,JFz_Scan51.j05,JFz_Scan51.j06,JFz_Scan51.j07,JFz_Scan51.j08,JFz_Scan51.j09,JFz_Scan51.j10,JFz_Scan51.j11,JFz_Scan51.j12,JFz_Scan51.b00_length,JFz_Scan51.b01_length,JFz_Scan51.b02_length,JFz_Scan51.b03_length,JFz_Scan51.b04_length,JFz_Scan51.b05_length,JFz_Scan51.b06_length,JFz_Scan51.b07_length,JFz_Scan51.b08_length,JFz_Scan51.b09_length,JFz_Scan51.b10_length,JFz_Scan51.b11_length,JFz_Scan51.b12_length,JFz_Scan51.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell03
theorem encoded03 : CandidateParserByteOrder.arrayBytes16 cell03=encodeQM31LE limbs03 := by
  funext i
  fin_cases i <;> rfl
theorem parser03 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell03)=
    ok (some ⟨⟨1636458083#u32,1030061345#u32⟩,⟨783035183#u32,1048842289#u32⟩⟩) :=
  JFr_EncodedCell.parser cell03 limbs03 encoded03
#print axioms encoded03
#print axioms parser03
def cell04 : Array U8 16#usize := ⟨[204#u8,30#u8,62#u8,6#u8,221#u8,222#u8,1#u8,104#u8,100#u8,11#u8,234#u8,112#u8,190#u8,254#u8,141#u8,64#u8],by rfl⟩
def limbs04 : QM31Limbs := ![⟨104734412,by change 104734412<2147483647;omega⟩,⟨1744953053,by change 1744953053<2147483647;omega⟩,⟨1894386532,by change 1894386532<2147483647;omega⟩,⟨1083047614,by change 1083047614<2147483647;omega⟩]
theorem rawCell04 : (raw.drop 64).take 16=cell04.val := by
  simp only [raw,JFz_Scan51.data,JFz_Scan51.j00,JFz_Scan51.j01,JFz_Scan51.j02,JFz_Scan51.j03,JFz_Scan51.j04,JFz_Scan51.j05,JFz_Scan51.j06,JFz_Scan51.j07,JFz_Scan51.j08,JFz_Scan51.j09,JFz_Scan51.j10,JFz_Scan51.j11,JFz_Scan51.j12,JFz_Scan51.b00_length,JFz_Scan51.b01_length,JFz_Scan51.b02_length,JFz_Scan51.b03_length,JFz_Scan51.b04_length,JFz_Scan51.b05_length,JFz_Scan51.b06_length,JFz_Scan51.b07_length,JFz_Scan51.b08_length,JFz_Scan51.b09_length,JFz_Scan51.b10_length,JFz_Scan51.b11_length,JFz_Scan51.b12_length,JFz_Scan51.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell04
theorem encoded04 : CandidateParserByteOrder.arrayBytes16 cell04=encodeQM31LE limbs04 := by
  funext i
  fin_cases i <;> rfl
theorem parser04 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell04)=
    ok (some ⟨⟨104734412#u32,1744953053#u32⟩,⟨1894386532#u32,1083047614#u32⟩⟩) :=
  JFr_EncodedCell.parser cell04 limbs04 encoded04
#print axioms encoded04
#print axioms parser04
def cell05 : Array U8 16#usize := ⟨[36#u8,118#u8,201#u8,24#u8,95#u8,145#u8,150#u8,42#u8,130#u8,92#u8,202#u8,43#u8,32#u8,168#u8,136#u8,48#u8],by rfl⟩
def limbs05 : QM31Limbs := ![⟨415856164,by change 415856164<2147483647;omega⟩,⟨714510687,by change 714510687<2147483647;omega⟩,⟨734682242,by change 734682242<2147483647;omega⟩,⟨814262304,by change 814262304<2147483647;omega⟩]
theorem rawCell05 : (raw.drop 80).take 16=cell05.val := by
  simp only [raw,JFz_Scan51.data,JFz_Scan51.j00,JFz_Scan51.j01,JFz_Scan51.j02,JFz_Scan51.j03,JFz_Scan51.j04,JFz_Scan51.j05,JFz_Scan51.j06,JFz_Scan51.j07,JFz_Scan51.j08,JFz_Scan51.j09,JFz_Scan51.j10,JFz_Scan51.j11,JFz_Scan51.j12,JFz_Scan51.b00_length,JFz_Scan51.b01_length,JFz_Scan51.b02_length,JFz_Scan51.b03_length,JFz_Scan51.b04_length,JFz_Scan51.b05_length,JFz_Scan51.b06_length,JFz_Scan51.b07_length,JFz_Scan51.b08_length,JFz_Scan51.b09_length,JFz_Scan51.b10_length,JFz_Scan51.b11_length,JFz_Scan51.b12_length,JFz_Scan51.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell05
theorem encoded05 : CandidateParserByteOrder.arrayBytes16 cell05=encodeQM31LE limbs05 := by
  funext i
  fin_cases i <;> rfl
theorem parser05 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell05)=
    ok (some ⟨⟨415856164#u32,714510687#u32⟩,⟨734682242#u32,814262304#u32⟩⟩) :=
  JFr_EncodedCell.parser cell05 limbs05 encoded05
#print axioms encoded05
#print axioms parser05
def cell06 : Array U8 16#usize := ⟨[143#u8,22#u8,231#u8,18#u8,145#u8,144#u8,137#u8,10#u8,230#u8,126#u8,167#u8,100#u8,53#u8,101#u8,210#u8,99#u8],by rfl⟩
def limbs06 : QM31Limbs := ![⟨317134479,by change 317134479<2147483647;omega⟩,⟨176787601,by change 176787601<2147483647;omega⟩,⟨1688698598,by change 1688698598<2147483647;omega⟩,⟨1674732853,by change 1674732853<2147483647;omega⟩]
theorem rawCell06 : (raw.drop 96).take 16=cell06.val := by
  simp only [raw,JFz_Scan51.data,JFz_Scan51.j00,JFz_Scan51.j01,JFz_Scan51.j02,JFz_Scan51.j03,JFz_Scan51.j04,JFz_Scan51.j05,JFz_Scan51.j06,JFz_Scan51.j07,JFz_Scan51.j08,JFz_Scan51.j09,JFz_Scan51.j10,JFz_Scan51.j11,JFz_Scan51.j12,JFz_Scan51.b00_length,JFz_Scan51.b01_length,JFz_Scan51.b02_length,JFz_Scan51.b03_length,JFz_Scan51.b04_length,JFz_Scan51.b05_length,JFz_Scan51.b06_length,JFz_Scan51.b07_length,JFz_Scan51.b08_length,JFz_Scan51.b09_length,JFz_Scan51.b10_length,JFz_Scan51.b11_length,JFz_Scan51.b12_length,JFz_Scan51.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell06
theorem encoded06 : CandidateParserByteOrder.arrayBytes16 cell06=encodeQM31LE limbs06 := by
  funext i
  fin_cases i <;> rfl
theorem parser06 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell06)=
    ok (some ⟨⟨317134479#u32,176787601#u32⟩,⟨1688698598#u32,1674732853#u32⟩⟩) :=
  JFr_EncodedCell.parser cell06 limbs06 encoded06
#print axioms encoded06
#print axioms parser06
def cell07 : Array U8 16#usize := ⟨[89#u8,169#u8,206#u8,31#u8,73#u8,215#u8,235#u8,94#u8,29#u8,213#u8,36#u8,101#u8,110#u8,104#u8,83#u8,80#u8],by rfl⟩
def limbs07 : QM31Limbs := ![⟨533637465,by change 533637465<2147483647;omega⟩,⟨1592514377,by change 1592514377<2147483647;omega⟩,⟨1696912669,by change 1696912669<2147483647;omega⟩,⟨1347643502,by change 1347643502<2147483647;omega⟩]
theorem rawCell07 : (raw.drop 112).take 16=cell07.val := by
  simp only [raw,JFz_Scan51.data,JFz_Scan51.j00,JFz_Scan51.j01,JFz_Scan51.j02,JFz_Scan51.j03,JFz_Scan51.j04,JFz_Scan51.j05,JFz_Scan51.j06,JFz_Scan51.j07,JFz_Scan51.j08,JFz_Scan51.j09,JFz_Scan51.j10,JFz_Scan51.j11,JFz_Scan51.j12,JFz_Scan51.b00_length,JFz_Scan51.b01_length,JFz_Scan51.b02_length,JFz_Scan51.b03_length,JFz_Scan51.b04_length,JFz_Scan51.b05_length,JFz_Scan51.b06_length,JFz_Scan51.b07_length,JFz_Scan51.b08_length,JFz_Scan51.b09_length,JFz_Scan51.b10_length,JFz_Scan51.b11_length,JFz_Scan51.b12_length,JFz_Scan51.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell07
theorem encoded07 : CandidateParserByteOrder.arrayBytes16 cell07=encodeQM31LE limbs07 := by
  funext i
  fin_cases i <;> rfl
theorem parser07 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell07)=
    ok (some ⟨⟨533637465#u32,1592514377#u32⟩,⟨1696912669#u32,1347643502#u32⟩⟩) :=
  JFr_EncodedCell.parser cell07 limbs07 encoded07
#print axioms encoded07
#print axioms parser07
def cell08 : Array U8 16#usize := ⟨[233#u8,27#u8,151#u8,18#u8,93#u8,82#u8,124#u8,55#u8,99#u8,240#u8,118#u8,88#u8,238#u8,203#u8,223#u8,13#u8],by rfl⟩
def limbs08 : QM31Limbs := ![⟨311892969,by change 311892969<2147483647;omega⟩,⟨930894429,by change 930894429<2147483647;omega⟩,⟨1484189795,by change 1484189795<2147483647;omega⟩,⟨232770542,by change 232770542<2147483647;omega⟩]
theorem rawCell08 : (raw.drop 128).take 16=cell08.val := by
  simp only [raw,JFz_Scan51.data,JFz_Scan51.j00,JFz_Scan51.j01,JFz_Scan51.j02,JFz_Scan51.j03,JFz_Scan51.j04,JFz_Scan51.j05,JFz_Scan51.j06,JFz_Scan51.j07,JFz_Scan51.j08,JFz_Scan51.j09,JFz_Scan51.j10,JFz_Scan51.j11,JFz_Scan51.j12,JFz_Scan51.b00_length,JFz_Scan51.b01_length,JFz_Scan51.b02_length,JFz_Scan51.b03_length,JFz_Scan51.b04_length,JFz_Scan51.b05_length,JFz_Scan51.b06_length,JFz_Scan51.b07_length,JFz_Scan51.b08_length,JFz_Scan51.b09_length,JFz_Scan51.b10_length,JFz_Scan51.b11_length,JFz_Scan51.b12_length,JFz_Scan51.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell08
theorem encoded08 : CandidateParserByteOrder.arrayBytes16 cell08=encodeQM31LE limbs08 := by
  funext i
  fin_cases i <;> rfl
theorem parser08 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell08)=
    ok (some ⟨⟨311892969#u32,930894429#u32⟩,⟨1484189795#u32,232770542#u32⟩⟩) :=
  JFr_EncodedCell.parser cell08 limbs08 encoded08
#print axioms encoded08
#print axioms parser08
def cell09 : Array U8 16#usize := ⟨[254#u8,127#u8,136#u8,35#u8,54#u8,104#u8,168#u8,51#u8,111#u8,220#u8,134#u8,48#u8,156#u8,129#u8,17#u8,99#u8],by rfl⟩
def limbs09 : QM31Limbs := ![⟨596148222,by change 596148222<2147483647;omega⟩,⟨866674742,by change 866674742<2147483647;omega⟩,⟨814144623,by change 814144623<2147483647;omega⟩,⟨1662091676,by change 1662091676<2147483647;omega⟩]
theorem rawCell09 : (raw.drop 144).take 16=cell09.val := by
  simp only [raw,JFz_Scan51.data,JFz_Scan51.j00,JFz_Scan51.j01,JFz_Scan51.j02,JFz_Scan51.j03,JFz_Scan51.j04,JFz_Scan51.j05,JFz_Scan51.j06,JFz_Scan51.j07,JFz_Scan51.j08,JFz_Scan51.j09,JFz_Scan51.j10,JFz_Scan51.j11,JFz_Scan51.j12,JFz_Scan51.b00_length,JFz_Scan51.b01_length,JFz_Scan51.b02_length,JFz_Scan51.b03_length,JFz_Scan51.b04_length,JFz_Scan51.b05_length,JFz_Scan51.b06_length,JFz_Scan51.b07_length,JFz_Scan51.b08_length,JFz_Scan51.b09_length,JFz_Scan51.b10_length,JFz_Scan51.b11_length,JFz_Scan51.b12_length,JFz_Scan51.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell09
theorem encoded09 : CandidateParserByteOrder.arrayBytes16 cell09=encodeQM31LE limbs09 := by
  funext i
  fin_cases i <;> rfl
theorem parser09 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell09)=
    ok (some ⟨⟨596148222#u32,866674742#u32⟩,⟨814144623#u32,1662091676#u32⟩⟩) :=
  JFr_EncodedCell.parser cell09 limbs09 encoded09
#print axioms encoded09
#print axioms parser09
def cell10 : Array U8 16#usize := ⟨[226#u8,231#u8,18#u8,17#u8,54#u8,254#u8,164#u8,114#u8,79#u8,82#u8,102#u8,35#u8,109#u8,6#u8,73#u8,44#u8],by rfl⟩
def limbs10 : QM31Limbs := ![⟨286451682,by change 286451682<2147483647;omega⟩,⟨1923415606,by change 1923415606<2147483647;omega⟩,⟨593908303,by change 593908303<2147483647;omega⟩,⟨742983277,by change 742983277<2147483647;omega⟩]
theorem rawCell10 : (raw.drop 160).take 16=cell10.val := by
  simp only [raw,JFz_Scan51.data,JFz_Scan51.j00,JFz_Scan51.j01,JFz_Scan51.j02,JFz_Scan51.j03,JFz_Scan51.j04,JFz_Scan51.j05,JFz_Scan51.j06,JFz_Scan51.j07,JFz_Scan51.j08,JFz_Scan51.j09,JFz_Scan51.j10,JFz_Scan51.j11,JFz_Scan51.j12,JFz_Scan51.b00_length,JFz_Scan51.b01_length,JFz_Scan51.b02_length,JFz_Scan51.b03_length,JFz_Scan51.b04_length,JFz_Scan51.b05_length,JFz_Scan51.b06_length,JFz_Scan51.b07_length,JFz_Scan51.b08_length,JFz_Scan51.b09_length,JFz_Scan51.b10_length,JFz_Scan51.b11_length,JFz_Scan51.b12_length,JFz_Scan51.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell10
theorem encoded10 : CandidateParserByteOrder.arrayBytes16 cell10=encodeQM31LE limbs10 := by
  funext i
  fin_cases i <;> rfl
theorem parser10 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell10)=
    ok (some ⟨⟨286451682#u32,1923415606#u32⟩,⟨593908303#u32,742983277#u32⟩⟩) :=
  JFr_EncodedCell.parser cell10 limbs10 encoded10
#print axioms encoded10
#print axioms parser10
def cell11 : Array U8 16#usize := ⟨[174#u8,144#u8,229#u8,20#u8,225#u8,159#u8,64#u8,115#u8,30#u8,15#u8,191#u8,72#u8,54#u8,189#u8,147#u8,29#u8],by rfl⟩
def limbs11 : QM31Limbs := ![⟨350589102,by change 350589102<2147483647;omega⟩,⟨1933615073,by change 1933615073<2147483647;omega⟩,⟨1220480798,by change 1220480798<2147483647;omega⟩,⟨496221494,by change 496221494<2147483647;omega⟩]
theorem rawCell11 : (raw.drop 176).take 16=cell11.val := by
  simp only [raw,JFz_Scan51.data,JFz_Scan51.j00,JFz_Scan51.j01,JFz_Scan51.j02,JFz_Scan51.j03,JFz_Scan51.j04,JFz_Scan51.j05,JFz_Scan51.j06,JFz_Scan51.j07,JFz_Scan51.j08,JFz_Scan51.j09,JFz_Scan51.j10,JFz_Scan51.j11,JFz_Scan51.j12,JFz_Scan51.b00_length,JFz_Scan51.b01_length,JFz_Scan51.b02_length,JFz_Scan51.b03_length,JFz_Scan51.b04_length,JFz_Scan51.b05_length,JFz_Scan51.b06_length,JFz_Scan51.b07_length,JFz_Scan51.b08_length,JFz_Scan51.b09_length,JFz_Scan51.b10_length,JFz_Scan51.b11_length,JFz_Scan51.b12_length,JFz_Scan51.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell11
theorem encoded11 : CandidateParserByteOrder.arrayBytes16 cell11=encodeQM31LE limbs11 := by
  funext i
  fin_cases i <;> rfl
theorem parser11 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell11)=
    ok (some ⟨⟨350589102#u32,1933615073#u32⟩,⟨1220480798#u32,496221494#u32⟩⟩) :=
  JFr_EncodedCell.parser cell11 limbs11 encoded11
#print axioms encoded11
#print axioms parser11
def cell12 : Array U8 16#usize := ⟨[112#u8,216#u8,119#u8,41#u8,249#u8,201#u8,227#u8,57#u8,164#u8,101#u8,29#u8,79#u8,246#u8,88#u8,72#u8,7#u8],by rfl⟩
def limbs12 : QM31Limbs := ![⟨695720048,by change 695720048<2147483647;omega⟩,⟨971229689,by change 971229689<2147483647;omega⟩,⟨1327326628,by change 1327326628<2147483647;omega⟩,⟨122181878,by change 122181878<2147483647;omega⟩]
theorem rawCell12 : (raw.drop 192).take 16=cell12.val := by
  simp only [raw,JFz_Scan51.data,JFz_Scan51.j00,JFz_Scan51.j01,JFz_Scan51.j02,JFz_Scan51.j03,JFz_Scan51.j04,JFz_Scan51.j05,JFz_Scan51.j06,JFz_Scan51.j07,JFz_Scan51.j08,JFz_Scan51.j09,JFz_Scan51.j10,JFz_Scan51.j11,JFz_Scan51.j12,JFz_Scan51.b00_length,JFz_Scan51.b01_length,JFz_Scan51.b02_length,JFz_Scan51.b03_length,JFz_Scan51.b04_length,JFz_Scan51.b05_length,JFz_Scan51.b06_length,JFz_Scan51.b07_length,JFz_Scan51.b08_length,JFz_Scan51.b09_length,JFz_Scan51.b10_length,JFz_Scan51.b11_length,JFz_Scan51.b12_length,JFz_Scan51.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell12
theorem encoded12 : CandidateParserByteOrder.arrayBytes16 cell12=encodeQM31LE limbs12 := by
  funext i
  fin_cases i <;> rfl
theorem parser12 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell12)=
    ok (some ⟨⟨695720048#u32,971229689#u32⟩,⟨1327326628#u32,122181878#u32⟩⟩) :=
  JFr_EncodedCell.parser cell12 limbs12 encoded12
#print axioms encoded12
#print axioms parser12
def cell13 : Array U8 16#usize := ⟨[95#u8,31#u8,79#u8,77#u8,155#u8,22#u8,188#u8,83#u8,233#u8,10#u8,235#u8,85#u8,136#u8,252#u8,225#u8,90#u8],by rfl⟩
def limbs13 : QM31Limbs := ![⟨1297031007,by change 1297031007<2147483647;omega⟩,⟨1404835483,by change 1404835483<2147483647;omega⟩,⟨1441467113,by change 1441467113<2147483647;omega⟩,⟨1524759688,by change 1524759688<2147483647;omega⟩]
theorem rawCell13 : (raw.drop 208).take 16=cell13.val := by
  simp only [raw,JFz_Scan51.data,JFz_Scan51.j00,JFz_Scan51.j01,JFz_Scan51.j02,JFz_Scan51.j03,JFz_Scan51.j04,JFz_Scan51.j05,JFz_Scan51.j06,JFz_Scan51.j07,JFz_Scan51.j08,JFz_Scan51.j09,JFz_Scan51.j10,JFz_Scan51.j11,JFz_Scan51.j12,JFz_Scan51.b00_length,JFz_Scan51.b01_length,JFz_Scan51.b02_length,JFz_Scan51.b03_length,JFz_Scan51.b04_length,JFz_Scan51.b05_length,JFz_Scan51.b06_length,JFz_Scan51.b07_length,JFz_Scan51.b08_length,JFz_Scan51.b09_length,JFz_Scan51.b10_length,JFz_Scan51.b11_length,JFz_Scan51.b12_length,JFz_Scan51.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell13
theorem encoded13 : CandidateParserByteOrder.arrayBytes16 cell13=encodeQM31LE limbs13 := by
  funext i
  fin_cases i <;> rfl
theorem parser13 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell13)=
    ok (some ⟨⟨1297031007#u32,1404835483#u32⟩,⟨1441467113#u32,1524759688#u32⟩⟩) :=
  JFr_EncodedCell.parser cell13 limbs13 encoded13
#print axioms encoded13
#print axioms parser13
def cell14 : Array U8 16#usize := ⟨[162#u8,138#u8,73#u8,34#u8,156#u8,2#u8,34#u8,57#u8,222#u8,21#u8,147#u8,32#u8,99#u8,126#u8,14#u8,54#u8],by rfl⟩
def limbs14 : QM31Limbs := ![⟨575244962,by change 575244962<2147483647;omega⟩,⟨958530204,by change 958530204<2147483647;omega⟩,⟨546510302,by change 546510302<2147483647;omega⟩,⟨906919523,by change 906919523<2147483647;omega⟩]
theorem rawCell14 : (raw.drop 224).take 16=cell14.val := by
  simp only [raw,JFz_Scan51.data,JFz_Scan51.j00,JFz_Scan51.j01,JFz_Scan51.j02,JFz_Scan51.j03,JFz_Scan51.j04,JFz_Scan51.j05,JFz_Scan51.j06,JFz_Scan51.j07,JFz_Scan51.j08,JFz_Scan51.j09,JFz_Scan51.j10,JFz_Scan51.j11,JFz_Scan51.j12,JFz_Scan51.b00_length,JFz_Scan51.b01_length,JFz_Scan51.b02_length,JFz_Scan51.b03_length,JFz_Scan51.b04_length,JFz_Scan51.b05_length,JFz_Scan51.b06_length,JFz_Scan51.b07_length,JFz_Scan51.b08_length,JFz_Scan51.b09_length,JFz_Scan51.b10_length,JFz_Scan51.b11_length,JFz_Scan51.b12_length,JFz_Scan51.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell14
theorem encoded14 : CandidateParserByteOrder.arrayBytes16 cell14=encodeQM31LE limbs14 := by
  funext i
  fin_cases i <;> rfl
theorem parser14 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell14)=
    ok (some ⟨⟨575244962#u32,958530204#u32⟩,⟨546510302#u32,906919523#u32⟩⟩) :=
  JFr_EncodedCell.parser cell14 limbs14 encoded14
#print axioms encoded14
#print axioms parser14
def cell15 : Array U8 16#usize := ⟨[2#u8,182#u8,138#u8,119#u8,113#u8,175#u8,90#u8,47#u8,176#u8,48#u8,148#u8,53#u8,222#u8,145#u8,60#u8,22#u8],by rfl⟩
def limbs15 : QM31Limbs := ![⟨2005579266,by change 2005579266<2147483647;omega⟩,⟨794472305,by change 794472305<2147483647;omega⟩,⟨898904240,by change 898904240<2147483647;omega⟩,⟨373068254,by change 373068254<2147483647;omega⟩]
theorem rawCell15 : (raw.drop 240).take 16=cell15.val := by
  simp only [raw,JFz_Scan51.data,JFz_Scan51.j00,JFz_Scan51.j01,JFz_Scan51.j02,JFz_Scan51.j03,JFz_Scan51.j04,JFz_Scan51.j05,JFz_Scan51.j06,JFz_Scan51.j07,JFz_Scan51.j08,JFz_Scan51.j09,JFz_Scan51.j10,JFz_Scan51.j11,JFz_Scan51.j12,JFz_Scan51.b00_length,JFz_Scan51.b01_length,JFz_Scan51.b02_length,JFz_Scan51.b03_length,JFz_Scan51.b04_length,JFz_Scan51.b05_length,JFz_Scan51.b06_length,JFz_Scan51.b07_length,JFz_Scan51.b08_length,JFz_Scan51.b09_length,JFz_Scan51.b10_length,JFz_Scan51.b11_length,JFz_Scan51.b12_length,JFz_Scan51.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell15
theorem encoded15 : CandidateParserByteOrder.arrayBytes16 cell15=encodeQM31LE limbs15 := by
  funext i
  fin_cases i <;> rfl
theorem parser15 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell15)=
    ok (some ⟨⟨2005579266#u32,794472305#u32⟩,⟨898904240#u32,373068254#u32⟩⟩) :=
  JFr_EncodedCell.parser cell15 limbs15 encoded15
#print axioms encoded15
#print axioms parser15
def cell16 : Array U8 16#usize := ⟨[90#u8,29#u8,148#u8,68#u8,156#u8,138#u8,180#u8,44#u8,15#u8,200#u8,54#u8,13#u8,56#u8,207#u8,164#u8,82#u8],by rfl⟩
def limbs16 : QM31Limbs := ![⟨1150557530,by change 1150557530<2147483647;omega⟩,⟨750029468,by change 750029468<2147483647;omega⟩,⟨221693967,by change 221693967<2147483647;omega⟩,⟨1386532664,by change 1386532664<2147483647;omega⟩]
theorem rawCell16 : (raw.drop 256).take 16=cell16.val := by
  simp only [raw,JFz_Scan51.data,JFz_Scan51.j00,JFz_Scan51.j01,JFz_Scan51.j02,JFz_Scan51.j03,JFz_Scan51.j04,JFz_Scan51.j05,JFz_Scan51.j06,JFz_Scan51.j07,JFz_Scan51.j08,JFz_Scan51.j09,JFz_Scan51.j10,JFz_Scan51.j11,JFz_Scan51.j12,JFz_Scan51.b00_length,JFz_Scan51.b01_length,JFz_Scan51.b02_length,JFz_Scan51.b03_length,JFz_Scan51.b04_length,JFz_Scan51.b05_length,JFz_Scan51.b06_length,JFz_Scan51.b07_length,JFz_Scan51.b08_length,JFz_Scan51.b09_length,JFz_Scan51.b10_length,JFz_Scan51.b11_length,JFz_Scan51.b12_length,JFz_Scan51.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell16
theorem encoded16 : CandidateParserByteOrder.arrayBytes16 cell16=encodeQM31LE limbs16 := by
  funext i
  fin_cases i <;> rfl
theorem parser16 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell16)=
    ok (some ⟨⟨1150557530#u32,750029468#u32⟩,⟨221693967#u32,1386532664#u32⟩⟩) :=
  JFr_EncodedCell.parser cell16 limbs16 encoded16
#print axioms encoded16
#print axioms parser16
def cell17 : Array U8 16#usize := ⟨[197#u8,130#u8,46#u8,118#u8,241#u8,73#u8,174#u8,52#u8,245#u8,36#u8,237#u8,31#u8,134#u8,115#u8,219#u8,14#u8],by rfl⟩
def limbs17 : QM31Limbs := ![⟨1982759621,by change 1982759621<2147483647;omega⟩,⟨883837425,by change 883837425<2147483647;omega⟩,⟨535635189,by change 535635189<2147483647;omega⟩,⟨249262982,by change 249262982<2147483647;omega⟩]
theorem rawCell17 : (raw.drop 272).take 16=cell17.val := by
  simp only [raw,JFz_Scan51.data,JFz_Scan51.j00,JFz_Scan51.j01,JFz_Scan51.j02,JFz_Scan51.j03,JFz_Scan51.j04,JFz_Scan51.j05,JFz_Scan51.j06,JFz_Scan51.j07,JFz_Scan51.j08,JFz_Scan51.j09,JFz_Scan51.j10,JFz_Scan51.j11,JFz_Scan51.j12,JFz_Scan51.b00_length,JFz_Scan51.b01_length,JFz_Scan51.b02_length,JFz_Scan51.b03_length,JFz_Scan51.b04_length,JFz_Scan51.b05_length,JFz_Scan51.b06_length,JFz_Scan51.b07_length,JFz_Scan51.b08_length,JFz_Scan51.b09_length,JFz_Scan51.b10_length,JFz_Scan51.b11_length,JFz_Scan51.b12_length,JFz_Scan51.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell17
theorem encoded17 : CandidateParserByteOrder.arrayBytes16 cell17=encodeQM31LE limbs17 := by
  funext i
  fin_cases i <;> rfl
theorem parser17 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell17)=
    ok (some ⟨⟨1982759621#u32,883837425#u32⟩,⟨535635189#u32,249262982#u32⟩⟩) :=
  JFr_EncodedCell.parser cell17 limbs17 encoded17
#print axioms encoded17
#print axioms parser17
def cell18 : Array U8 16#usize := ⟨[136#u8,220#u8,193#u8,70#u8,39#u8,22#u8,108#u8,66#u8,247#u8,210#u8,174#u8,57#u8,216#u8,80#u8,147#u8,61#u8],by rfl⟩
def limbs18 : QM31Limbs := ![⟨1187110024,by change 1187110024<2147483647;omega⟩,⟨1114379815,by change 1114379815<2147483647;omega⟩,⟨967758583,by change 967758583<2147483647;omega⟩,⟨1033064664,by change 1033064664<2147483647;omega⟩]
theorem rawCell18 : (raw.drop 288).take 16=cell18.val := by
  simp only [raw,JFz_Scan51.data,JFz_Scan51.j00,JFz_Scan51.j01,JFz_Scan51.j02,JFz_Scan51.j03,JFz_Scan51.j04,JFz_Scan51.j05,JFz_Scan51.j06,JFz_Scan51.j07,JFz_Scan51.j08,JFz_Scan51.j09,JFz_Scan51.j10,JFz_Scan51.j11,JFz_Scan51.j12,JFz_Scan51.b00_length,JFz_Scan51.b01_length,JFz_Scan51.b02_length,JFz_Scan51.b03_length,JFz_Scan51.b04_length,JFz_Scan51.b05_length,JFz_Scan51.b06_length,JFz_Scan51.b07_length,JFz_Scan51.b08_length,JFz_Scan51.b09_length,JFz_Scan51.b10_length,JFz_Scan51.b11_length,JFz_Scan51.b12_length,JFz_Scan51.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell18
theorem encoded18 : CandidateParserByteOrder.arrayBytes16 cell18=encodeQM31LE limbs18 := by
  funext i
  fin_cases i <;> rfl
theorem parser18 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell18)=
    ok (some ⟨⟨1187110024#u32,1114379815#u32⟩,⟨967758583#u32,1033064664#u32⟩⟩) :=
  JFr_EncodedCell.parser cell18 limbs18 encoded18
#print axioms encoded18
#print axioms parser18
def cell19 : Array U8 16#usize := ⟨[146#u8,80#u8,136#u8,116#u8,252#u8,108#u8,224#u8,42#u8,246#u8,229#u8,156#u8,7#u8,124#u8,222#u8,252#u8,100#u8],by rfl⟩
def limbs19 : QM31Limbs := ![⟨1955090578,by change 1955090578<2147483647;omega⟩,⟨719351036,by change 719351036<2147483647;omega⟩,⟨127722998,by change 127722998<2147483647;omega⟩,⟨1694293628,by change 1694293628<2147483647;omega⟩]
theorem rawCell19 : (raw.drop 304).take 16=cell19.val := by
  simp only [raw,JFz_Scan51.data,JFz_Scan51.j00,JFz_Scan51.j01,JFz_Scan51.j02,JFz_Scan51.j03,JFz_Scan51.j04,JFz_Scan51.j05,JFz_Scan51.j06,JFz_Scan51.j07,JFz_Scan51.j08,JFz_Scan51.j09,JFz_Scan51.j10,JFz_Scan51.j11,JFz_Scan51.j12,JFz_Scan51.b00_length,JFz_Scan51.b01_length,JFz_Scan51.b02_length,JFz_Scan51.b03_length,JFz_Scan51.b04_length,JFz_Scan51.b05_length,JFz_Scan51.b06_length,JFz_Scan51.b07_length,JFz_Scan51.b08_length,JFz_Scan51.b09_length,JFz_Scan51.b10_length,JFz_Scan51.b11_length,JFz_Scan51.b12_length,JFz_Scan51.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell19
theorem encoded19 : CandidateParserByteOrder.arrayBytes16 cell19=encodeQM31LE limbs19 := by
  funext i
  fin_cases i <;> rfl
theorem parser19 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell19)=
    ok (some ⟨⟨1955090578#u32,719351036#u32⟩,⟨127722998#u32,1694293628#u32⟩⟩) :=
  JFr_EncodedCell.parser cell19 limbs19 encoded19
#print axioms encoded19
#print axioms parser19
def cell20 : Array U8 16#usize := ⟨[222#u8,6#u8,168#u8,95#u8,167#u8,20#u8,192#u8,86#u8,37#u8,88#u8,145#u8,6#u8,207#u8,69#u8,210#u8,114#u8],by rfl⟩
def limbs20 : QM31Limbs := ![⟨1604847326,by change 1604847326<2147483647;omega⟩,⟨1455428775,by change 1455428775<2147483647;omega⟩,⟨110188581,by change 110188581<2147483647;omega⟩,⟨1926383055,by change 1926383055<2147483647;omega⟩]
theorem rawCell20 : (raw.drop 320).take 16=cell20.val := by
  simp only [raw,JFz_Scan51.data,JFz_Scan51.j00,JFz_Scan51.j01,JFz_Scan51.j02,JFz_Scan51.j03,JFz_Scan51.j04,JFz_Scan51.j05,JFz_Scan51.j06,JFz_Scan51.j07,JFz_Scan51.j08,JFz_Scan51.j09,JFz_Scan51.j10,JFz_Scan51.j11,JFz_Scan51.j12,JFz_Scan51.b00_length,JFz_Scan51.b01_length,JFz_Scan51.b02_length,JFz_Scan51.b03_length,JFz_Scan51.b04_length,JFz_Scan51.b05_length,JFz_Scan51.b06_length,JFz_Scan51.b07_length,JFz_Scan51.b08_length,JFz_Scan51.b09_length,JFz_Scan51.b10_length,JFz_Scan51.b11_length,JFz_Scan51.b12_length,JFz_Scan51.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell20
theorem encoded20 : CandidateParserByteOrder.arrayBytes16 cell20=encodeQM31LE limbs20 := by
  funext i
  fin_cases i <;> rfl
theorem parser20 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell20)=
    ok (some ⟨⟨1604847326#u32,1455428775#u32⟩,⟨110188581#u32,1926383055#u32⟩⟩) :=
  JFr_EncodedCell.parser cell20 limbs20 encoded20
#print axioms encoded20
#print axioms parser20
def cell21 : Array U8 16#usize := ⟨[224#u8,133#u8,223#u8,119#u8,75#u8,232#u8,250#u8,98#u8,103#u8,9#u8,229#u8,48#u8,248#u8,117#u8,46#u8,6#u8],by rfl⟩
def limbs21 : QM31Limbs := ![⟨2011137504,by change 2011137504<2147483647;omega⟩,⟨1660610635,by change 1660610635<2147483647;omega⟩,⟨820316519,by change 820316519<2147483647;omega⟩,⟨103708152,by change 103708152<2147483647;omega⟩]
theorem rawCell21 : (raw.drop 336).take 16=cell21.val := by
  simp only [raw,JFz_Scan51.data,JFz_Scan51.j00,JFz_Scan51.j01,JFz_Scan51.j02,JFz_Scan51.j03,JFz_Scan51.j04,JFz_Scan51.j05,JFz_Scan51.j06,JFz_Scan51.j07,JFz_Scan51.j08,JFz_Scan51.j09,JFz_Scan51.j10,JFz_Scan51.j11,JFz_Scan51.j12,JFz_Scan51.b00_length,JFz_Scan51.b01_length,JFz_Scan51.b02_length,JFz_Scan51.b03_length,JFz_Scan51.b04_length,JFz_Scan51.b05_length,JFz_Scan51.b06_length,JFz_Scan51.b07_length,JFz_Scan51.b08_length,JFz_Scan51.b09_length,JFz_Scan51.b10_length,JFz_Scan51.b11_length,JFz_Scan51.b12_length,JFz_Scan51.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell21
theorem encoded21 : CandidateParserByteOrder.arrayBytes16 cell21=encodeQM31LE limbs21 := by
  funext i
  fin_cases i <;> rfl
theorem parser21 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell21)=
    ok (some ⟨⟨2011137504#u32,1660610635#u32⟩,⟨820316519#u32,103708152#u32⟩⟩) :=
  JFr_EncodedCell.parser cell21 limbs21 encoded21
#print axioms encoded21
#print axioms parser21
def cell22 : Array U8 16#usize := ⟨[145#u8,230#u8,173#u8,116#u8,155#u8,93#u8,177#u8,50#u8,21#u8,118#u8,210#u8,21#u8,48#u8,19#u8,59#u8,82#u8],by rfl⟩
def limbs22 : QM31Limbs := ![⟨1957553809,by change 1957553809<2147483647;omega⟩,⟨850484635,by change 850484635<2147483647;omega⟩,⟨366114325,by change 366114325<2147483647;omega⟩,⟨1379603248,by change 1379603248<2147483647;omega⟩]
theorem rawCell22 : (raw.drop 352).take 16=cell22.val := by
  simp only [raw,JFz_Scan51.data,JFz_Scan51.j00,JFz_Scan51.j01,JFz_Scan51.j02,JFz_Scan51.j03,JFz_Scan51.j04,JFz_Scan51.j05,JFz_Scan51.j06,JFz_Scan51.j07,JFz_Scan51.j08,JFz_Scan51.j09,JFz_Scan51.j10,JFz_Scan51.j11,JFz_Scan51.j12,JFz_Scan51.b00_length,JFz_Scan51.b01_length,JFz_Scan51.b02_length,JFz_Scan51.b03_length,JFz_Scan51.b04_length,JFz_Scan51.b05_length,JFz_Scan51.b06_length,JFz_Scan51.b07_length,JFz_Scan51.b08_length,JFz_Scan51.b09_length,JFz_Scan51.b10_length,JFz_Scan51.b11_length,JFz_Scan51.b12_length,JFz_Scan51.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell22
theorem encoded22 : CandidateParserByteOrder.arrayBytes16 cell22=encodeQM31LE limbs22 := by
  funext i
  fin_cases i <;> rfl
theorem parser22 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell22)=
    ok (some ⟨⟨1957553809#u32,850484635#u32⟩,⟨366114325#u32,1379603248#u32⟩⟩) :=
  JFr_EncodedCell.parser cell22 limbs22 encoded22
#print axioms encoded22
#print axioms parser22
def cell23 : Array U8 16#usize := ⟨[177#u8,228#u8,88#u8,88#u8,49#u8,197#u8,180#u8,21#u8,198#u8,246#u8,106#u8,92#u8,119#u8,253#u8,136#u8,16#u8],by rfl⟩
def limbs23 : QM31Limbs := ![⟨1482220721,by change 1482220721<2147483647;omega⟩,⟨364168497,by change 364168497<2147483647;omega⟩,⟨1550513862,by change 1550513862<2147483647;omega⟩,⟨277413239,by change 277413239<2147483647;omega⟩]
theorem rawCell23 : (raw.drop 368).take 16=cell23.val := by
  simp only [raw,JFz_Scan51.data,JFz_Scan51.j00,JFz_Scan51.j01,JFz_Scan51.j02,JFz_Scan51.j03,JFz_Scan51.j04,JFz_Scan51.j05,JFz_Scan51.j06,JFz_Scan51.j07,JFz_Scan51.j08,JFz_Scan51.j09,JFz_Scan51.j10,JFz_Scan51.j11,JFz_Scan51.j12,JFz_Scan51.b00_length,JFz_Scan51.b01_length,JFz_Scan51.b02_length,JFz_Scan51.b03_length,JFz_Scan51.b04_length,JFz_Scan51.b05_length,JFz_Scan51.b06_length,JFz_Scan51.b07_length,JFz_Scan51.b08_length,JFz_Scan51.b09_length,JFz_Scan51.b10_length,JFz_Scan51.b11_length,JFz_Scan51.b12_length,JFz_Scan51.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell23
theorem encoded23 : CandidateParserByteOrder.arrayBytes16 cell23=encodeQM31LE limbs23 := by
  funext i
  fin_cases i <;> rfl
theorem parser23 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell23)=
    ok (some ⟨⟨1482220721#u32,364168497#u32⟩,⟨1550513862#u32,277413239#u32⟩⟩) :=
  JFr_EncodedCell.parser cell23 limbs23 encoded23
#print axioms encoded23
#print axioms parser23
def cell24 : Array U8 16#usize := ⟨[246#u8,252#u8,138#u8,48#u8,155#u8,34#u8,170#u8,40#u8,171#u8,56#u8,155#u8,116#u8,8#u8,231#u8,35#u8,62#u8],by rfl⟩
def limbs24 : QM31Limbs := ![⟨814415094,by change 814415094<2147483647;omega⟩,⟨682238619,by change 682238619<2147483647;omega⟩,⟨1956329643,by change 1956329643<2147483647;omega⟩,⟨1042540296,by change 1042540296<2147483647;omega⟩]
theorem rawCell24 : (raw.drop 384).take 16=cell24.val := by
  simp only [raw,JFz_Scan51.data,JFz_Scan51.j00,JFz_Scan51.j01,JFz_Scan51.j02,JFz_Scan51.j03,JFz_Scan51.j04,JFz_Scan51.j05,JFz_Scan51.j06,JFz_Scan51.j07,JFz_Scan51.j08,JFz_Scan51.j09,JFz_Scan51.j10,JFz_Scan51.j11,JFz_Scan51.j12,JFz_Scan51.b00_length,JFz_Scan51.b01_length,JFz_Scan51.b02_length,JFz_Scan51.b03_length,JFz_Scan51.b04_length,JFz_Scan51.b05_length,JFz_Scan51.b06_length,JFz_Scan51.b07_length,JFz_Scan51.b08_length,JFz_Scan51.b09_length,JFz_Scan51.b10_length,JFz_Scan51.b11_length,JFz_Scan51.b12_length,JFz_Scan51.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell24
theorem encoded24 : CandidateParserByteOrder.arrayBytes16 cell24=encodeQM31LE limbs24 := by
  funext i
  fin_cases i <;> rfl
theorem parser24 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell24)=
    ok (some ⟨⟨814415094#u32,682238619#u32⟩,⟨1956329643#u32,1042540296#u32⟩⟩) :=
  JFr_EncodedCell.parser cell24 limbs24 encoded24
#print axioms encoded24
#print axioms parser24
def cell25 : Array U8 16#usize := ⟨[176#u8,59#u8,24#u8,93#u8,213#u8,101#u8,135#u8,40#u8,107#u8,126#u8,84#u8,6#u8,192#u8,211#u8,236#u8,86#u8],by rfl⟩
def limbs25 : QM31Limbs := ![⟨1561869232,by change 1561869232<2147483647;omega⟩,⟨679962069,by change 679962069<2147483647;omega⟩,⟨106200683,by change 106200683<2147483647;omega⟩,⟨1458361280,by change 1458361280<2147483647;omega⟩]
theorem rawCell25 : (raw.drop 400).take 16=cell25.val := by
  simp only [raw,JFz_Scan51.data,JFz_Scan51.j00,JFz_Scan51.j01,JFz_Scan51.j02,JFz_Scan51.j03,JFz_Scan51.j04,JFz_Scan51.j05,JFz_Scan51.j06,JFz_Scan51.j07,JFz_Scan51.j08,JFz_Scan51.j09,JFz_Scan51.j10,JFz_Scan51.j11,JFz_Scan51.j12,JFz_Scan51.b00_length,JFz_Scan51.b01_length,JFz_Scan51.b02_length,JFz_Scan51.b03_length,JFz_Scan51.b04_length,JFz_Scan51.b05_length,JFz_Scan51.b06_length,JFz_Scan51.b07_length,JFz_Scan51.b08_length,JFz_Scan51.b09_length,JFz_Scan51.b10_length,JFz_Scan51.b11_length,JFz_Scan51.b12_length,JFz_Scan51.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell25
theorem encoded25 : CandidateParserByteOrder.arrayBytes16 cell25=encodeQM31LE limbs25 := by
  funext i
  fin_cases i <;> rfl
theorem parser25 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell25)=
    ok (some ⟨⟨1561869232#u32,679962069#u32⟩,⟨106200683#u32,1458361280#u32⟩⟩) :=
  JFr_EncodedCell.parser cell25 limbs25 encoded25
#print axioms encoded25
#print axioms parser25
def cell26 : Array U8 16#usize := ⟨[80#u8,65#u8,147#u8,59#u8,80#u8,111#u8,15#u8,43#u8,67#u8,68#u8,204#u8,18#u8,144#u8,26#u8,110#u8,125#u8],by rfl⟩
def limbs26 : QM31Limbs := ![⟨999506256,by change 999506256<2147483647;omega⟩,⟨722431824,by change 722431824<2147483647;omega⟩,⟨315376707,by change 315376707<2147483647;omega⟩,⟨2104367760,by change 2104367760<2147483647;omega⟩]
theorem rawCell26 : (raw.drop 416).take 16=cell26.val := by
  simp only [raw,JFz_Scan51.data,JFz_Scan51.j00,JFz_Scan51.j01,JFz_Scan51.j02,JFz_Scan51.j03,JFz_Scan51.j04,JFz_Scan51.j05,JFz_Scan51.j06,JFz_Scan51.j07,JFz_Scan51.j08,JFz_Scan51.j09,JFz_Scan51.j10,JFz_Scan51.j11,JFz_Scan51.j12,JFz_Scan51.b00_length,JFz_Scan51.b01_length,JFz_Scan51.b02_length,JFz_Scan51.b03_length,JFz_Scan51.b04_length,JFz_Scan51.b05_length,JFz_Scan51.b06_length,JFz_Scan51.b07_length,JFz_Scan51.b08_length,JFz_Scan51.b09_length,JFz_Scan51.b10_length,JFz_Scan51.b11_length,JFz_Scan51.b12_length,JFz_Scan51.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell26
theorem encoded26 : CandidateParserByteOrder.arrayBytes16 cell26=encodeQM31LE limbs26 := by
  funext i
  fin_cases i <;> rfl
theorem parser26 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell26)=
    ok (some ⟨⟨999506256#u32,722431824#u32⟩,⟨315376707#u32,2104367760#u32⟩⟩) :=
  JFr_EncodedCell.parser cell26 limbs26 encoded26
#print axioms encoded26
#print axioms parser26
def cell27 : Array U8 16#usize := ⟨[48#u8,156#u8,78#u8,116#u8,73#u8,86#u8,116#u8,23#u8,253#u8,36#u8,174#u8,124#u8,14#u8,55#u8,170#u8,53#u8],by rfl⟩
def limbs27 : QM31Limbs := ![⟨1951308848,by change 1951308848<2147483647;omega⟩,⟨393500233,by change 393500233<2147483647;omega⟩,⟨2091787517,by change 2091787517<2147483647;omega⟩,⟨900347662,by change 900347662<2147483647;omega⟩]
theorem rawCell27 : (raw.drop 432).take 16=cell27.val := by
  simp only [raw,JFz_Scan51.data,JFz_Scan51.j00,JFz_Scan51.j01,JFz_Scan51.j02,JFz_Scan51.j03,JFz_Scan51.j04,JFz_Scan51.j05,JFz_Scan51.j06,JFz_Scan51.j07,JFz_Scan51.j08,JFz_Scan51.j09,JFz_Scan51.j10,JFz_Scan51.j11,JFz_Scan51.j12,JFz_Scan51.b00_length,JFz_Scan51.b01_length,JFz_Scan51.b02_length,JFz_Scan51.b03_length,JFz_Scan51.b04_length,JFz_Scan51.b05_length,JFz_Scan51.b06_length,JFz_Scan51.b07_length,JFz_Scan51.b08_length,JFz_Scan51.b09_length,JFz_Scan51.b10_length,JFz_Scan51.b11_length,JFz_Scan51.b12_length,JFz_Scan51.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell27
theorem encoded27 : CandidateParserByteOrder.arrayBytes16 cell27=encodeQM31LE limbs27 := by
  funext i
  fin_cases i <;> rfl
theorem parser27 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell27)=
    ok (some ⟨⟨1951308848#u32,393500233#u32⟩,⟨2091787517#u32,900347662#u32⟩⟩) :=
  JFr_EncodedCell.parser cell27 limbs27 encoded27
#print axioms encoded27
#print axioms parser27
end AspisR1.JFr_Bytes03
