import NDO_JFr_Data05
import NDO_JFr_EncodedCell
import NDO_JFz_Scan53
set_option autoImplicit false
namespace AspisR1.JFr_Bytes05
open Aeneas Aeneas.Std Result RetainedFieldByteCodec
open AspisR1PublicPreparation
open AspisS1ExtractedRoundChildren
def raw : List U8 := JFz_Scan53.data
theorem rawLength : raw.length=448 := JFz_Scan53.length
#print axioms rawLength
theorem selected : (JFx_NativeBytes.proof.val.drop 2441).take 448=raw := JFz_Scan53.selected
#print axioms selected
def cell00 : Array U8 16#usize := ⟨[18#u8,189#u8,205#u8,73#u8,210#u8,9#u8,93#u8,86#u8,43#u8,96#u8,58#u8,65#u8,111#u8,0#u8,141#u8,108#u8],by rfl⟩
def limbs00 : QM31Limbs := ![⟨1238220050,by change 1238220050<2147483647;omega⟩,⟨1448937938,by change 1448937938<2147483647;omega⟩,⟨1094344747,by change 1094344747<2147483647;omega⟩,⟨1821180015,by change 1821180015<2147483647;omega⟩]
theorem rawCell00 : (raw.drop 0).take 16=cell00.val := by
  simp only [raw,JFz_Scan53.data,JFz_Scan53.j00,JFz_Scan53.j01,JFz_Scan53.j02,JFz_Scan53.j03,JFz_Scan53.j04,JFz_Scan53.j05,JFz_Scan53.j06,JFz_Scan53.j07,JFz_Scan53.j08,JFz_Scan53.j09,JFz_Scan53.j10,JFz_Scan53.j11,JFz_Scan53.j12,JFz_Scan53.b00_length,JFz_Scan53.b01_length,JFz_Scan53.b02_length,JFz_Scan53.b03_length,JFz_Scan53.b04_length,JFz_Scan53.b05_length,JFz_Scan53.b06_length,JFz_Scan53.b07_length,JFz_Scan53.b08_length,JFz_Scan53.b09_length,JFz_Scan53.b10_length,JFz_Scan53.b11_length,JFz_Scan53.b12_length,JFz_Scan53.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell00
theorem encoded00 : CandidateParserByteOrder.arrayBytes16 cell00=encodeQM31LE limbs00 := by
  funext i
  fin_cases i <;> rfl
theorem parser00 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell00)=
    ok (some ⟨⟨1238220050#u32,1448937938#u32⟩,⟨1094344747#u32,1821180015#u32⟩⟩) :=
  JFr_EncodedCell.parser cell00 limbs00 encoded00
#print axioms encoded00
#print axioms parser00
def cell01 : Array U8 16#usize := ⟨[15#u8,118#u8,128#u8,78#u8,251#u8,29#u8,115#u8,110#u8,148#u8,114#u8,57#u8,72#u8,228#u8,74#u8,101#u8,16#u8],by rfl⟩
def limbs01 : QM31Limbs := ![⟨1317041679,by change 1317041679<2147483647;omega⟩,⟨1853038075,by change 1853038075<2147483647;omega⟩,⟨1211724436,by change 1211724436<2147483647;omega⟩,⟨275073764,by change 275073764<2147483647;omega⟩]
theorem rawCell01 : (raw.drop 16).take 16=cell01.val := by
  simp only [raw,JFz_Scan53.data,JFz_Scan53.j00,JFz_Scan53.j01,JFz_Scan53.j02,JFz_Scan53.j03,JFz_Scan53.j04,JFz_Scan53.j05,JFz_Scan53.j06,JFz_Scan53.j07,JFz_Scan53.j08,JFz_Scan53.j09,JFz_Scan53.j10,JFz_Scan53.j11,JFz_Scan53.j12,JFz_Scan53.b00_length,JFz_Scan53.b01_length,JFz_Scan53.b02_length,JFz_Scan53.b03_length,JFz_Scan53.b04_length,JFz_Scan53.b05_length,JFz_Scan53.b06_length,JFz_Scan53.b07_length,JFz_Scan53.b08_length,JFz_Scan53.b09_length,JFz_Scan53.b10_length,JFz_Scan53.b11_length,JFz_Scan53.b12_length,JFz_Scan53.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell01
theorem encoded01 : CandidateParserByteOrder.arrayBytes16 cell01=encodeQM31LE limbs01 := by
  funext i
  fin_cases i <;> rfl
theorem parser01 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell01)=
    ok (some ⟨⟨1317041679#u32,1853038075#u32⟩,⟨1211724436#u32,275073764#u32⟩⟩) :=
  JFr_EncodedCell.parser cell01 limbs01 encoded01
#print axioms encoded01
#print axioms parser01
def cell02 : Array U8 16#usize := ⟨[13#u8,116#u8,7#u8,62#u8,200#u8,191#u8,170#u8,29#u8,150#u8,182#u8,3#u8,81#u8,213#u8,244#u8,16#u8,8#u8],by rfl⟩
def limbs02 : QM31Limbs := ![⟨1040675853,by change 1040675853<2147483647;omega⟩,⟨497729480,by change 497729480<2147483647;omega⟩,⟨1359197846,by change 1359197846<2147483647;omega⟩,⟨135328981,by change 135328981<2147483647;omega⟩]
theorem rawCell02 : (raw.drop 32).take 16=cell02.val := by
  simp only [raw,JFz_Scan53.data,JFz_Scan53.j00,JFz_Scan53.j01,JFz_Scan53.j02,JFz_Scan53.j03,JFz_Scan53.j04,JFz_Scan53.j05,JFz_Scan53.j06,JFz_Scan53.j07,JFz_Scan53.j08,JFz_Scan53.j09,JFz_Scan53.j10,JFz_Scan53.j11,JFz_Scan53.j12,JFz_Scan53.b00_length,JFz_Scan53.b01_length,JFz_Scan53.b02_length,JFz_Scan53.b03_length,JFz_Scan53.b04_length,JFz_Scan53.b05_length,JFz_Scan53.b06_length,JFz_Scan53.b07_length,JFz_Scan53.b08_length,JFz_Scan53.b09_length,JFz_Scan53.b10_length,JFz_Scan53.b11_length,JFz_Scan53.b12_length,JFz_Scan53.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell02
theorem encoded02 : CandidateParserByteOrder.arrayBytes16 cell02=encodeQM31LE limbs02 := by
  funext i
  fin_cases i <;> rfl
theorem parser02 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell02)=
    ok (some ⟨⟨1040675853#u32,497729480#u32⟩,⟨1359197846#u32,135328981#u32⟩⟩) :=
  JFr_EncodedCell.parser cell02 limbs02 encoded02
#print axioms encoded02
#print axioms parser02
def cell03 : Array U8 16#usize := ⟨[163#u8,130#u8,67#u8,19#u8,81#u8,148#u8,7#u8,85#u8,121#u8,211#u8,76#u8,38#u8,188#u8,198#u8,37#u8,11#u8],by rfl⟩
def limbs03 : QM31Limbs := ![⟨323191459,by change 323191459<2147483647;omega⟩,⟨1426560081,by change 1426560081<2147483647;omega⟩,⟨642569081,by change 642569081<2147483647;omega⟩,⟨187025084,by change 187025084<2147483647;omega⟩]
theorem rawCell03 : (raw.drop 48).take 16=cell03.val := by
  simp only [raw,JFz_Scan53.data,JFz_Scan53.j00,JFz_Scan53.j01,JFz_Scan53.j02,JFz_Scan53.j03,JFz_Scan53.j04,JFz_Scan53.j05,JFz_Scan53.j06,JFz_Scan53.j07,JFz_Scan53.j08,JFz_Scan53.j09,JFz_Scan53.j10,JFz_Scan53.j11,JFz_Scan53.j12,JFz_Scan53.b00_length,JFz_Scan53.b01_length,JFz_Scan53.b02_length,JFz_Scan53.b03_length,JFz_Scan53.b04_length,JFz_Scan53.b05_length,JFz_Scan53.b06_length,JFz_Scan53.b07_length,JFz_Scan53.b08_length,JFz_Scan53.b09_length,JFz_Scan53.b10_length,JFz_Scan53.b11_length,JFz_Scan53.b12_length,JFz_Scan53.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell03
theorem encoded03 : CandidateParserByteOrder.arrayBytes16 cell03=encodeQM31LE limbs03 := by
  funext i
  fin_cases i <;> rfl
theorem parser03 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell03)=
    ok (some ⟨⟨323191459#u32,1426560081#u32⟩,⟨642569081#u32,187025084#u32⟩⟩) :=
  JFr_EncodedCell.parser cell03 limbs03 encoded03
#print axioms encoded03
#print axioms parser03
def cell04 : Array U8 16#usize := ⟨[78#u8,105#u8,219#u8,75#u8,245#u8,176#u8,218#u8,37#u8,252#u8,210#u8,102#u8,39#u8,94#u8,116#u8,253#u8,47#u8],by rfl⟩
def limbs04 : QM31Limbs := ![⟨1272670542,by change 1272670542<2147483647;omega⟩,⟨635089141,by change 635089141<2147483647;omega⟩,⟨661050108,by change 661050108<2147483647;omega⟩,⟨805139550,by change 805139550<2147483647;omega⟩]
theorem rawCell04 : (raw.drop 64).take 16=cell04.val := by
  simp only [raw,JFz_Scan53.data,JFz_Scan53.j00,JFz_Scan53.j01,JFz_Scan53.j02,JFz_Scan53.j03,JFz_Scan53.j04,JFz_Scan53.j05,JFz_Scan53.j06,JFz_Scan53.j07,JFz_Scan53.j08,JFz_Scan53.j09,JFz_Scan53.j10,JFz_Scan53.j11,JFz_Scan53.j12,JFz_Scan53.b00_length,JFz_Scan53.b01_length,JFz_Scan53.b02_length,JFz_Scan53.b03_length,JFz_Scan53.b04_length,JFz_Scan53.b05_length,JFz_Scan53.b06_length,JFz_Scan53.b07_length,JFz_Scan53.b08_length,JFz_Scan53.b09_length,JFz_Scan53.b10_length,JFz_Scan53.b11_length,JFz_Scan53.b12_length,JFz_Scan53.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell04
theorem encoded04 : CandidateParserByteOrder.arrayBytes16 cell04=encodeQM31LE limbs04 := by
  funext i
  fin_cases i <;> rfl
theorem parser04 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell04)=
    ok (some ⟨⟨1272670542#u32,635089141#u32⟩,⟨661050108#u32,805139550#u32⟩⟩) :=
  JFr_EncodedCell.parser cell04 limbs04 encoded04
#print axioms encoded04
#print axioms parser04
def cell05 : Array U8 16#usize := ⟨[76#u8,229#u8,62#u8,100#u8,98#u8,14#u8,90#u8,90#u8,139#u8,106#u8,224#u8,5#u8,157#u8,224#u8,246#u8,48#u8],by rfl⟩
def limbs05 : QM31Limbs := ![⟨1681843532,by change 1681843532<2147483647;omega⟩,⟨1515851362,by change 1515851362<2147483647;omega⟩,⟨98593419,by change 98593419<2147483647;omega⟩,⟨821485725,by change 821485725<2147483647;omega⟩]
theorem rawCell05 : (raw.drop 80).take 16=cell05.val := by
  simp only [raw,JFz_Scan53.data,JFz_Scan53.j00,JFz_Scan53.j01,JFz_Scan53.j02,JFz_Scan53.j03,JFz_Scan53.j04,JFz_Scan53.j05,JFz_Scan53.j06,JFz_Scan53.j07,JFz_Scan53.j08,JFz_Scan53.j09,JFz_Scan53.j10,JFz_Scan53.j11,JFz_Scan53.j12,JFz_Scan53.b00_length,JFz_Scan53.b01_length,JFz_Scan53.b02_length,JFz_Scan53.b03_length,JFz_Scan53.b04_length,JFz_Scan53.b05_length,JFz_Scan53.b06_length,JFz_Scan53.b07_length,JFz_Scan53.b08_length,JFz_Scan53.b09_length,JFz_Scan53.b10_length,JFz_Scan53.b11_length,JFz_Scan53.b12_length,JFz_Scan53.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell05
theorem encoded05 : CandidateParserByteOrder.arrayBytes16 cell05=encodeQM31LE limbs05 := by
  funext i
  fin_cases i <;> rfl
theorem parser05 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell05)=
    ok (some ⟨⟨1681843532#u32,1515851362#u32⟩,⟨98593419#u32,821485725#u32⟩⟩) :=
  JFr_EncodedCell.parser cell05 limbs05 encoded05
#print axioms encoded05
#print axioms parser05
def cell06 : Array U8 16#usize := ⟨[46#u8,212#u8,145#u8,45#u8,137#u8,201#u8,178#u8,32#u8,126#u8,81#u8,197#u8,116#u8,138#u8,137#u8,240#u8,45#u8],by rfl⟩
def limbs06 : QM31Limbs := ![⟨764531758,by change 764531758<2147483647;omega⟩,⟨548587913,by change 548587913<2147483647;omega⟩,⟨1959088510,by change 1959088510<2147483647;omega⟩,⟨770738570,by change 770738570<2147483647;omega⟩]
theorem rawCell06 : (raw.drop 96).take 16=cell06.val := by
  simp only [raw,JFz_Scan53.data,JFz_Scan53.j00,JFz_Scan53.j01,JFz_Scan53.j02,JFz_Scan53.j03,JFz_Scan53.j04,JFz_Scan53.j05,JFz_Scan53.j06,JFz_Scan53.j07,JFz_Scan53.j08,JFz_Scan53.j09,JFz_Scan53.j10,JFz_Scan53.j11,JFz_Scan53.j12,JFz_Scan53.b00_length,JFz_Scan53.b01_length,JFz_Scan53.b02_length,JFz_Scan53.b03_length,JFz_Scan53.b04_length,JFz_Scan53.b05_length,JFz_Scan53.b06_length,JFz_Scan53.b07_length,JFz_Scan53.b08_length,JFz_Scan53.b09_length,JFz_Scan53.b10_length,JFz_Scan53.b11_length,JFz_Scan53.b12_length,JFz_Scan53.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell06
theorem encoded06 : CandidateParserByteOrder.arrayBytes16 cell06=encodeQM31LE limbs06 := by
  funext i
  fin_cases i <;> rfl
theorem parser06 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell06)=
    ok (some ⟨⟨764531758#u32,548587913#u32⟩,⟨1959088510#u32,770738570#u32⟩⟩) :=
  JFr_EncodedCell.parser cell06 limbs06 encoded06
#print axioms encoded06
#print axioms parser06
def cell07 : Array U8 16#usize := ⟨[55#u8,241#u8,174#u8,16#u8,45#u8,121#u8,229#u8,37#u8,15#u8,63#u8,232#u8,70#u8,227#u8,178#u8,147#u8,53#u8],by rfl⟩
def limbs07 : QM31Limbs := ![⟨279900471,by change 279900471<2147483647;omega⟩,⟨635795757,by change 635795757<2147483647;omega⟩,⟨1189625615,by change 1189625615<2147483647;omega⟩,⟨898872035,by change 898872035<2147483647;omega⟩]
theorem rawCell07 : (raw.drop 112).take 16=cell07.val := by
  simp only [raw,JFz_Scan53.data,JFz_Scan53.j00,JFz_Scan53.j01,JFz_Scan53.j02,JFz_Scan53.j03,JFz_Scan53.j04,JFz_Scan53.j05,JFz_Scan53.j06,JFz_Scan53.j07,JFz_Scan53.j08,JFz_Scan53.j09,JFz_Scan53.j10,JFz_Scan53.j11,JFz_Scan53.j12,JFz_Scan53.b00_length,JFz_Scan53.b01_length,JFz_Scan53.b02_length,JFz_Scan53.b03_length,JFz_Scan53.b04_length,JFz_Scan53.b05_length,JFz_Scan53.b06_length,JFz_Scan53.b07_length,JFz_Scan53.b08_length,JFz_Scan53.b09_length,JFz_Scan53.b10_length,JFz_Scan53.b11_length,JFz_Scan53.b12_length,JFz_Scan53.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell07
theorem encoded07 : CandidateParserByteOrder.arrayBytes16 cell07=encodeQM31LE limbs07 := by
  funext i
  fin_cases i <;> rfl
theorem parser07 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell07)=
    ok (some ⟨⟨279900471#u32,635795757#u32⟩,⟨1189625615#u32,898872035#u32⟩⟩) :=
  JFr_EncodedCell.parser cell07 limbs07 encoded07
#print axioms encoded07
#print axioms parser07
def cell08 : Array U8 16#usize := ⟨[59#u8,241#u8,65#u8,38#u8,136#u8,104#u8,192#u8,96#u8,166#u8,161#u8,30#u8,87#u8,131#u8,236#u8,210#u8,49#u8],by rfl⟩
def limbs08 : QM31Limbs := ![⟨641855803,by change 641855803<2147483647;omega⟩,⟨1623222408,by change 1623222408<2147483647;omega⟩,⟨1461625254,by change 1461625254<2147483647;omega⟩,⟨835906691,by change 835906691<2147483647;omega⟩]
theorem rawCell08 : (raw.drop 128).take 16=cell08.val := by
  simp only [raw,JFz_Scan53.data,JFz_Scan53.j00,JFz_Scan53.j01,JFz_Scan53.j02,JFz_Scan53.j03,JFz_Scan53.j04,JFz_Scan53.j05,JFz_Scan53.j06,JFz_Scan53.j07,JFz_Scan53.j08,JFz_Scan53.j09,JFz_Scan53.j10,JFz_Scan53.j11,JFz_Scan53.j12,JFz_Scan53.b00_length,JFz_Scan53.b01_length,JFz_Scan53.b02_length,JFz_Scan53.b03_length,JFz_Scan53.b04_length,JFz_Scan53.b05_length,JFz_Scan53.b06_length,JFz_Scan53.b07_length,JFz_Scan53.b08_length,JFz_Scan53.b09_length,JFz_Scan53.b10_length,JFz_Scan53.b11_length,JFz_Scan53.b12_length,JFz_Scan53.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell08
theorem encoded08 : CandidateParserByteOrder.arrayBytes16 cell08=encodeQM31LE limbs08 := by
  funext i
  fin_cases i <;> rfl
theorem parser08 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell08)=
    ok (some ⟨⟨641855803#u32,1623222408#u32⟩,⟨1461625254#u32,835906691#u32⟩⟩) :=
  JFr_EncodedCell.parser cell08 limbs08 encoded08
#print axioms encoded08
#print axioms parser08
def cell09 : Array U8 16#usize := ⟨[84#u8,54#u8,56#u8,33#u8,18#u8,167#u8,161#u8,12#u8,119#u8,45#u8,254#u8,67#u8,16#u8,99#u8,183#u8,82#u8],by rfl⟩
def limbs09 : QM31Limbs := ![⟨557332052,by change 557332052<2147483647;omega⟩,⟨211920658,by change 211920658<2147483647;omega⟩,⟨1140731255,by change 1140731255<2147483647;omega⟩,⟨1387750160,by change 1387750160<2147483647;omega⟩]
theorem rawCell09 : (raw.drop 144).take 16=cell09.val := by
  simp only [raw,JFz_Scan53.data,JFz_Scan53.j00,JFz_Scan53.j01,JFz_Scan53.j02,JFz_Scan53.j03,JFz_Scan53.j04,JFz_Scan53.j05,JFz_Scan53.j06,JFz_Scan53.j07,JFz_Scan53.j08,JFz_Scan53.j09,JFz_Scan53.j10,JFz_Scan53.j11,JFz_Scan53.j12,JFz_Scan53.b00_length,JFz_Scan53.b01_length,JFz_Scan53.b02_length,JFz_Scan53.b03_length,JFz_Scan53.b04_length,JFz_Scan53.b05_length,JFz_Scan53.b06_length,JFz_Scan53.b07_length,JFz_Scan53.b08_length,JFz_Scan53.b09_length,JFz_Scan53.b10_length,JFz_Scan53.b11_length,JFz_Scan53.b12_length,JFz_Scan53.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell09
theorem encoded09 : CandidateParserByteOrder.arrayBytes16 cell09=encodeQM31LE limbs09 := by
  funext i
  fin_cases i <;> rfl
theorem parser09 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell09)=
    ok (some ⟨⟨557332052#u32,211920658#u32⟩,⟨1140731255#u32,1387750160#u32⟩⟩) :=
  JFr_EncodedCell.parser cell09 limbs09 encoded09
#print axioms encoded09
#print axioms parser09
def cell10 : Array U8 16#usize := ⟨[187#u8,160#u8,237#u8,115#u8,56#u8,104#u8,230#u8,97#u8,213#u8,222#u8,112#u8,98#u8,74#u8,227#u8,161#u8,88#u8],by rfl⟩
def limbs10 : QM31Limbs := ![⟨1944953019,by change 1944953019<2147483647;omega⟩,⟨1642489912,by change 1642489912<2147483647;omega⟩,⟨1651564245,by change 1651564245<2147483647;omega⟩,⟨1487004490,by change 1487004490<2147483647;omega⟩]
theorem rawCell10 : (raw.drop 160).take 16=cell10.val := by
  simp only [raw,JFz_Scan53.data,JFz_Scan53.j00,JFz_Scan53.j01,JFz_Scan53.j02,JFz_Scan53.j03,JFz_Scan53.j04,JFz_Scan53.j05,JFz_Scan53.j06,JFz_Scan53.j07,JFz_Scan53.j08,JFz_Scan53.j09,JFz_Scan53.j10,JFz_Scan53.j11,JFz_Scan53.j12,JFz_Scan53.b00_length,JFz_Scan53.b01_length,JFz_Scan53.b02_length,JFz_Scan53.b03_length,JFz_Scan53.b04_length,JFz_Scan53.b05_length,JFz_Scan53.b06_length,JFz_Scan53.b07_length,JFz_Scan53.b08_length,JFz_Scan53.b09_length,JFz_Scan53.b10_length,JFz_Scan53.b11_length,JFz_Scan53.b12_length,JFz_Scan53.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell10
theorem encoded10 : CandidateParserByteOrder.arrayBytes16 cell10=encodeQM31LE limbs10 := by
  funext i
  fin_cases i <;> rfl
theorem parser10 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell10)=
    ok (some ⟨⟨1944953019#u32,1642489912#u32⟩,⟨1651564245#u32,1487004490#u32⟩⟩) :=
  JFr_EncodedCell.parser cell10 limbs10 encoded10
#print axioms encoded10
#print axioms parser10
def cell11 : Array U8 16#usize := ⟨[79#u8,220#u8,66#u8,20#u8,53#u8,251#u8,114#u8,22#u8,186#u8,138#u8,4#u8,99#u8,160#u8,224#u8,216#u8,57#u8],by rfl⟩
def limbs11 : QM31Limbs := ![⟨339926095,by change 339926095<2147483647;omega⟩,⟨376634165,by change 376634165<2147483647;omega⟩,⟨1661242042,by change 1661242042<2147483647;omega⟩,⟨970514592,by change 970514592<2147483647;omega⟩]
theorem rawCell11 : (raw.drop 176).take 16=cell11.val := by
  simp only [raw,JFz_Scan53.data,JFz_Scan53.j00,JFz_Scan53.j01,JFz_Scan53.j02,JFz_Scan53.j03,JFz_Scan53.j04,JFz_Scan53.j05,JFz_Scan53.j06,JFz_Scan53.j07,JFz_Scan53.j08,JFz_Scan53.j09,JFz_Scan53.j10,JFz_Scan53.j11,JFz_Scan53.j12,JFz_Scan53.b00_length,JFz_Scan53.b01_length,JFz_Scan53.b02_length,JFz_Scan53.b03_length,JFz_Scan53.b04_length,JFz_Scan53.b05_length,JFz_Scan53.b06_length,JFz_Scan53.b07_length,JFz_Scan53.b08_length,JFz_Scan53.b09_length,JFz_Scan53.b10_length,JFz_Scan53.b11_length,JFz_Scan53.b12_length,JFz_Scan53.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell11
theorem encoded11 : CandidateParserByteOrder.arrayBytes16 cell11=encodeQM31LE limbs11 := by
  funext i
  fin_cases i <;> rfl
theorem parser11 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell11)=
    ok (some ⟨⟨339926095#u32,376634165#u32⟩,⟨1661242042#u32,970514592#u32⟩⟩) :=
  JFr_EncodedCell.parser cell11 limbs11 encoded11
#print axioms encoded11
#print axioms parser11
def cell12 : Array U8 16#usize := ⟨[216#u8,150#u8,136#u8,109#u8,171#u8,123#u8,82#u8,43#u8,100#u8,37#u8,239#u8,54#u8,131#u8,211#u8,154#u8,38#u8],by rfl⟩
def limbs12 : QM31Limbs := ![⟨1837668056,by change 1837668056<2147483647;omega⟩,⟨726825899,by change 726825899<2147483647;omega⟩,⟨921642340,by change 921642340<2147483647;omega⟩,⟨647680899,by change 647680899<2147483647;omega⟩]
theorem rawCell12 : (raw.drop 192).take 16=cell12.val := by
  simp only [raw,JFz_Scan53.data,JFz_Scan53.j00,JFz_Scan53.j01,JFz_Scan53.j02,JFz_Scan53.j03,JFz_Scan53.j04,JFz_Scan53.j05,JFz_Scan53.j06,JFz_Scan53.j07,JFz_Scan53.j08,JFz_Scan53.j09,JFz_Scan53.j10,JFz_Scan53.j11,JFz_Scan53.j12,JFz_Scan53.b00_length,JFz_Scan53.b01_length,JFz_Scan53.b02_length,JFz_Scan53.b03_length,JFz_Scan53.b04_length,JFz_Scan53.b05_length,JFz_Scan53.b06_length,JFz_Scan53.b07_length,JFz_Scan53.b08_length,JFz_Scan53.b09_length,JFz_Scan53.b10_length,JFz_Scan53.b11_length,JFz_Scan53.b12_length,JFz_Scan53.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell12
theorem encoded12 : CandidateParserByteOrder.arrayBytes16 cell12=encodeQM31LE limbs12 := by
  funext i
  fin_cases i <;> rfl
theorem parser12 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell12)=
    ok (some ⟨⟨1837668056#u32,726825899#u32⟩,⟨921642340#u32,647680899#u32⟩⟩) :=
  JFr_EncodedCell.parser cell12 limbs12 encoded12
#print axioms encoded12
#print axioms parser12
def cell13 : Array U8 16#usize := ⟨[92#u8,98#u8,128#u8,109#u8,159#u8,182#u8,192#u8,123#u8,66#u8,96#u8,135#u8,9#u8,244#u8,163#u8,27#u8,93#u8],by rfl⟩
def limbs13 : QM31Limbs := ![⟨1837130332,by change 1837130332<2147483647;omega⟩,⟨2076227231,by change 2076227231<2147483647;omega⟩,⟨159866946,by change 159866946<2147483647;omega⟩,⟨1562092532,by change 1562092532<2147483647;omega⟩]
theorem rawCell13 : (raw.drop 208).take 16=cell13.val := by
  simp only [raw,JFz_Scan53.data,JFz_Scan53.j00,JFz_Scan53.j01,JFz_Scan53.j02,JFz_Scan53.j03,JFz_Scan53.j04,JFz_Scan53.j05,JFz_Scan53.j06,JFz_Scan53.j07,JFz_Scan53.j08,JFz_Scan53.j09,JFz_Scan53.j10,JFz_Scan53.j11,JFz_Scan53.j12,JFz_Scan53.b00_length,JFz_Scan53.b01_length,JFz_Scan53.b02_length,JFz_Scan53.b03_length,JFz_Scan53.b04_length,JFz_Scan53.b05_length,JFz_Scan53.b06_length,JFz_Scan53.b07_length,JFz_Scan53.b08_length,JFz_Scan53.b09_length,JFz_Scan53.b10_length,JFz_Scan53.b11_length,JFz_Scan53.b12_length,JFz_Scan53.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell13
theorem encoded13 : CandidateParserByteOrder.arrayBytes16 cell13=encodeQM31LE limbs13 := by
  funext i
  fin_cases i <;> rfl
theorem parser13 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell13)=
    ok (some ⟨⟨1837130332#u32,2076227231#u32⟩,⟨159866946#u32,1562092532#u32⟩⟩) :=
  JFr_EncodedCell.parser cell13 limbs13 encoded13
#print axioms encoded13
#print axioms parser13
def cell14 : Array U8 16#usize := ⟨[100#u8,234#u8,159#u8,5#u8,119#u8,86#u8,148#u8,15#u8,4#u8,36#u8,181#u8,67#u8,151#u8,222#u8,167#u8,113#u8],by rfl⟩
def limbs14 : QM31Limbs := ![⟨94366308,by change 94366308<2147483647;omega⟩,⟨261379703,by change 261379703<2147483647;omega⟩,⟨1135944708,by change 1135944708<2147483647;omega⟩,⟨1906826903,by change 1906826903<2147483647;omega⟩]
theorem rawCell14 : (raw.drop 224).take 16=cell14.val := by
  simp only [raw,JFz_Scan53.data,JFz_Scan53.j00,JFz_Scan53.j01,JFz_Scan53.j02,JFz_Scan53.j03,JFz_Scan53.j04,JFz_Scan53.j05,JFz_Scan53.j06,JFz_Scan53.j07,JFz_Scan53.j08,JFz_Scan53.j09,JFz_Scan53.j10,JFz_Scan53.j11,JFz_Scan53.j12,JFz_Scan53.b00_length,JFz_Scan53.b01_length,JFz_Scan53.b02_length,JFz_Scan53.b03_length,JFz_Scan53.b04_length,JFz_Scan53.b05_length,JFz_Scan53.b06_length,JFz_Scan53.b07_length,JFz_Scan53.b08_length,JFz_Scan53.b09_length,JFz_Scan53.b10_length,JFz_Scan53.b11_length,JFz_Scan53.b12_length,JFz_Scan53.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell14
theorem encoded14 : CandidateParserByteOrder.arrayBytes16 cell14=encodeQM31LE limbs14 := by
  funext i
  fin_cases i <;> rfl
theorem parser14 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell14)=
    ok (some ⟨⟨94366308#u32,261379703#u32⟩,⟨1135944708#u32,1906826903#u32⟩⟩) :=
  JFr_EncodedCell.parser cell14 limbs14 encoded14
#print axioms encoded14
#print axioms parser14
def cell15 : Array U8 16#usize := ⟨[168#u8,73#u8,71#u8,72#u8,234#u8,226#u8,171#u8,59#u8,201#u8,87#u8,227#u8,72#u8,135#u8,42#u8,245#u8,0#u8],by rfl⟩
def limbs15 : QM31Limbs := ![⟨1212631464,by change 1212631464<2147483647;omega⟩,⟨1001120490,by change 1001120490<2147483647;omega⟩,⟨1222858697,by change 1222858697<2147483647;omega⟩,⟨16067207,by change 16067207<2147483647;omega⟩]
theorem rawCell15 : (raw.drop 240).take 16=cell15.val := by
  simp only [raw,JFz_Scan53.data,JFz_Scan53.j00,JFz_Scan53.j01,JFz_Scan53.j02,JFz_Scan53.j03,JFz_Scan53.j04,JFz_Scan53.j05,JFz_Scan53.j06,JFz_Scan53.j07,JFz_Scan53.j08,JFz_Scan53.j09,JFz_Scan53.j10,JFz_Scan53.j11,JFz_Scan53.j12,JFz_Scan53.b00_length,JFz_Scan53.b01_length,JFz_Scan53.b02_length,JFz_Scan53.b03_length,JFz_Scan53.b04_length,JFz_Scan53.b05_length,JFz_Scan53.b06_length,JFz_Scan53.b07_length,JFz_Scan53.b08_length,JFz_Scan53.b09_length,JFz_Scan53.b10_length,JFz_Scan53.b11_length,JFz_Scan53.b12_length,JFz_Scan53.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell15
theorem encoded15 : CandidateParserByteOrder.arrayBytes16 cell15=encodeQM31LE limbs15 := by
  funext i
  fin_cases i <;> rfl
theorem parser15 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell15)=
    ok (some ⟨⟨1212631464#u32,1001120490#u32⟩,⟨1222858697#u32,16067207#u32⟩⟩) :=
  JFr_EncodedCell.parser cell15 limbs15 encoded15
#print axioms encoded15
#print axioms parser15
def cell16 : Array U8 16#usize := ⟨[31#u8,54#u8,9#u8,82#u8,95#u8,15#u8,63#u8,4#u8,203#u8,205#u8,41#u8,127#u8,137#u8,250#u8,122#u8,66#u8],by rfl⟩
def limbs16 : QM31Limbs := ![⟨1376335391,by change 1376335391<2147483647;omega⟩,⟨71241567,by change 71241567<2147483647;omega⟩,⟨2133446091,by change 2133446091<2147483647;omega⟩,⟨1115355785,by change 1115355785<2147483647;omega⟩]
theorem rawCell16 : (raw.drop 256).take 16=cell16.val := by
  simp only [raw,JFz_Scan53.data,JFz_Scan53.j00,JFz_Scan53.j01,JFz_Scan53.j02,JFz_Scan53.j03,JFz_Scan53.j04,JFz_Scan53.j05,JFz_Scan53.j06,JFz_Scan53.j07,JFz_Scan53.j08,JFz_Scan53.j09,JFz_Scan53.j10,JFz_Scan53.j11,JFz_Scan53.j12,JFz_Scan53.b00_length,JFz_Scan53.b01_length,JFz_Scan53.b02_length,JFz_Scan53.b03_length,JFz_Scan53.b04_length,JFz_Scan53.b05_length,JFz_Scan53.b06_length,JFz_Scan53.b07_length,JFz_Scan53.b08_length,JFz_Scan53.b09_length,JFz_Scan53.b10_length,JFz_Scan53.b11_length,JFz_Scan53.b12_length,JFz_Scan53.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell16
theorem encoded16 : CandidateParserByteOrder.arrayBytes16 cell16=encodeQM31LE limbs16 := by
  funext i
  fin_cases i <;> rfl
theorem parser16 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell16)=
    ok (some ⟨⟨1376335391#u32,71241567#u32⟩,⟨2133446091#u32,1115355785#u32⟩⟩) :=
  JFr_EncodedCell.parser cell16 limbs16 encoded16
#print axioms encoded16
#print axioms parser16
def cell17 : Array U8 16#usize := ⟨[170#u8,134#u8,106#u8,41#u8,182#u8,35#u8,196#u8,40#u8,243#u8,127#u8,176#u8,105#u8,24#u8,50#u8,120#u8,17#u8],by rfl⟩
def limbs17 : QM31Limbs := ![⟨694847146,by change 694847146<2147483647;omega⟩,⟨683942838,by change 683942838<2147483647;omega⟩,⟨1773174771,by change 1773174771<2147483647;omega⟩,⟨293089816,by change 293089816<2147483647;omega⟩]
theorem rawCell17 : (raw.drop 272).take 16=cell17.val := by
  simp only [raw,JFz_Scan53.data,JFz_Scan53.j00,JFz_Scan53.j01,JFz_Scan53.j02,JFz_Scan53.j03,JFz_Scan53.j04,JFz_Scan53.j05,JFz_Scan53.j06,JFz_Scan53.j07,JFz_Scan53.j08,JFz_Scan53.j09,JFz_Scan53.j10,JFz_Scan53.j11,JFz_Scan53.j12,JFz_Scan53.b00_length,JFz_Scan53.b01_length,JFz_Scan53.b02_length,JFz_Scan53.b03_length,JFz_Scan53.b04_length,JFz_Scan53.b05_length,JFz_Scan53.b06_length,JFz_Scan53.b07_length,JFz_Scan53.b08_length,JFz_Scan53.b09_length,JFz_Scan53.b10_length,JFz_Scan53.b11_length,JFz_Scan53.b12_length,JFz_Scan53.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell17
theorem encoded17 : CandidateParserByteOrder.arrayBytes16 cell17=encodeQM31LE limbs17 := by
  funext i
  fin_cases i <;> rfl
theorem parser17 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell17)=
    ok (some ⟨⟨694847146#u32,683942838#u32⟩,⟨1773174771#u32,293089816#u32⟩⟩) :=
  JFr_EncodedCell.parser cell17 limbs17 encoded17
#print axioms encoded17
#print axioms parser17
def cell18 : Array U8 16#usize := ⟨[84#u8,181#u8,209#u8,54#u8,189#u8,83#u8,139#u8,49#u8,33#u8,70#u8,53#u8,67#u8,27#u8,110#u8,115#u8,36#u8],by rfl⟩
def limbs18 : QM31Limbs := ![⟨919713108,by change 919713108<2147483647;omega⟩,⟨831214525,by change 831214525<2147483647;omega⟩,⟨1127564833,by change 1127564833<2147483647;omega⟩,⟨611544603,by change 611544603<2147483647;omega⟩]
theorem rawCell18 : (raw.drop 288).take 16=cell18.val := by
  simp only [raw,JFz_Scan53.data,JFz_Scan53.j00,JFz_Scan53.j01,JFz_Scan53.j02,JFz_Scan53.j03,JFz_Scan53.j04,JFz_Scan53.j05,JFz_Scan53.j06,JFz_Scan53.j07,JFz_Scan53.j08,JFz_Scan53.j09,JFz_Scan53.j10,JFz_Scan53.j11,JFz_Scan53.j12,JFz_Scan53.b00_length,JFz_Scan53.b01_length,JFz_Scan53.b02_length,JFz_Scan53.b03_length,JFz_Scan53.b04_length,JFz_Scan53.b05_length,JFz_Scan53.b06_length,JFz_Scan53.b07_length,JFz_Scan53.b08_length,JFz_Scan53.b09_length,JFz_Scan53.b10_length,JFz_Scan53.b11_length,JFz_Scan53.b12_length,JFz_Scan53.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell18
theorem encoded18 : CandidateParserByteOrder.arrayBytes16 cell18=encodeQM31LE limbs18 := by
  funext i
  fin_cases i <;> rfl
theorem parser18 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell18)=
    ok (some ⟨⟨919713108#u32,831214525#u32⟩,⟨1127564833#u32,611544603#u32⟩⟩) :=
  JFr_EncodedCell.parser cell18 limbs18 encoded18
#print axioms encoded18
#print axioms parser18
def cell19 : Array U8 16#usize := ⟨[209#u8,231#u8,54#u8,77#u8,57#u8,200#u8,75#u8,27#u8,240#u8,64#u8,68#u8,32#u8,121#u8,66#u8,173#u8,121#u8],by rfl⟩
def limbs19 : QM31Limbs := ![⟨1295443921,by change 1295443921<2147483647;omega⟩,⟨457951289,by change 457951289<2147483647;omega⟩,⟨541343984,by change 541343984<2147483647;omega⟩,⟨2041397881,by change 2041397881<2147483647;omega⟩]
theorem rawCell19 : (raw.drop 304).take 16=cell19.val := by
  simp only [raw,JFz_Scan53.data,JFz_Scan53.j00,JFz_Scan53.j01,JFz_Scan53.j02,JFz_Scan53.j03,JFz_Scan53.j04,JFz_Scan53.j05,JFz_Scan53.j06,JFz_Scan53.j07,JFz_Scan53.j08,JFz_Scan53.j09,JFz_Scan53.j10,JFz_Scan53.j11,JFz_Scan53.j12,JFz_Scan53.b00_length,JFz_Scan53.b01_length,JFz_Scan53.b02_length,JFz_Scan53.b03_length,JFz_Scan53.b04_length,JFz_Scan53.b05_length,JFz_Scan53.b06_length,JFz_Scan53.b07_length,JFz_Scan53.b08_length,JFz_Scan53.b09_length,JFz_Scan53.b10_length,JFz_Scan53.b11_length,JFz_Scan53.b12_length,JFz_Scan53.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell19
theorem encoded19 : CandidateParserByteOrder.arrayBytes16 cell19=encodeQM31LE limbs19 := by
  funext i
  fin_cases i <;> rfl
theorem parser19 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell19)=
    ok (some ⟨⟨1295443921#u32,457951289#u32⟩,⟨541343984#u32,2041397881#u32⟩⟩) :=
  JFr_EncodedCell.parser cell19 limbs19 encoded19
#print axioms encoded19
#print axioms parser19
def cell20 : Array U8 16#usize := ⟨[192#u8,141#u8,82#u8,84#u8,98#u8,178#u8,37#u8,29#u8,242#u8,123#u8,69#u8,120#u8,9#u8,235#u8,95#u8,3#u8],by rfl⟩
def limbs20 : QM31Limbs := ![⟨1414696384,by change 1414696384<2147483647;omega⟩,⟨489009762,by change 489009762<2147483647;omega⟩,⟨2017819634,by change 2017819634<2147483647;omega⟩,⟨56617737,by change 56617737<2147483647;omega⟩]
theorem rawCell20 : (raw.drop 320).take 16=cell20.val := by
  simp only [raw,JFz_Scan53.data,JFz_Scan53.j00,JFz_Scan53.j01,JFz_Scan53.j02,JFz_Scan53.j03,JFz_Scan53.j04,JFz_Scan53.j05,JFz_Scan53.j06,JFz_Scan53.j07,JFz_Scan53.j08,JFz_Scan53.j09,JFz_Scan53.j10,JFz_Scan53.j11,JFz_Scan53.j12,JFz_Scan53.b00_length,JFz_Scan53.b01_length,JFz_Scan53.b02_length,JFz_Scan53.b03_length,JFz_Scan53.b04_length,JFz_Scan53.b05_length,JFz_Scan53.b06_length,JFz_Scan53.b07_length,JFz_Scan53.b08_length,JFz_Scan53.b09_length,JFz_Scan53.b10_length,JFz_Scan53.b11_length,JFz_Scan53.b12_length,JFz_Scan53.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell20
theorem encoded20 : CandidateParserByteOrder.arrayBytes16 cell20=encodeQM31LE limbs20 := by
  funext i
  fin_cases i <;> rfl
theorem parser20 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell20)=
    ok (some ⟨⟨1414696384#u32,489009762#u32⟩,⟨2017819634#u32,56617737#u32⟩⟩) :=
  JFr_EncodedCell.parser cell20 limbs20 encoded20
#print axioms encoded20
#print axioms parser20
def cell21 : Array U8 16#usize := ⟨[136#u8,54#u8,86#u8,28#u8,180#u8,40#u8,206#u8,10#u8,214#u8,12#u8,126#u8,1#u8,167#u8,10#u8,115#u8,70#u8],by rfl⟩
def limbs21 : QM31Limbs := ![⟨475412104,by change 475412104<2147483647;omega⟩,⟨181282996,by change 181282996<2147483647;omega⟩,⟨25038038,by change 25038038<2147483647;omega⟩,⟨1181944487,by change 1181944487<2147483647;omega⟩]
theorem rawCell21 : (raw.drop 336).take 16=cell21.val := by
  simp only [raw,JFz_Scan53.data,JFz_Scan53.j00,JFz_Scan53.j01,JFz_Scan53.j02,JFz_Scan53.j03,JFz_Scan53.j04,JFz_Scan53.j05,JFz_Scan53.j06,JFz_Scan53.j07,JFz_Scan53.j08,JFz_Scan53.j09,JFz_Scan53.j10,JFz_Scan53.j11,JFz_Scan53.j12,JFz_Scan53.b00_length,JFz_Scan53.b01_length,JFz_Scan53.b02_length,JFz_Scan53.b03_length,JFz_Scan53.b04_length,JFz_Scan53.b05_length,JFz_Scan53.b06_length,JFz_Scan53.b07_length,JFz_Scan53.b08_length,JFz_Scan53.b09_length,JFz_Scan53.b10_length,JFz_Scan53.b11_length,JFz_Scan53.b12_length,JFz_Scan53.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell21
theorem encoded21 : CandidateParserByteOrder.arrayBytes16 cell21=encodeQM31LE limbs21 := by
  funext i
  fin_cases i <;> rfl
theorem parser21 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell21)=
    ok (some ⟨⟨475412104#u32,181282996#u32⟩,⟨25038038#u32,1181944487#u32⟩⟩) :=
  JFr_EncodedCell.parser cell21 limbs21 encoded21
#print axioms encoded21
#print axioms parser21
def cell22 : Array U8 16#usize := ⟨[118#u8,160#u8,114#u8,61#u8,68#u8,253#u8,13#u8,28#u8,230#u8,124#u8,97#u8,49#u8,134#u8,113#u8,133#u8,68#u8],by rfl⟩
def limbs22 : QM31Limbs := ![⟨1030922358,by change 1030922358<2147483647;omega⟩,⟨470678852,by change 470678852<2147483647;omega⟩,⟨828472550,by change 828472550<2147483647;omega⟩,⟨1149596038,by change 1149596038<2147483647;omega⟩]
theorem rawCell22 : (raw.drop 352).take 16=cell22.val := by
  simp only [raw,JFz_Scan53.data,JFz_Scan53.j00,JFz_Scan53.j01,JFz_Scan53.j02,JFz_Scan53.j03,JFz_Scan53.j04,JFz_Scan53.j05,JFz_Scan53.j06,JFz_Scan53.j07,JFz_Scan53.j08,JFz_Scan53.j09,JFz_Scan53.j10,JFz_Scan53.j11,JFz_Scan53.j12,JFz_Scan53.b00_length,JFz_Scan53.b01_length,JFz_Scan53.b02_length,JFz_Scan53.b03_length,JFz_Scan53.b04_length,JFz_Scan53.b05_length,JFz_Scan53.b06_length,JFz_Scan53.b07_length,JFz_Scan53.b08_length,JFz_Scan53.b09_length,JFz_Scan53.b10_length,JFz_Scan53.b11_length,JFz_Scan53.b12_length,JFz_Scan53.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell22
theorem encoded22 : CandidateParserByteOrder.arrayBytes16 cell22=encodeQM31LE limbs22 := by
  funext i
  fin_cases i <;> rfl
theorem parser22 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell22)=
    ok (some ⟨⟨1030922358#u32,470678852#u32⟩,⟨828472550#u32,1149596038#u32⟩⟩) :=
  JFr_EncodedCell.parser cell22 limbs22 encoded22
#print axioms encoded22
#print axioms parser22
def cell23 : Array U8 16#usize := ⟨[181#u8,42#u8,229#u8,91#u8,200#u8,186#u8,187#u8,105#u8,187#u8,79#u8,232#u8,58#u8,133#u8,109#u8,1#u8,48#u8],by rfl⟩
def limbs23 : QM31Limbs := ![⟨1541745333,by change 1541745333<2147483647;omega⟩,⟨1773910728,by change 1773910728<2147483647;omega⟩,⟨988303291,by change 988303291<2147483647;omega⟩,⟨805399941,by change 805399941<2147483647;omega⟩]
theorem rawCell23 : (raw.drop 368).take 16=cell23.val := by
  simp only [raw,JFz_Scan53.data,JFz_Scan53.j00,JFz_Scan53.j01,JFz_Scan53.j02,JFz_Scan53.j03,JFz_Scan53.j04,JFz_Scan53.j05,JFz_Scan53.j06,JFz_Scan53.j07,JFz_Scan53.j08,JFz_Scan53.j09,JFz_Scan53.j10,JFz_Scan53.j11,JFz_Scan53.j12,JFz_Scan53.b00_length,JFz_Scan53.b01_length,JFz_Scan53.b02_length,JFz_Scan53.b03_length,JFz_Scan53.b04_length,JFz_Scan53.b05_length,JFz_Scan53.b06_length,JFz_Scan53.b07_length,JFz_Scan53.b08_length,JFz_Scan53.b09_length,JFz_Scan53.b10_length,JFz_Scan53.b11_length,JFz_Scan53.b12_length,JFz_Scan53.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell23
theorem encoded23 : CandidateParserByteOrder.arrayBytes16 cell23=encodeQM31LE limbs23 := by
  funext i
  fin_cases i <;> rfl
theorem parser23 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell23)=
    ok (some ⟨⟨1541745333#u32,1773910728#u32⟩,⟨988303291#u32,805399941#u32⟩⟩) :=
  JFr_EncodedCell.parser cell23 limbs23 encoded23
#print axioms encoded23
#print axioms parser23
def cell24 : Array U8 16#usize := ⟨[157#u8,51#u8,139#u8,42#u8,43#u8,94#u8,150#u8,55#u8,30#u8,147#u8,236#u8,28#u8,154#u8,136#u8,167#u8,98#u8],by rfl⟩
def limbs24 : QM31Limbs := ![⟨713765789,by change 713765789<2147483647;omega⟩,⟨932601387,by change 932601387<2147483647;omega⟩,⟨485266206,by change 485266206<2147483647;omega⟩,⟨1655146650,by change 1655146650<2147483647;omega⟩]
theorem rawCell24 : (raw.drop 384).take 16=cell24.val := by
  simp only [raw,JFz_Scan53.data,JFz_Scan53.j00,JFz_Scan53.j01,JFz_Scan53.j02,JFz_Scan53.j03,JFz_Scan53.j04,JFz_Scan53.j05,JFz_Scan53.j06,JFz_Scan53.j07,JFz_Scan53.j08,JFz_Scan53.j09,JFz_Scan53.j10,JFz_Scan53.j11,JFz_Scan53.j12,JFz_Scan53.b00_length,JFz_Scan53.b01_length,JFz_Scan53.b02_length,JFz_Scan53.b03_length,JFz_Scan53.b04_length,JFz_Scan53.b05_length,JFz_Scan53.b06_length,JFz_Scan53.b07_length,JFz_Scan53.b08_length,JFz_Scan53.b09_length,JFz_Scan53.b10_length,JFz_Scan53.b11_length,JFz_Scan53.b12_length,JFz_Scan53.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell24
theorem encoded24 : CandidateParserByteOrder.arrayBytes16 cell24=encodeQM31LE limbs24 := by
  funext i
  fin_cases i <;> rfl
theorem parser24 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell24)=
    ok (some ⟨⟨713765789#u32,932601387#u32⟩,⟨485266206#u32,1655146650#u32⟩⟩) :=
  JFr_EncodedCell.parser cell24 limbs24 encoded24
#print axioms encoded24
#print axioms parser24
def cell25 : Array U8 16#usize := ⟨[44#u8,22#u8,8#u8,113#u8,54#u8,75#u8,159#u8,120#u8,175#u8,99#u8,10#u8,99#u8,145#u8,221#u8,161#u8,14#u8],by rfl⟩
def limbs25 : QM31Limbs := ![⟨1896355372,by change 1896355372<2147483647;omega⟩,⟨2023705398,by change 2023705398<2147483647;omega⟩,⟨1661625263,by change 1661625263<2147483647;omega⟩,⟨245489041,by change 245489041<2147483647;omega⟩]
theorem rawCell25 : (raw.drop 400).take 16=cell25.val := by
  simp only [raw,JFz_Scan53.data,JFz_Scan53.j00,JFz_Scan53.j01,JFz_Scan53.j02,JFz_Scan53.j03,JFz_Scan53.j04,JFz_Scan53.j05,JFz_Scan53.j06,JFz_Scan53.j07,JFz_Scan53.j08,JFz_Scan53.j09,JFz_Scan53.j10,JFz_Scan53.j11,JFz_Scan53.j12,JFz_Scan53.b00_length,JFz_Scan53.b01_length,JFz_Scan53.b02_length,JFz_Scan53.b03_length,JFz_Scan53.b04_length,JFz_Scan53.b05_length,JFz_Scan53.b06_length,JFz_Scan53.b07_length,JFz_Scan53.b08_length,JFz_Scan53.b09_length,JFz_Scan53.b10_length,JFz_Scan53.b11_length,JFz_Scan53.b12_length,JFz_Scan53.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell25
theorem encoded25 : CandidateParserByteOrder.arrayBytes16 cell25=encodeQM31LE limbs25 := by
  funext i
  fin_cases i <;> rfl
theorem parser25 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell25)=
    ok (some ⟨⟨1896355372#u32,2023705398#u32⟩,⟨1661625263#u32,245489041#u32⟩⟩) :=
  JFr_EncodedCell.parser cell25 limbs25 encoded25
#print axioms encoded25
#print axioms parser25
def cell26 : Array U8 16#usize := ⟨[60#u8,47#u8,64#u8,40#u8,69#u8,44#u8,56#u8,96#u8,118#u8,147#u8,89#u8,15#u8,212#u8,247#u8,196#u8,52#u8],by rfl⟩
def limbs26 : QM31Limbs := ![⟨675295036,by change 675295036<2147483647;omega⟩,⟨1614294085,by change 1614294085<2147483647;omega⟩,⟨257528694,by change 257528694<2147483647;omega⟩,⟨885323732,by change 885323732<2147483647;omega⟩]
theorem rawCell26 : (raw.drop 416).take 16=cell26.val := by
  simp only [raw,JFz_Scan53.data,JFz_Scan53.j00,JFz_Scan53.j01,JFz_Scan53.j02,JFz_Scan53.j03,JFz_Scan53.j04,JFz_Scan53.j05,JFz_Scan53.j06,JFz_Scan53.j07,JFz_Scan53.j08,JFz_Scan53.j09,JFz_Scan53.j10,JFz_Scan53.j11,JFz_Scan53.j12,JFz_Scan53.b00_length,JFz_Scan53.b01_length,JFz_Scan53.b02_length,JFz_Scan53.b03_length,JFz_Scan53.b04_length,JFz_Scan53.b05_length,JFz_Scan53.b06_length,JFz_Scan53.b07_length,JFz_Scan53.b08_length,JFz_Scan53.b09_length,JFz_Scan53.b10_length,JFz_Scan53.b11_length,JFz_Scan53.b12_length,JFz_Scan53.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell26
theorem encoded26 : CandidateParserByteOrder.arrayBytes16 cell26=encodeQM31LE limbs26 := by
  funext i
  fin_cases i <;> rfl
theorem parser26 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell26)=
    ok (some ⟨⟨675295036#u32,1614294085#u32⟩,⟨257528694#u32,885323732#u32⟩⟩) :=
  JFr_EncodedCell.parser cell26 limbs26 encoded26
#print axioms encoded26
#print axioms parser26
def cell27 : Array U8 16#usize := ⟨[99#u8,170#u8,179#u8,32#u8,72#u8,216#u8,75#u8,117#u8,50#u8,50#u8,79#u8,23#u8,235#u8,3#u8,169#u8,123#u8],by rfl⟩
def limbs27 : QM31Limbs := ![⟨548645475,by change 548645475<2147483647;omega⟩,⟨1967904840,by change 1967904840<2147483647;omega⟩,⟨391066162,by change 391066162<2147483647;omega⟩,⟨2074674155,by change 2074674155<2147483647;omega⟩]
theorem rawCell27 : (raw.drop 432).take 16=cell27.val := by
  simp only [raw,JFz_Scan53.data,JFz_Scan53.j00,JFz_Scan53.j01,JFz_Scan53.j02,JFz_Scan53.j03,JFz_Scan53.j04,JFz_Scan53.j05,JFz_Scan53.j06,JFz_Scan53.j07,JFz_Scan53.j08,JFz_Scan53.j09,JFz_Scan53.j10,JFz_Scan53.j11,JFz_Scan53.j12,JFz_Scan53.b00_length,JFz_Scan53.b01_length,JFz_Scan53.b02_length,JFz_Scan53.b03_length,JFz_Scan53.b04_length,JFz_Scan53.b05_length,JFz_Scan53.b06_length,JFz_Scan53.b07_length,JFz_Scan53.b08_length,JFz_Scan53.b09_length,JFz_Scan53.b10_length,JFz_Scan53.b11_length,JFz_Scan53.b12_length,JFz_Scan53.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell27
theorem encoded27 : CandidateParserByteOrder.arrayBytes16 cell27=encodeQM31LE limbs27 := by
  funext i
  fin_cases i <;> rfl
theorem parser27 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell27)=
    ok (some ⟨⟨548645475#u32,1967904840#u32⟩,⟨391066162#u32,2074674155#u32⟩⟩) :=
  JFr_EncodedCell.parser cell27 limbs27 encoded27
#print axioms encoded27
#print axioms parser27
end AspisR1.JFr_Bytes05
