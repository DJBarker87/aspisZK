import NDO_JFr_Data06
import NDO_JFr_EncodedCell
import NDO_JFz_Scan54
set_option autoImplicit false
namespace AspisR1.JFr_Bytes06
open Aeneas Aeneas.Std Result RetainedFieldByteCodec
open AspisR1PublicPreparation
open AspisS1ExtractedRoundChildren
def raw : List U8 := JFz_Scan54.data
theorem rawLength : raw.length=448 := JFz_Scan54.length
#print axioms rawLength
theorem selected : (JFx_NativeBytes.proof.val.drop 2894).take 448=raw := JFz_Scan54.selected
#print axioms selected
def cell00 : Array U8 16#usize := ⟨[167#u8,10#u8,165#u8,99#u8,159#u8,127#u8,7#u8,32#u8,171#u8,73#u8,176#u8,21#u8,119#u8,7#u8,210#u8,76#u8],by rfl⟩
def limbs00 : QM31Limbs := ![⟨1671760551,by change 1671760551<2147483647;omega⟩,⟨537362335,by change 537362335<2147483647;omega⟩,⟨363874731,by change 363874731<2147483647;omega⟩,⟨1288832887,by change 1288832887<2147483647;omega⟩]
theorem rawCell00 : (raw.drop 0).take 16=cell00.val := by
  simp only [raw,JFz_Scan54.data,JFz_Scan54.j00,JFz_Scan54.j01,JFz_Scan54.j02,JFz_Scan54.j03,JFz_Scan54.j04,JFz_Scan54.j05,JFz_Scan54.j06,JFz_Scan54.j07,JFz_Scan54.j08,JFz_Scan54.j09,JFz_Scan54.j10,JFz_Scan54.j11,JFz_Scan54.j12,JFz_Scan54.b00_length,JFz_Scan54.b01_length,JFz_Scan54.b02_length,JFz_Scan54.b03_length,JFz_Scan54.b04_length,JFz_Scan54.b05_length,JFz_Scan54.b06_length,JFz_Scan54.b07_length,JFz_Scan54.b08_length,JFz_Scan54.b09_length,JFz_Scan54.b10_length,JFz_Scan54.b11_length,JFz_Scan54.b12_length,JFz_Scan54.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell00
theorem encoded00 : CandidateParserByteOrder.arrayBytes16 cell00=encodeQM31LE limbs00 := by
  funext i
  fin_cases i <;> rfl
theorem parser00 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell00)=
    ok (some ⟨⟨1671760551#u32,537362335#u32⟩,⟨363874731#u32,1288832887#u32⟩⟩) :=
  JFr_EncodedCell.parser cell00 limbs00 encoded00
#print axioms encoded00
#print axioms parser00
def cell01 : Array U8 16#usize := ⟨[239#u8,22#u8,213#u8,17#u8,163#u8,229#u8,89#u8,81#u8,168#u8,57#u8,203#u8,126#u8,226#u8,164#u8,148#u8,41#u8],by rfl⟩
def limbs01 : QM31Limbs := ![⟨299177711,by change 299177711<2147483647;omega⟩,⟨1364845987,by change 1364845987<2147483647;omega⟩,⟨2127247784,by change 2127247784<2147483647;omega⟩,⟨697607394,by change 697607394<2147483647;omega⟩]
theorem rawCell01 : (raw.drop 16).take 16=cell01.val := by
  simp only [raw,JFz_Scan54.data,JFz_Scan54.j00,JFz_Scan54.j01,JFz_Scan54.j02,JFz_Scan54.j03,JFz_Scan54.j04,JFz_Scan54.j05,JFz_Scan54.j06,JFz_Scan54.j07,JFz_Scan54.j08,JFz_Scan54.j09,JFz_Scan54.j10,JFz_Scan54.j11,JFz_Scan54.j12,JFz_Scan54.b00_length,JFz_Scan54.b01_length,JFz_Scan54.b02_length,JFz_Scan54.b03_length,JFz_Scan54.b04_length,JFz_Scan54.b05_length,JFz_Scan54.b06_length,JFz_Scan54.b07_length,JFz_Scan54.b08_length,JFz_Scan54.b09_length,JFz_Scan54.b10_length,JFz_Scan54.b11_length,JFz_Scan54.b12_length,JFz_Scan54.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell01
theorem encoded01 : CandidateParserByteOrder.arrayBytes16 cell01=encodeQM31LE limbs01 := by
  funext i
  fin_cases i <;> rfl
theorem parser01 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell01)=
    ok (some ⟨⟨299177711#u32,1364845987#u32⟩,⟨2127247784#u32,697607394#u32⟩⟩) :=
  JFr_EncodedCell.parser cell01 limbs01 encoded01
#print axioms encoded01
#print axioms parser01
def cell02 : Array U8 16#usize := ⟨[52#u8,150#u8,66#u8,96#u8,32#u8,15#u8,166#u8,13#u8,67#u8,194#u8,145#u8,81#u8,68#u8,120#u8,212#u8,127#u8],by rfl⟩
def limbs02 : QM31Limbs := ![⟨1614976564,by change 1614976564<2147483647;omega⟩,⟨228986656,by change 228986656<2147483647;omega⟩,⟨1368506947,by change 1368506947<2147483647;omega⟩,⟨2144630852,by change 2144630852<2147483647;omega⟩]
theorem rawCell02 : (raw.drop 32).take 16=cell02.val := by
  simp only [raw,JFz_Scan54.data,JFz_Scan54.j00,JFz_Scan54.j01,JFz_Scan54.j02,JFz_Scan54.j03,JFz_Scan54.j04,JFz_Scan54.j05,JFz_Scan54.j06,JFz_Scan54.j07,JFz_Scan54.j08,JFz_Scan54.j09,JFz_Scan54.j10,JFz_Scan54.j11,JFz_Scan54.j12,JFz_Scan54.b00_length,JFz_Scan54.b01_length,JFz_Scan54.b02_length,JFz_Scan54.b03_length,JFz_Scan54.b04_length,JFz_Scan54.b05_length,JFz_Scan54.b06_length,JFz_Scan54.b07_length,JFz_Scan54.b08_length,JFz_Scan54.b09_length,JFz_Scan54.b10_length,JFz_Scan54.b11_length,JFz_Scan54.b12_length,JFz_Scan54.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell02
theorem encoded02 : CandidateParserByteOrder.arrayBytes16 cell02=encodeQM31LE limbs02 := by
  funext i
  fin_cases i <;> rfl
theorem parser02 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell02)=
    ok (some ⟨⟨1614976564#u32,228986656#u32⟩,⟨1368506947#u32,2144630852#u32⟩⟩) :=
  JFr_EncodedCell.parser cell02 limbs02 encoded02
#print axioms encoded02
#print axioms parser02
def cell03 : Array U8 16#usize := ⟨[98#u8,20#u8,129#u8,6#u8,254#u8,241#u8,210#u8,95#u8,228#u8,206#u8,218#u8,82#u8,249#u8,45#u8,164#u8,49#u8],by rfl⟩
def limbs03 : QM31Limbs := ![⟨109122658,by change 109122658<2147483647;omega⟩,⟨1607660030,by change 1607660030<2147483647;omega⟩,⟨1390071524,by change 1390071524<2147483647;omega⟩,⟨832843257,by change 832843257<2147483647;omega⟩]
theorem rawCell03 : (raw.drop 48).take 16=cell03.val := by
  simp only [raw,JFz_Scan54.data,JFz_Scan54.j00,JFz_Scan54.j01,JFz_Scan54.j02,JFz_Scan54.j03,JFz_Scan54.j04,JFz_Scan54.j05,JFz_Scan54.j06,JFz_Scan54.j07,JFz_Scan54.j08,JFz_Scan54.j09,JFz_Scan54.j10,JFz_Scan54.j11,JFz_Scan54.j12,JFz_Scan54.b00_length,JFz_Scan54.b01_length,JFz_Scan54.b02_length,JFz_Scan54.b03_length,JFz_Scan54.b04_length,JFz_Scan54.b05_length,JFz_Scan54.b06_length,JFz_Scan54.b07_length,JFz_Scan54.b08_length,JFz_Scan54.b09_length,JFz_Scan54.b10_length,JFz_Scan54.b11_length,JFz_Scan54.b12_length,JFz_Scan54.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell03
theorem encoded03 : CandidateParserByteOrder.arrayBytes16 cell03=encodeQM31LE limbs03 := by
  funext i
  fin_cases i <;> rfl
theorem parser03 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell03)=
    ok (some ⟨⟨109122658#u32,1607660030#u32⟩,⟨1390071524#u32,832843257#u32⟩⟩) :=
  JFr_EncodedCell.parser cell03 limbs03 encoded03
#print axioms encoded03
#print axioms parser03
def cell04 : Array U8 16#usize := ⟨[123#u8,8#u8,57#u8,101#u8,22#u8,220#u8,167#u8,57#u8,41#u8,103#u8,240#u8,93#u8,250#u8,247#u8,184#u8,115#u8],by rfl⟩
def limbs04 : QM31Limbs := ![⟨1698236539,by change 1698236539<2147483647;omega⟩,⟨967302166,by change 967302166<2147483647;omega⟩,⟨1576036137,by change 1576036137<2147483647;omega⟩,⟨1941501946,by change 1941501946<2147483647;omega⟩]
theorem rawCell04 : (raw.drop 64).take 16=cell04.val := by
  simp only [raw,JFz_Scan54.data,JFz_Scan54.j00,JFz_Scan54.j01,JFz_Scan54.j02,JFz_Scan54.j03,JFz_Scan54.j04,JFz_Scan54.j05,JFz_Scan54.j06,JFz_Scan54.j07,JFz_Scan54.j08,JFz_Scan54.j09,JFz_Scan54.j10,JFz_Scan54.j11,JFz_Scan54.j12,JFz_Scan54.b00_length,JFz_Scan54.b01_length,JFz_Scan54.b02_length,JFz_Scan54.b03_length,JFz_Scan54.b04_length,JFz_Scan54.b05_length,JFz_Scan54.b06_length,JFz_Scan54.b07_length,JFz_Scan54.b08_length,JFz_Scan54.b09_length,JFz_Scan54.b10_length,JFz_Scan54.b11_length,JFz_Scan54.b12_length,JFz_Scan54.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell04
theorem encoded04 : CandidateParserByteOrder.arrayBytes16 cell04=encodeQM31LE limbs04 := by
  funext i
  fin_cases i <;> rfl
theorem parser04 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell04)=
    ok (some ⟨⟨1698236539#u32,967302166#u32⟩,⟨1576036137#u32,1941501946#u32⟩⟩) :=
  JFr_EncodedCell.parser cell04 limbs04 encoded04
#print axioms encoded04
#print axioms parser04
def cell05 : Array U8 16#usize := ⟨[190#u8,54#u8,131#u8,19#u8,172#u8,190#u8,86#u8,60#u8,86#u8,70#u8,37#u8,99#u8,142#u8,124#u8,18#u8,39#u8],by rfl⟩
def limbs05 : QM31Limbs := ![⟨327366334,by change 327366334<2147483647;omega⟩,⟨1012317868,by change 1012317868<2147483647;omega⟩,⟨1663387222,by change 1663387222<2147483647;omega⟩,⟨655522958,by change 655522958<2147483647;omega⟩]
theorem rawCell05 : (raw.drop 80).take 16=cell05.val := by
  simp only [raw,JFz_Scan54.data,JFz_Scan54.j00,JFz_Scan54.j01,JFz_Scan54.j02,JFz_Scan54.j03,JFz_Scan54.j04,JFz_Scan54.j05,JFz_Scan54.j06,JFz_Scan54.j07,JFz_Scan54.j08,JFz_Scan54.j09,JFz_Scan54.j10,JFz_Scan54.j11,JFz_Scan54.j12,JFz_Scan54.b00_length,JFz_Scan54.b01_length,JFz_Scan54.b02_length,JFz_Scan54.b03_length,JFz_Scan54.b04_length,JFz_Scan54.b05_length,JFz_Scan54.b06_length,JFz_Scan54.b07_length,JFz_Scan54.b08_length,JFz_Scan54.b09_length,JFz_Scan54.b10_length,JFz_Scan54.b11_length,JFz_Scan54.b12_length,JFz_Scan54.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell05
theorem encoded05 : CandidateParserByteOrder.arrayBytes16 cell05=encodeQM31LE limbs05 := by
  funext i
  fin_cases i <;> rfl
theorem parser05 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell05)=
    ok (some ⟨⟨327366334#u32,1012317868#u32⟩,⟨1663387222#u32,655522958#u32⟩⟩) :=
  JFr_EncodedCell.parser cell05 limbs05 encoded05
#print axioms encoded05
#print axioms parser05
def cell06 : Array U8 16#usize := ⟨[14#u8,96#u8,18#u8,70#u8,190#u8,6#u8,171#u8,118#u8,79#u8,253#u8,250#u8,78#u8,227#u8,138#u8,101#u8,9#u8],by rfl⟩
def limbs06 : QM31Limbs := ![⟨1175609358,by change 1175609358<2147483647;omega⟩,⟨1990919870,by change 1990919870<2147483647;omega⟩,⟨1325071695,by change 1325071695<2147483647;omega⟩,⟨157649635,by change 157649635<2147483647;omega⟩]
theorem rawCell06 : (raw.drop 96).take 16=cell06.val := by
  simp only [raw,JFz_Scan54.data,JFz_Scan54.j00,JFz_Scan54.j01,JFz_Scan54.j02,JFz_Scan54.j03,JFz_Scan54.j04,JFz_Scan54.j05,JFz_Scan54.j06,JFz_Scan54.j07,JFz_Scan54.j08,JFz_Scan54.j09,JFz_Scan54.j10,JFz_Scan54.j11,JFz_Scan54.j12,JFz_Scan54.b00_length,JFz_Scan54.b01_length,JFz_Scan54.b02_length,JFz_Scan54.b03_length,JFz_Scan54.b04_length,JFz_Scan54.b05_length,JFz_Scan54.b06_length,JFz_Scan54.b07_length,JFz_Scan54.b08_length,JFz_Scan54.b09_length,JFz_Scan54.b10_length,JFz_Scan54.b11_length,JFz_Scan54.b12_length,JFz_Scan54.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell06
theorem encoded06 : CandidateParserByteOrder.arrayBytes16 cell06=encodeQM31LE limbs06 := by
  funext i
  fin_cases i <;> rfl
theorem parser06 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell06)=
    ok (some ⟨⟨1175609358#u32,1990919870#u32⟩,⟨1325071695#u32,157649635#u32⟩⟩) :=
  JFr_EncodedCell.parser cell06 limbs06 encoded06
#print axioms encoded06
#print axioms parser06
def cell07 : Array U8 16#usize := ⟨[253#u8,42#u8,39#u8,46#u8,22#u8,141#u8,166#u8,71#u8,204#u8,251#u8,245#u8,90#u8,32#u8,26#u8,58#u8,96#u8],by rfl⟩
def limbs07 : QM31Limbs := ![⟨774318845,by change 774318845<2147483647;omega⟩,⟨1202097430,by change 1202097430<2147483647;omega⟩,⟨1526070220,by change 1526070220<2147483647;omega⟩,⟨1614420512,by change 1614420512<2147483647;omega⟩]
theorem rawCell07 : (raw.drop 112).take 16=cell07.val := by
  simp only [raw,JFz_Scan54.data,JFz_Scan54.j00,JFz_Scan54.j01,JFz_Scan54.j02,JFz_Scan54.j03,JFz_Scan54.j04,JFz_Scan54.j05,JFz_Scan54.j06,JFz_Scan54.j07,JFz_Scan54.j08,JFz_Scan54.j09,JFz_Scan54.j10,JFz_Scan54.j11,JFz_Scan54.j12,JFz_Scan54.b00_length,JFz_Scan54.b01_length,JFz_Scan54.b02_length,JFz_Scan54.b03_length,JFz_Scan54.b04_length,JFz_Scan54.b05_length,JFz_Scan54.b06_length,JFz_Scan54.b07_length,JFz_Scan54.b08_length,JFz_Scan54.b09_length,JFz_Scan54.b10_length,JFz_Scan54.b11_length,JFz_Scan54.b12_length,JFz_Scan54.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell07
theorem encoded07 : CandidateParserByteOrder.arrayBytes16 cell07=encodeQM31LE limbs07 := by
  funext i
  fin_cases i <;> rfl
theorem parser07 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell07)=
    ok (some ⟨⟨774318845#u32,1202097430#u32⟩,⟨1526070220#u32,1614420512#u32⟩⟩) :=
  JFr_EncodedCell.parser cell07 limbs07 encoded07
#print axioms encoded07
#print axioms parser07
def cell08 : Array U8 16#usize := ⟨[3#u8,188#u8,72#u8,63#u8,187#u8,216#u8,60#u8,54#u8,249#u8,97#u8,79#u8,88#u8,2#u8,53#u8,255#u8,52#u8],by rfl⟩
def limbs08 : QM31Limbs := ![⟨1061731331,by change 1061731331<2147483647;omega⟩,⟨909957307,by change 909957307<2147483647;omega⟩,⟨1481597433,by change 1481597433<2147483647;omega⟩,⟨889140482,by change 889140482<2147483647;omega⟩]
theorem rawCell08 : (raw.drop 128).take 16=cell08.val := by
  simp only [raw,JFz_Scan54.data,JFz_Scan54.j00,JFz_Scan54.j01,JFz_Scan54.j02,JFz_Scan54.j03,JFz_Scan54.j04,JFz_Scan54.j05,JFz_Scan54.j06,JFz_Scan54.j07,JFz_Scan54.j08,JFz_Scan54.j09,JFz_Scan54.j10,JFz_Scan54.j11,JFz_Scan54.j12,JFz_Scan54.b00_length,JFz_Scan54.b01_length,JFz_Scan54.b02_length,JFz_Scan54.b03_length,JFz_Scan54.b04_length,JFz_Scan54.b05_length,JFz_Scan54.b06_length,JFz_Scan54.b07_length,JFz_Scan54.b08_length,JFz_Scan54.b09_length,JFz_Scan54.b10_length,JFz_Scan54.b11_length,JFz_Scan54.b12_length,JFz_Scan54.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell08
theorem encoded08 : CandidateParserByteOrder.arrayBytes16 cell08=encodeQM31LE limbs08 := by
  funext i
  fin_cases i <;> rfl
theorem parser08 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell08)=
    ok (some ⟨⟨1061731331#u32,909957307#u32⟩,⟨1481597433#u32,889140482#u32⟩⟩) :=
  JFr_EncodedCell.parser cell08 limbs08 encoded08
#print axioms encoded08
#print axioms parser08
def cell09 : Array U8 16#usize := ⟨[166#u8,74#u8,82#u8,91#u8,241#u8,203#u8,85#u8,10#u8,34#u8,222#u8,167#u8,59#u8,0#u8,168#u8,204#u8,53#u8],by rfl⟩
def limbs09 : QM31Limbs := ![⟨1532119718,by change 1532119718<2147483647;omega⟩,⟨173394929,by change 173394929<2147483647;omega⟩,⟨1000857122,by change 1000857122<2147483647;omega⟩,⟨902604800,by change 902604800<2147483647;omega⟩]
theorem rawCell09 : (raw.drop 144).take 16=cell09.val := by
  simp only [raw,JFz_Scan54.data,JFz_Scan54.j00,JFz_Scan54.j01,JFz_Scan54.j02,JFz_Scan54.j03,JFz_Scan54.j04,JFz_Scan54.j05,JFz_Scan54.j06,JFz_Scan54.j07,JFz_Scan54.j08,JFz_Scan54.j09,JFz_Scan54.j10,JFz_Scan54.j11,JFz_Scan54.j12,JFz_Scan54.b00_length,JFz_Scan54.b01_length,JFz_Scan54.b02_length,JFz_Scan54.b03_length,JFz_Scan54.b04_length,JFz_Scan54.b05_length,JFz_Scan54.b06_length,JFz_Scan54.b07_length,JFz_Scan54.b08_length,JFz_Scan54.b09_length,JFz_Scan54.b10_length,JFz_Scan54.b11_length,JFz_Scan54.b12_length,JFz_Scan54.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell09
theorem encoded09 : CandidateParserByteOrder.arrayBytes16 cell09=encodeQM31LE limbs09 := by
  funext i
  fin_cases i <;> rfl
theorem parser09 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell09)=
    ok (some ⟨⟨1532119718#u32,173394929#u32⟩,⟨1000857122#u32,902604800#u32⟩⟩) :=
  JFr_EncodedCell.parser cell09 limbs09 encoded09
#print axioms encoded09
#print axioms parser09
def cell10 : Array U8 16#usize := ⟨[54#u8,70#u8,90#u8,13#u8,179#u8,137#u8,74#u8,26#u8,68#u8,160#u8,23#u8,7#u8,226#u8,147#u8,87#u8,79#u8],by rfl⟩
def limbs10 : QM31Limbs := ![⟨224020022,by change 224020022<2147483647;omega⟩,⟨441092531,by change 441092531<2147483647;omega⟩,⟨118988868,by change 118988868<2147483647;omega⟩,⟨1331139554,by change 1331139554<2147483647;omega⟩]
theorem rawCell10 : (raw.drop 160).take 16=cell10.val := by
  simp only [raw,JFz_Scan54.data,JFz_Scan54.j00,JFz_Scan54.j01,JFz_Scan54.j02,JFz_Scan54.j03,JFz_Scan54.j04,JFz_Scan54.j05,JFz_Scan54.j06,JFz_Scan54.j07,JFz_Scan54.j08,JFz_Scan54.j09,JFz_Scan54.j10,JFz_Scan54.j11,JFz_Scan54.j12,JFz_Scan54.b00_length,JFz_Scan54.b01_length,JFz_Scan54.b02_length,JFz_Scan54.b03_length,JFz_Scan54.b04_length,JFz_Scan54.b05_length,JFz_Scan54.b06_length,JFz_Scan54.b07_length,JFz_Scan54.b08_length,JFz_Scan54.b09_length,JFz_Scan54.b10_length,JFz_Scan54.b11_length,JFz_Scan54.b12_length,JFz_Scan54.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell10
theorem encoded10 : CandidateParserByteOrder.arrayBytes16 cell10=encodeQM31LE limbs10 := by
  funext i
  fin_cases i <;> rfl
theorem parser10 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell10)=
    ok (some ⟨⟨224020022#u32,441092531#u32⟩,⟨118988868#u32,1331139554#u32⟩⟩) :=
  JFr_EncodedCell.parser cell10 limbs10 encoded10
#print axioms encoded10
#print axioms parser10
def cell11 : Array U8 16#usize := ⟨[33#u8,61#u8,115#u8,46#u8,113#u8,187#u8,92#u8,120#u8,203#u8,92#u8,80#u8,92#u8,128#u8,128#u8,115#u8,75#u8],by rfl⟩
def limbs11 : QM31Limbs := ![⟨779304225,by change 779304225<2147483647;omega⟩,⟨2019343217,by change 2019343217<2147483647;omega⟩,⟨1548770507,by change 1548770507<2147483647;omega⟩,⟨1265860736,by change 1265860736<2147483647;omega⟩]
theorem rawCell11 : (raw.drop 176).take 16=cell11.val := by
  simp only [raw,JFz_Scan54.data,JFz_Scan54.j00,JFz_Scan54.j01,JFz_Scan54.j02,JFz_Scan54.j03,JFz_Scan54.j04,JFz_Scan54.j05,JFz_Scan54.j06,JFz_Scan54.j07,JFz_Scan54.j08,JFz_Scan54.j09,JFz_Scan54.j10,JFz_Scan54.j11,JFz_Scan54.j12,JFz_Scan54.b00_length,JFz_Scan54.b01_length,JFz_Scan54.b02_length,JFz_Scan54.b03_length,JFz_Scan54.b04_length,JFz_Scan54.b05_length,JFz_Scan54.b06_length,JFz_Scan54.b07_length,JFz_Scan54.b08_length,JFz_Scan54.b09_length,JFz_Scan54.b10_length,JFz_Scan54.b11_length,JFz_Scan54.b12_length,JFz_Scan54.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell11
theorem encoded11 : CandidateParserByteOrder.arrayBytes16 cell11=encodeQM31LE limbs11 := by
  funext i
  fin_cases i <;> rfl
theorem parser11 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell11)=
    ok (some ⟨⟨779304225#u32,2019343217#u32⟩,⟨1548770507#u32,1265860736#u32⟩⟩) :=
  JFr_EncodedCell.parser cell11 limbs11 encoded11
#print axioms encoded11
#print axioms parser11
def cell12 : Array U8 16#usize := ⟨[209#u8,247#u8,94#u8,98#u8,84#u8,132#u8,25#u8,100#u8,238#u8,146#u8,33#u8,87#u8,190#u8,198#u8,165#u8,34#u8],by rfl⟩
def limbs12 : QM31Limbs := ![⟨1650390993,by change 1650390993<2147483647;omega⟩,⟨1679393876,by change 1679393876<2147483647;omega⟩,⟨1461818094,by change 1461818094<2147483647;omega⟩,⟨581289662,by change 581289662<2147483647;omega⟩]
theorem rawCell12 : (raw.drop 192).take 16=cell12.val := by
  simp only [raw,JFz_Scan54.data,JFz_Scan54.j00,JFz_Scan54.j01,JFz_Scan54.j02,JFz_Scan54.j03,JFz_Scan54.j04,JFz_Scan54.j05,JFz_Scan54.j06,JFz_Scan54.j07,JFz_Scan54.j08,JFz_Scan54.j09,JFz_Scan54.j10,JFz_Scan54.j11,JFz_Scan54.j12,JFz_Scan54.b00_length,JFz_Scan54.b01_length,JFz_Scan54.b02_length,JFz_Scan54.b03_length,JFz_Scan54.b04_length,JFz_Scan54.b05_length,JFz_Scan54.b06_length,JFz_Scan54.b07_length,JFz_Scan54.b08_length,JFz_Scan54.b09_length,JFz_Scan54.b10_length,JFz_Scan54.b11_length,JFz_Scan54.b12_length,JFz_Scan54.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell12
theorem encoded12 : CandidateParserByteOrder.arrayBytes16 cell12=encodeQM31LE limbs12 := by
  funext i
  fin_cases i <;> rfl
theorem parser12 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell12)=
    ok (some ⟨⟨1650390993#u32,1679393876#u32⟩,⟨1461818094#u32,581289662#u32⟩⟩) :=
  JFr_EncodedCell.parser cell12 limbs12 encoded12
#print axioms encoded12
#print axioms parser12
def cell13 : Array U8 16#usize := ⟨[103#u8,93#u8,50#u8,5#u8,252#u8,252#u8,227#u8,60#u8,16#u8,75#u8,77#u8,125#u8,161#u8,140#u8,196#u8,69#u8],by rfl⟩
def limbs13 : QM31Limbs := ![⟨87186791,by change 87186791<2147483647;omega⟩,⟨1021574396,by change 1021574396<2147483647;omega⟩,⟨2102217488,by change 2102217488<2147483647;omega⟩,⟨1170508961,by change 1170508961<2147483647;omega⟩]
theorem rawCell13 : (raw.drop 208).take 16=cell13.val := by
  simp only [raw,JFz_Scan54.data,JFz_Scan54.j00,JFz_Scan54.j01,JFz_Scan54.j02,JFz_Scan54.j03,JFz_Scan54.j04,JFz_Scan54.j05,JFz_Scan54.j06,JFz_Scan54.j07,JFz_Scan54.j08,JFz_Scan54.j09,JFz_Scan54.j10,JFz_Scan54.j11,JFz_Scan54.j12,JFz_Scan54.b00_length,JFz_Scan54.b01_length,JFz_Scan54.b02_length,JFz_Scan54.b03_length,JFz_Scan54.b04_length,JFz_Scan54.b05_length,JFz_Scan54.b06_length,JFz_Scan54.b07_length,JFz_Scan54.b08_length,JFz_Scan54.b09_length,JFz_Scan54.b10_length,JFz_Scan54.b11_length,JFz_Scan54.b12_length,JFz_Scan54.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell13
theorem encoded13 : CandidateParserByteOrder.arrayBytes16 cell13=encodeQM31LE limbs13 := by
  funext i
  fin_cases i <;> rfl
theorem parser13 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell13)=
    ok (some ⟨⟨87186791#u32,1021574396#u32⟩,⟨2102217488#u32,1170508961#u32⟩⟩) :=
  JFr_EncodedCell.parser cell13 limbs13 encoded13
#print axioms encoded13
#print axioms parser13
def cell14 : Array U8 16#usize := ⟨[231#u8,29#u8,24#u8,12#u8,254#u8,222#u8,171#u8,35#u8,34#u8,121#u8,71#u8,68#u8,152#u8,131#u8,69#u8,34#u8],by rfl⟩
def limbs14 : QM31Limbs := ![⟨202907111,by change 202907111<2147483647;omega⟩,⟨598466302,by change 598466302<2147483647;omega⟩,⟨1145534754,by change 1145534754<2147483647;omega⟩,⟨574981016,by change 574981016<2147483647;omega⟩]
theorem rawCell14 : (raw.drop 224).take 16=cell14.val := by
  simp only [raw,JFz_Scan54.data,JFz_Scan54.j00,JFz_Scan54.j01,JFz_Scan54.j02,JFz_Scan54.j03,JFz_Scan54.j04,JFz_Scan54.j05,JFz_Scan54.j06,JFz_Scan54.j07,JFz_Scan54.j08,JFz_Scan54.j09,JFz_Scan54.j10,JFz_Scan54.j11,JFz_Scan54.j12,JFz_Scan54.b00_length,JFz_Scan54.b01_length,JFz_Scan54.b02_length,JFz_Scan54.b03_length,JFz_Scan54.b04_length,JFz_Scan54.b05_length,JFz_Scan54.b06_length,JFz_Scan54.b07_length,JFz_Scan54.b08_length,JFz_Scan54.b09_length,JFz_Scan54.b10_length,JFz_Scan54.b11_length,JFz_Scan54.b12_length,JFz_Scan54.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell14
theorem encoded14 : CandidateParserByteOrder.arrayBytes16 cell14=encodeQM31LE limbs14 := by
  funext i
  fin_cases i <;> rfl
theorem parser14 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell14)=
    ok (some ⟨⟨202907111#u32,598466302#u32⟩,⟨1145534754#u32,574981016#u32⟩⟩) :=
  JFr_EncodedCell.parser cell14 limbs14 encoded14
#print axioms encoded14
#print axioms parser14
def cell15 : Array U8 16#usize := ⟨[164#u8,178#u8,207#u8,92#u8,165#u8,18#u8,44#u8,54#u8,152#u8,217#u8,239#u8,2#u8,120#u8,5#u8,101#u8,70#u8],by rfl⟩
def limbs15 : QM31Limbs := ![⟨1557115556,by change 1557115556<2147483647;omega⟩,⟨908858021,by change 908858021<2147483647;omega⟩,⟨49273240,by change 49273240<2147483647;omega⟩,⟨1181025656,by change 1181025656<2147483647;omega⟩]
theorem rawCell15 : (raw.drop 240).take 16=cell15.val := by
  simp only [raw,JFz_Scan54.data,JFz_Scan54.j00,JFz_Scan54.j01,JFz_Scan54.j02,JFz_Scan54.j03,JFz_Scan54.j04,JFz_Scan54.j05,JFz_Scan54.j06,JFz_Scan54.j07,JFz_Scan54.j08,JFz_Scan54.j09,JFz_Scan54.j10,JFz_Scan54.j11,JFz_Scan54.j12,JFz_Scan54.b00_length,JFz_Scan54.b01_length,JFz_Scan54.b02_length,JFz_Scan54.b03_length,JFz_Scan54.b04_length,JFz_Scan54.b05_length,JFz_Scan54.b06_length,JFz_Scan54.b07_length,JFz_Scan54.b08_length,JFz_Scan54.b09_length,JFz_Scan54.b10_length,JFz_Scan54.b11_length,JFz_Scan54.b12_length,JFz_Scan54.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell15
theorem encoded15 : CandidateParserByteOrder.arrayBytes16 cell15=encodeQM31LE limbs15 := by
  funext i
  fin_cases i <;> rfl
theorem parser15 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell15)=
    ok (some ⟨⟨1557115556#u32,908858021#u32⟩,⟨49273240#u32,1181025656#u32⟩⟩) :=
  JFr_EncodedCell.parser cell15 limbs15 encoded15
#print axioms encoded15
#print axioms parser15
def cell16 : Array U8 16#usize := ⟨[201#u8,153#u8,195#u8,46#u8,112#u8,47#u8,81#u8,52#u8,228#u8,10#u8,200#u8,118#u8,144#u8,186#u8,188#u8,49#u8],by rfl⟩
def limbs16 : QM31Limbs := ![⟨784570825,by change 784570825<2147483647;omega⟩,⟨877735792,by change 877735792<2147483647;omega⟩,⟨1992821476,by change 1992821476<2147483647;omega⟩,⟨834452112,by change 834452112<2147483647;omega⟩]
theorem rawCell16 : (raw.drop 256).take 16=cell16.val := by
  simp only [raw,JFz_Scan54.data,JFz_Scan54.j00,JFz_Scan54.j01,JFz_Scan54.j02,JFz_Scan54.j03,JFz_Scan54.j04,JFz_Scan54.j05,JFz_Scan54.j06,JFz_Scan54.j07,JFz_Scan54.j08,JFz_Scan54.j09,JFz_Scan54.j10,JFz_Scan54.j11,JFz_Scan54.j12,JFz_Scan54.b00_length,JFz_Scan54.b01_length,JFz_Scan54.b02_length,JFz_Scan54.b03_length,JFz_Scan54.b04_length,JFz_Scan54.b05_length,JFz_Scan54.b06_length,JFz_Scan54.b07_length,JFz_Scan54.b08_length,JFz_Scan54.b09_length,JFz_Scan54.b10_length,JFz_Scan54.b11_length,JFz_Scan54.b12_length,JFz_Scan54.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell16
theorem encoded16 : CandidateParserByteOrder.arrayBytes16 cell16=encodeQM31LE limbs16 := by
  funext i
  fin_cases i <;> rfl
theorem parser16 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell16)=
    ok (some ⟨⟨784570825#u32,877735792#u32⟩,⟨1992821476#u32,834452112#u32⟩⟩) :=
  JFr_EncodedCell.parser cell16 limbs16 encoded16
#print axioms encoded16
#print axioms parser16
def cell17 : Array U8 16#usize := ⟨[212#u8,140#u8,16#u8,13#u8,26#u8,90#u8,215#u8,12#u8,234#u8,122#u8,14#u8,39#u8,102#u8,157#u8,100#u8,90#u8],by rfl⟩
def limbs17 : QM31Limbs := ![⟨219188436,by change 219188436<2147483647;omega⟩,⟨215439898,by change 215439898<2147483647;omega⟩,⟨655260394,by change 655260394<2147483647;omega⟩,⟨1516543334,by change 1516543334<2147483647;omega⟩]
theorem rawCell17 : (raw.drop 272).take 16=cell17.val := by
  simp only [raw,JFz_Scan54.data,JFz_Scan54.j00,JFz_Scan54.j01,JFz_Scan54.j02,JFz_Scan54.j03,JFz_Scan54.j04,JFz_Scan54.j05,JFz_Scan54.j06,JFz_Scan54.j07,JFz_Scan54.j08,JFz_Scan54.j09,JFz_Scan54.j10,JFz_Scan54.j11,JFz_Scan54.j12,JFz_Scan54.b00_length,JFz_Scan54.b01_length,JFz_Scan54.b02_length,JFz_Scan54.b03_length,JFz_Scan54.b04_length,JFz_Scan54.b05_length,JFz_Scan54.b06_length,JFz_Scan54.b07_length,JFz_Scan54.b08_length,JFz_Scan54.b09_length,JFz_Scan54.b10_length,JFz_Scan54.b11_length,JFz_Scan54.b12_length,JFz_Scan54.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell17
theorem encoded17 : CandidateParserByteOrder.arrayBytes16 cell17=encodeQM31LE limbs17 := by
  funext i
  fin_cases i <;> rfl
theorem parser17 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell17)=
    ok (some ⟨⟨219188436#u32,215439898#u32⟩,⟨655260394#u32,1516543334#u32⟩⟩) :=
  JFr_EncodedCell.parser cell17 limbs17 encoded17
#print axioms encoded17
#print axioms parser17
def cell18 : Array U8 16#usize := ⟨[2#u8,159#u8,32#u8,122#u8,40#u8,205#u8,74#u8,4#u8,34#u8,88#u8,205#u8,42#u8,253#u8,171#u8,57#u8,85#u8],by rfl⟩
def limbs18 : QM31Limbs := ![⟨2048958210,by change 2048958210<2147483647;omega⟩,⟨72011048,by change 72011048<2147483647;omega⟩,⟨718100514,by change 718100514<2147483647;omega⟩,⟨1429842941,by change 1429842941<2147483647;omega⟩]
theorem rawCell18 : (raw.drop 288).take 16=cell18.val := by
  simp only [raw,JFz_Scan54.data,JFz_Scan54.j00,JFz_Scan54.j01,JFz_Scan54.j02,JFz_Scan54.j03,JFz_Scan54.j04,JFz_Scan54.j05,JFz_Scan54.j06,JFz_Scan54.j07,JFz_Scan54.j08,JFz_Scan54.j09,JFz_Scan54.j10,JFz_Scan54.j11,JFz_Scan54.j12,JFz_Scan54.b00_length,JFz_Scan54.b01_length,JFz_Scan54.b02_length,JFz_Scan54.b03_length,JFz_Scan54.b04_length,JFz_Scan54.b05_length,JFz_Scan54.b06_length,JFz_Scan54.b07_length,JFz_Scan54.b08_length,JFz_Scan54.b09_length,JFz_Scan54.b10_length,JFz_Scan54.b11_length,JFz_Scan54.b12_length,JFz_Scan54.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell18
theorem encoded18 : CandidateParserByteOrder.arrayBytes16 cell18=encodeQM31LE limbs18 := by
  funext i
  fin_cases i <;> rfl
theorem parser18 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell18)=
    ok (some ⟨⟨2048958210#u32,72011048#u32⟩,⟨718100514#u32,1429842941#u32⟩⟩) :=
  JFr_EncodedCell.parser cell18 limbs18 encoded18
#print axioms encoded18
#print axioms parser18
def cell19 : Array U8 16#usize := ⟨[140#u8,231#u8,107#u8,76#u8,95#u8,237#u8,178#u8,122#u8,142#u8,249#u8,130#u8,68#u8,24#u8,144#u8,82#u8,78#u8],by rfl⟩
def limbs19 : QM31Limbs := ![⟨1282140044,by change 1282140044<2147483647;omega⟩,⟨2058546527,by change 2058546527<2147483647;omega⟩,⟨1149434254,by change 1149434254<2147483647;omega⟩,⟨1314033688,by change 1314033688<2147483647;omega⟩]
theorem rawCell19 : (raw.drop 304).take 16=cell19.val := by
  simp only [raw,JFz_Scan54.data,JFz_Scan54.j00,JFz_Scan54.j01,JFz_Scan54.j02,JFz_Scan54.j03,JFz_Scan54.j04,JFz_Scan54.j05,JFz_Scan54.j06,JFz_Scan54.j07,JFz_Scan54.j08,JFz_Scan54.j09,JFz_Scan54.j10,JFz_Scan54.j11,JFz_Scan54.j12,JFz_Scan54.b00_length,JFz_Scan54.b01_length,JFz_Scan54.b02_length,JFz_Scan54.b03_length,JFz_Scan54.b04_length,JFz_Scan54.b05_length,JFz_Scan54.b06_length,JFz_Scan54.b07_length,JFz_Scan54.b08_length,JFz_Scan54.b09_length,JFz_Scan54.b10_length,JFz_Scan54.b11_length,JFz_Scan54.b12_length,JFz_Scan54.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell19
theorem encoded19 : CandidateParserByteOrder.arrayBytes16 cell19=encodeQM31LE limbs19 := by
  funext i
  fin_cases i <;> rfl
theorem parser19 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell19)=
    ok (some ⟨⟨1282140044#u32,2058546527#u32⟩,⟨1149434254#u32,1314033688#u32⟩⟩) :=
  JFr_EncodedCell.parser cell19 limbs19 encoded19
#print axioms encoded19
#print axioms parser19
def cell20 : Array U8 16#usize := ⟨[138#u8,176#u8,177#u8,24#u8,17#u8,193#u8,241#u8,52#u8,249#u8,196#u8,11#u8,106#u8,145#u8,180#u8,134#u8,38#u8],by rfl⟩
def limbs20 : QM31Limbs := ![⟨414298250,by change 414298250<2147483647;omega⟩,⟨888258833,by change 888258833<2147483647;omega⟩,⟨1779156217,by change 1779156217<2147483647;omega⟩,⟨646362257,by change 646362257<2147483647;omega⟩]
theorem rawCell20 : (raw.drop 320).take 16=cell20.val := by
  simp only [raw,JFz_Scan54.data,JFz_Scan54.j00,JFz_Scan54.j01,JFz_Scan54.j02,JFz_Scan54.j03,JFz_Scan54.j04,JFz_Scan54.j05,JFz_Scan54.j06,JFz_Scan54.j07,JFz_Scan54.j08,JFz_Scan54.j09,JFz_Scan54.j10,JFz_Scan54.j11,JFz_Scan54.j12,JFz_Scan54.b00_length,JFz_Scan54.b01_length,JFz_Scan54.b02_length,JFz_Scan54.b03_length,JFz_Scan54.b04_length,JFz_Scan54.b05_length,JFz_Scan54.b06_length,JFz_Scan54.b07_length,JFz_Scan54.b08_length,JFz_Scan54.b09_length,JFz_Scan54.b10_length,JFz_Scan54.b11_length,JFz_Scan54.b12_length,JFz_Scan54.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell20
theorem encoded20 : CandidateParserByteOrder.arrayBytes16 cell20=encodeQM31LE limbs20 := by
  funext i
  fin_cases i <;> rfl
theorem parser20 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell20)=
    ok (some ⟨⟨414298250#u32,888258833#u32⟩,⟨1779156217#u32,646362257#u32⟩⟩) :=
  JFr_EncodedCell.parser cell20 limbs20 encoded20
#print axioms encoded20
#print axioms parser20
def cell21 : Array U8 16#usize := ⟨[128#u8,43#u8,28#u8,12#u8,253#u8,246#u8,251#u8,26#u8,14#u8,61#u8,201#u8,9#u8,110#u8,111#u8,68#u8,69#u8],by rfl⟩
def limbs21 : QM31Limbs := ![⟨203172736,by change 203172736<2147483647;omega⟩,⟨452720381,by change 452720381<2147483647;omega⟩,⟨164183310,by change 164183310<2147483647;omega⟩,⟨1162112878,by change 1162112878<2147483647;omega⟩]
theorem rawCell21 : (raw.drop 336).take 16=cell21.val := by
  simp only [raw,JFz_Scan54.data,JFz_Scan54.j00,JFz_Scan54.j01,JFz_Scan54.j02,JFz_Scan54.j03,JFz_Scan54.j04,JFz_Scan54.j05,JFz_Scan54.j06,JFz_Scan54.j07,JFz_Scan54.j08,JFz_Scan54.j09,JFz_Scan54.j10,JFz_Scan54.j11,JFz_Scan54.j12,JFz_Scan54.b00_length,JFz_Scan54.b01_length,JFz_Scan54.b02_length,JFz_Scan54.b03_length,JFz_Scan54.b04_length,JFz_Scan54.b05_length,JFz_Scan54.b06_length,JFz_Scan54.b07_length,JFz_Scan54.b08_length,JFz_Scan54.b09_length,JFz_Scan54.b10_length,JFz_Scan54.b11_length,JFz_Scan54.b12_length,JFz_Scan54.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell21
theorem encoded21 : CandidateParserByteOrder.arrayBytes16 cell21=encodeQM31LE limbs21 := by
  funext i
  fin_cases i <;> rfl
theorem parser21 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell21)=
    ok (some ⟨⟨203172736#u32,452720381#u32⟩,⟨164183310#u32,1162112878#u32⟩⟩) :=
  JFr_EncodedCell.parser cell21 limbs21 encoded21
#print axioms encoded21
#print axioms parser21
def cell22 : Array U8 16#usize := ⟨[145#u8,111#u8,35#u8,73#u8,167#u8,207#u8,3#u8,124#u8,165#u8,11#u8,130#u8,6#u8,231#u8,138#u8,105#u8,114#u8],by rfl⟩
def limbs22 : QM31Limbs := ![⟨1227059089,by change 1227059089<2147483647;omega⟩,⟨2080624551,by change 2080624551<2147483647;omega⟩,⟨109185957,by change 109185957<2147483647;omega⟩,⟨1919519463,by change 1919519463<2147483647;omega⟩]
theorem rawCell22 : (raw.drop 352).take 16=cell22.val := by
  simp only [raw,JFz_Scan54.data,JFz_Scan54.j00,JFz_Scan54.j01,JFz_Scan54.j02,JFz_Scan54.j03,JFz_Scan54.j04,JFz_Scan54.j05,JFz_Scan54.j06,JFz_Scan54.j07,JFz_Scan54.j08,JFz_Scan54.j09,JFz_Scan54.j10,JFz_Scan54.j11,JFz_Scan54.j12,JFz_Scan54.b00_length,JFz_Scan54.b01_length,JFz_Scan54.b02_length,JFz_Scan54.b03_length,JFz_Scan54.b04_length,JFz_Scan54.b05_length,JFz_Scan54.b06_length,JFz_Scan54.b07_length,JFz_Scan54.b08_length,JFz_Scan54.b09_length,JFz_Scan54.b10_length,JFz_Scan54.b11_length,JFz_Scan54.b12_length,JFz_Scan54.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell22
theorem encoded22 : CandidateParserByteOrder.arrayBytes16 cell22=encodeQM31LE limbs22 := by
  funext i
  fin_cases i <;> rfl
theorem parser22 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell22)=
    ok (some ⟨⟨1227059089#u32,2080624551#u32⟩,⟨109185957#u32,1919519463#u32⟩⟩) :=
  JFr_EncodedCell.parser cell22 limbs22 encoded22
#print axioms encoded22
#print axioms parser22
def cell23 : Array U8 16#usize := ⟨[244#u8,199#u8,15#u8,52#u8,7#u8,23#u8,92#u8,51#u8,85#u8,179#u8,213#u8,117#u8,241#u8,146#u8,129#u8,29#u8],by rfl⟩
def limbs23 : QM31Limbs := ![⟨873449460,by change 873449460<2147483647;omega⟩,⟨861673223,by change 861673223<2147483647;omega⟩,⟨1976939349,by change 1976939349<2147483647;omega⟩,⟨495031025,by change 495031025<2147483647;omega⟩]
theorem rawCell23 : (raw.drop 368).take 16=cell23.val := by
  simp only [raw,JFz_Scan54.data,JFz_Scan54.j00,JFz_Scan54.j01,JFz_Scan54.j02,JFz_Scan54.j03,JFz_Scan54.j04,JFz_Scan54.j05,JFz_Scan54.j06,JFz_Scan54.j07,JFz_Scan54.j08,JFz_Scan54.j09,JFz_Scan54.j10,JFz_Scan54.j11,JFz_Scan54.j12,JFz_Scan54.b00_length,JFz_Scan54.b01_length,JFz_Scan54.b02_length,JFz_Scan54.b03_length,JFz_Scan54.b04_length,JFz_Scan54.b05_length,JFz_Scan54.b06_length,JFz_Scan54.b07_length,JFz_Scan54.b08_length,JFz_Scan54.b09_length,JFz_Scan54.b10_length,JFz_Scan54.b11_length,JFz_Scan54.b12_length,JFz_Scan54.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell23
theorem encoded23 : CandidateParserByteOrder.arrayBytes16 cell23=encodeQM31LE limbs23 := by
  funext i
  fin_cases i <;> rfl
theorem parser23 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell23)=
    ok (some ⟨⟨873449460#u32,861673223#u32⟩,⟨1976939349#u32,495031025#u32⟩⟩) :=
  JFr_EncodedCell.parser cell23 limbs23 encoded23
#print axioms encoded23
#print axioms parser23
def cell24 : Array U8 16#usize := ⟨[55#u8,241#u8,139#u8,25#u8,56#u8,124#u8,89#u8,72#u8,27#u8,61#u8,25#u8,1#u8,54#u8,70#u8,88#u8,93#u8],by rfl⟩
def limbs24 : QM31Limbs := ![⟨428601655,by change 428601655<2147483647;omega⟩,⟨1213824056,by change 1213824056<2147483647;omega⟩,⟨18431259,by change 18431259<2147483647;omega⟩,⟨1566066230,by change 1566066230<2147483647;omega⟩]
theorem rawCell24 : (raw.drop 384).take 16=cell24.val := by
  simp only [raw,JFz_Scan54.data,JFz_Scan54.j00,JFz_Scan54.j01,JFz_Scan54.j02,JFz_Scan54.j03,JFz_Scan54.j04,JFz_Scan54.j05,JFz_Scan54.j06,JFz_Scan54.j07,JFz_Scan54.j08,JFz_Scan54.j09,JFz_Scan54.j10,JFz_Scan54.j11,JFz_Scan54.j12,JFz_Scan54.b00_length,JFz_Scan54.b01_length,JFz_Scan54.b02_length,JFz_Scan54.b03_length,JFz_Scan54.b04_length,JFz_Scan54.b05_length,JFz_Scan54.b06_length,JFz_Scan54.b07_length,JFz_Scan54.b08_length,JFz_Scan54.b09_length,JFz_Scan54.b10_length,JFz_Scan54.b11_length,JFz_Scan54.b12_length,JFz_Scan54.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell24
theorem encoded24 : CandidateParserByteOrder.arrayBytes16 cell24=encodeQM31LE limbs24 := by
  funext i
  fin_cases i <;> rfl
theorem parser24 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell24)=
    ok (some ⟨⟨428601655#u32,1213824056#u32⟩,⟨18431259#u32,1566066230#u32⟩⟩) :=
  JFr_EncodedCell.parser cell24 limbs24 encoded24
#print axioms encoded24
#print axioms parser24
def cell25 : Array U8 16#usize := ⟨[139#u8,186#u8,214#u8,17#u8,129#u8,52#u8,195#u8,70#u8,193#u8,67#u8,101#u8,14#u8,255#u8,156#u8,228#u8,15#u8],by rfl⟩
def limbs25 : QM31Limbs := ![⟨299285131,by change 299285131<2147483647;omega⟩,⟨1187198081,by change 1187198081<2147483647;omega⟩,⟨241517505,by change 241517505<2147483647;omega⟩,⟨266640639,by change 266640639<2147483647;omega⟩]
theorem rawCell25 : (raw.drop 400).take 16=cell25.val := by
  simp only [raw,JFz_Scan54.data,JFz_Scan54.j00,JFz_Scan54.j01,JFz_Scan54.j02,JFz_Scan54.j03,JFz_Scan54.j04,JFz_Scan54.j05,JFz_Scan54.j06,JFz_Scan54.j07,JFz_Scan54.j08,JFz_Scan54.j09,JFz_Scan54.j10,JFz_Scan54.j11,JFz_Scan54.j12,JFz_Scan54.b00_length,JFz_Scan54.b01_length,JFz_Scan54.b02_length,JFz_Scan54.b03_length,JFz_Scan54.b04_length,JFz_Scan54.b05_length,JFz_Scan54.b06_length,JFz_Scan54.b07_length,JFz_Scan54.b08_length,JFz_Scan54.b09_length,JFz_Scan54.b10_length,JFz_Scan54.b11_length,JFz_Scan54.b12_length,JFz_Scan54.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell25
theorem encoded25 : CandidateParserByteOrder.arrayBytes16 cell25=encodeQM31LE limbs25 := by
  funext i
  fin_cases i <;> rfl
theorem parser25 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell25)=
    ok (some ⟨⟨299285131#u32,1187198081#u32⟩,⟨241517505#u32,266640639#u32⟩⟩) :=
  JFr_EncodedCell.parser cell25 limbs25 encoded25
#print axioms encoded25
#print axioms parser25
def cell26 : Array U8 16#usize := ⟨[197#u8,17#u8,253#u8,73#u8,92#u8,1#u8,213#u8,81#u8,48#u8,17#u8,65#u8,96#u8,158#u8,28#u8,254#u8,94#u8],by rfl⟩
def limbs26 : QM31Limbs := ![⟨1241321925,by change 1241321925<2147483647;omega⟩,⟨1372914012,by change 1372914012<2147483647;omega⟩,⟨1614876976,by change 1614876976<2147483647;omega⟩,⟨1593711774,by change 1593711774<2147483647;omega⟩]
theorem rawCell26 : (raw.drop 416).take 16=cell26.val := by
  simp only [raw,JFz_Scan54.data,JFz_Scan54.j00,JFz_Scan54.j01,JFz_Scan54.j02,JFz_Scan54.j03,JFz_Scan54.j04,JFz_Scan54.j05,JFz_Scan54.j06,JFz_Scan54.j07,JFz_Scan54.j08,JFz_Scan54.j09,JFz_Scan54.j10,JFz_Scan54.j11,JFz_Scan54.j12,JFz_Scan54.b00_length,JFz_Scan54.b01_length,JFz_Scan54.b02_length,JFz_Scan54.b03_length,JFz_Scan54.b04_length,JFz_Scan54.b05_length,JFz_Scan54.b06_length,JFz_Scan54.b07_length,JFz_Scan54.b08_length,JFz_Scan54.b09_length,JFz_Scan54.b10_length,JFz_Scan54.b11_length,JFz_Scan54.b12_length,JFz_Scan54.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell26
theorem encoded26 : CandidateParserByteOrder.arrayBytes16 cell26=encodeQM31LE limbs26 := by
  funext i
  fin_cases i <;> rfl
theorem parser26 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell26)=
    ok (some ⟨⟨1241321925#u32,1372914012#u32⟩,⟨1614876976#u32,1593711774#u32⟩⟩) :=
  JFr_EncodedCell.parser cell26 limbs26 encoded26
#print axioms encoded26
#print axioms parser26
def cell27 : Array U8 16#usize := ⟨[193#u8,160#u8,180#u8,40#u8,6#u8,56#u8,24#u8,114#u8,191#u8,234#u8,200#u8,95#u8,99#u8,114#u8,189#u8,34#u8],by rfl⟩
def limbs27 : QM31Limbs := ![⟨682926273,by change 682926273<2147483647;omega⟩,⟨1914189830,by change 1914189830<2147483647;omega⟩,⟨1607002815,by change 1607002815<2147483647;omega⟩,⟨582840931,by change 582840931<2147483647;omega⟩]
theorem rawCell27 : (raw.drop 432).take 16=cell27.val := by
  simp only [raw,JFz_Scan54.data,JFz_Scan54.j00,JFz_Scan54.j01,JFz_Scan54.j02,JFz_Scan54.j03,JFz_Scan54.j04,JFz_Scan54.j05,JFz_Scan54.j06,JFz_Scan54.j07,JFz_Scan54.j08,JFz_Scan54.j09,JFz_Scan54.j10,JFz_Scan54.j11,JFz_Scan54.j12,JFz_Scan54.b00_length,JFz_Scan54.b01_length,JFz_Scan54.b02_length,JFz_Scan54.b03_length,JFz_Scan54.b04_length,JFz_Scan54.b05_length,JFz_Scan54.b06_length,JFz_Scan54.b07_length,JFz_Scan54.b08_length,JFz_Scan54.b09_length,JFz_Scan54.b10_length,JFz_Scan54.b11_length,JFz_Scan54.b12_length,JFz_Scan54.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell27
theorem encoded27 : CandidateParserByteOrder.arrayBytes16 cell27=encodeQM31LE limbs27 := by
  funext i
  fin_cases i <;> rfl
theorem parser27 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell27)=
    ok (some ⟨⟨682926273#u32,1914189830#u32⟩,⟨1607002815#u32,582840931#u32⟩⟩) :=
  JFr_EncodedCell.parser cell27 limbs27 encoded27
#print axioms encoded27
#print axioms parser27
end AspisR1.JFr_Bytes06
