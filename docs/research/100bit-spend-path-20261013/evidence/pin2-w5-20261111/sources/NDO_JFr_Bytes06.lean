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
def cell00 : Array U8 16#usize := ⟨[36#u8,112#u8,202#u8,52#u8,198#u8,130#u8,117#u8,53#u8,167#u8,107#u8,66#u8,94#u8,169#u8,144#u8,150#u8,5#u8],by rfl⟩
def limbs00 : QM31Limbs := ![⟨885682212,by change 885682212<2147483647;omega⟩,⟨896893638,by change 896893638<2147483647;omega⟩,⟨1581411239,by change 1581411239<2147483647;omega⟩,⟨93753513,by change 93753513<2147483647;omega⟩]
theorem rawCell00 : (raw.drop 0).take 16=cell00.val := by
  simp only [raw,JFz_Scan54.data,JFz_Scan54.j00,JFz_Scan54.j01,JFz_Scan54.j02,JFz_Scan54.j03,JFz_Scan54.j04,JFz_Scan54.j05,JFz_Scan54.j06,JFz_Scan54.j07,JFz_Scan54.j08,JFz_Scan54.j09,JFz_Scan54.j10,JFz_Scan54.j11,JFz_Scan54.j12,JFz_Scan54.b00_length,JFz_Scan54.b01_length,JFz_Scan54.b02_length,JFz_Scan54.b03_length,JFz_Scan54.b04_length,JFz_Scan54.b05_length,JFz_Scan54.b06_length,JFz_Scan54.b07_length,JFz_Scan54.b08_length,JFz_Scan54.b09_length,JFz_Scan54.b10_length,JFz_Scan54.b11_length,JFz_Scan54.b12_length,JFz_Scan54.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell00
theorem encoded00 : CandidateParserByteOrder.arrayBytes16 cell00=encodeQM31LE limbs00 := by
  funext i
  fin_cases i <;> rfl
theorem parser00 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell00)=
    ok (some ⟨⟨885682212#u32,896893638#u32⟩,⟨1581411239#u32,93753513#u32⟩⟩) :=
  JFr_EncodedCell.parser cell00 limbs00 encoded00
#print axioms encoded00
#print axioms parser00
def cell01 : Array U8 16#usize := ⟨[227#u8,154#u8,128#u8,39#u8,173#u8,142#u8,6#u8,97#u8,9#u8,11#u8,21#u8,29#u8,102#u8,21#u8,196#u8,90#u8],by rfl⟩
def limbs01 : QM31Limbs := ![⟨662739683,by change 662739683<2147483647;omega⟩,⟨1627819693,by change 1627819693<2147483647;omega⟩,⟨487918345,by change 487918345<2147483647;omega⟩,⟨1522799974,by change 1522799974<2147483647;omega⟩]
theorem rawCell01 : (raw.drop 16).take 16=cell01.val := by
  simp only [raw,JFz_Scan54.data,JFz_Scan54.j00,JFz_Scan54.j01,JFz_Scan54.j02,JFz_Scan54.j03,JFz_Scan54.j04,JFz_Scan54.j05,JFz_Scan54.j06,JFz_Scan54.j07,JFz_Scan54.j08,JFz_Scan54.j09,JFz_Scan54.j10,JFz_Scan54.j11,JFz_Scan54.j12,JFz_Scan54.b00_length,JFz_Scan54.b01_length,JFz_Scan54.b02_length,JFz_Scan54.b03_length,JFz_Scan54.b04_length,JFz_Scan54.b05_length,JFz_Scan54.b06_length,JFz_Scan54.b07_length,JFz_Scan54.b08_length,JFz_Scan54.b09_length,JFz_Scan54.b10_length,JFz_Scan54.b11_length,JFz_Scan54.b12_length,JFz_Scan54.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell01
theorem encoded01 : CandidateParserByteOrder.arrayBytes16 cell01=encodeQM31LE limbs01 := by
  funext i
  fin_cases i <;> rfl
theorem parser01 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell01)=
    ok (some ⟨⟨662739683#u32,1627819693#u32⟩,⟨487918345#u32,1522799974#u32⟩⟩) :=
  JFr_EncodedCell.parser cell01 limbs01 encoded01
#print axioms encoded01
#print axioms parser01
def cell02 : Array U8 16#usize := ⟨[180#u8,121#u8,23#u8,37#u8,22#u8,162#u8,125#u8,19#u8,246#u8,177#u8,58#u8,36#u8,185#u8,122#u8,131#u8,6#u8],by rfl⟩
def limbs02 : QM31Limbs := ![⟨622295476,by change 622295476<2147483647;omega⟩,⟨327000598,by change 327000598<2147483647;omega⟩,⟨607826422,by change 607826422<2147483647;omega⟩,⟨109279929,by change 109279929<2147483647;omega⟩]
theorem rawCell02 : (raw.drop 32).take 16=cell02.val := by
  simp only [raw,JFz_Scan54.data,JFz_Scan54.j00,JFz_Scan54.j01,JFz_Scan54.j02,JFz_Scan54.j03,JFz_Scan54.j04,JFz_Scan54.j05,JFz_Scan54.j06,JFz_Scan54.j07,JFz_Scan54.j08,JFz_Scan54.j09,JFz_Scan54.j10,JFz_Scan54.j11,JFz_Scan54.j12,JFz_Scan54.b00_length,JFz_Scan54.b01_length,JFz_Scan54.b02_length,JFz_Scan54.b03_length,JFz_Scan54.b04_length,JFz_Scan54.b05_length,JFz_Scan54.b06_length,JFz_Scan54.b07_length,JFz_Scan54.b08_length,JFz_Scan54.b09_length,JFz_Scan54.b10_length,JFz_Scan54.b11_length,JFz_Scan54.b12_length,JFz_Scan54.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell02
theorem encoded02 : CandidateParserByteOrder.arrayBytes16 cell02=encodeQM31LE limbs02 := by
  funext i
  fin_cases i <;> rfl
theorem parser02 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell02)=
    ok (some ⟨⟨622295476#u32,327000598#u32⟩,⟨607826422#u32,109279929#u32⟩⟩) :=
  JFr_EncodedCell.parser cell02 limbs02 encoded02
#print axioms encoded02
#print axioms parser02
def cell03 : Array U8 16#usize := ⟨[202#u8,228#u8,185#u8,72#u8,4#u8,57#u8,159#u8,95#u8,71#u8,124#u8,175#u8,7#u8,106#u8,183#u8,225#u8,29#u8],by rfl⟩
def limbs03 : QM31Limbs := ![⟨1220142282,by change 1220142282<2147483647;omega⟩,⟨1604270340,by change 1604270340<2147483647;omega⟩,⟨128941127,by change 128941127<2147483647;omega⟩,⟨501331818,by change 501331818<2147483647;omega⟩]
theorem rawCell03 : (raw.drop 48).take 16=cell03.val := by
  simp only [raw,JFz_Scan54.data,JFz_Scan54.j00,JFz_Scan54.j01,JFz_Scan54.j02,JFz_Scan54.j03,JFz_Scan54.j04,JFz_Scan54.j05,JFz_Scan54.j06,JFz_Scan54.j07,JFz_Scan54.j08,JFz_Scan54.j09,JFz_Scan54.j10,JFz_Scan54.j11,JFz_Scan54.j12,JFz_Scan54.b00_length,JFz_Scan54.b01_length,JFz_Scan54.b02_length,JFz_Scan54.b03_length,JFz_Scan54.b04_length,JFz_Scan54.b05_length,JFz_Scan54.b06_length,JFz_Scan54.b07_length,JFz_Scan54.b08_length,JFz_Scan54.b09_length,JFz_Scan54.b10_length,JFz_Scan54.b11_length,JFz_Scan54.b12_length,JFz_Scan54.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell03
theorem encoded03 : CandidateParserByteOrder.arrayBytes16 cell03=encodeQM31LE limbs03 := by
  funext i
  fin_cases i <;> rfl
theorem parser03 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell03)=
    ok (some ⟨⟨1220142282#u32,1604270340#u32⟩,⟨128941127#u32,501331818#u32⟩⟩) :=
  JFr_EncodedCell.parser cell03 limbs03 encoded03
#print axioms encoded03
#print axioms parser03
def cell04 : Array U8 16#usize := ⟨[101#u8,126#u8,93#u8,120#u8,152#u8,99#u8,41#u8,71#u8,120#u8,139#u8,213#u8,82#u8,216#u8,153#u8,165#u8,22#u8],by rfl⟩
def limbs04 : QM31Limbs := ![⟨2019393125,by change 2019393125<2147483647;omega⟩,⟨1193894808,by change 1193894808<2147483647;omega⟩,⟨1389726584,by change 1389726584<2147483647;omega⟩,⟨379951576,by change 379951576<2147483647;omega⟩]
theorem rawCell04 : (raw.drop 64).take 16=cell04.val := by
  simp only [raw,JFz_Scan54.data,JFz_Scan54.j00,JFz_Scan54.j01,JFz_Scan54.j02,JFz_Scan54.j03,JFz_Scan54.j04,JFz_Scan54.j05,JFz_Scan54.j06,JFz_Scan54.j07,JFz_Scan54.j08,JFz_Scan54.j09,JFz_Scan54.j10,JFz_Scan54.j11,JFz_Scan54.j12,JFz_Scan54.b00_length,JFz_Scan54.b01_length,JFz_Scan54.b02_length,JFz_Scan54.b03_length,JFz_Scan54.b04_length,JFz_Scan54.b05_length,JFz_Scan54.b06_length,JFz_Scan54.b07_length,JFz_Scan54.b08_length,JFz_Scan54.b09_length,JFz_Scan54.b10_length,JFz_Scan54.b11_length,JFz_Scan54.b12_length,JFz_Scan54.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell04
theorem encoded04 : CandidateParserByteOrder.arrayBytes16 cell04=encodeQM31LE limbs04 := by
  funext i
  fin_cases i <;> rfl
theorem parser04 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell04)=
    ok (some ⟨⟨2019393125#u32,1193894808#u32⟩,⟨1389726584#u32,379951576#u32⟩⟩) :=
  JFr_EncodedCell.parser cell04 limbs04 encoded04
#print axioms encoded04
#print axioms parser04
def cell05 : Array U8 16#usize := ⟨[198#u8,107#u8,102#u8,83#u8,33#u8,103#u8,149#u8,85#u8,121#u8,74#u8,177#u8,84#u8,12#u8,132#u8,28#u8,99#u8],by rfl⟩
def limbs05 : QM31Limbs := ![⟨1399221190,by change 1399221190<2147483647;omega⟩,⟨1435854625,by change 1435854625<2147483647;omega⟩,⟨1420905081,by change 1420905081<2147483647;omega⟩,⟨1662813196,by change 1662813196<2147483647;omega⟩]
theorem rawCell05 : (raw.drop 80).take 16=cell05.val := by
  simp only [raw,JFz_Scan54.data,JFz_Scan54.j00,JFz_Scan54.j01,JFz_Scan54.j02,JFz_Scan54.j03,JFz_Scan54.j04,JFz_Scan54.j05,JFz_Scan54.j06,JFz_Scan54.j07,JFz_Scan54.j08,JFz_Scan54.j09,JFz_Scan54.j10,JFz_Scan54.j11,JFz_Scan54.j12,JFz_Scan54.b00_length,JFz_Scan54.b01_length,JFz_Scan54.b02_length,JFz_Scan54.b03_length,JFz_Scan54.b04_length,JFz_Scan54.b05_length,JFz_Scan54.b06_length,JFz_Scan54.b07_length,JFz_Scan54.b08_length,JFz_Scan54.b09_length,JFz_Scan54.b10_length,JFz_Scan54.b11_length,JFz_Scan54.b12_length,JFz_Scan54.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell05
theorem encoded05 : CandidateParserByteOrder.arrayBytes16 cell05=encodeQM31LE limbs05 := by
  funext i
  fin_cases i <;> rfl
theorem parser05 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell05)=
    ok (some ⟨⟨1399221190#u32,1435854625#u32⟩,⟨1420905081#u32,1662813196#u32⟩⟩) :=
  JFr_EncodedCell.parser cell05 limbs05 encoded05
#print axioms encoded05
#print axioms parser05
def cell06 : Array U8 16#usize := ⟨[75#u8,82#u8,188#u8,32#u8,201#u8,229#u8,218#u8,23#u8,139#u8,71#u8,167#u8,62#u8,208#u8,139#u8,165#u8,40#u8],by rfl⟩
def limbs06 : QM31Limbs := ![⟨549212747,by change 549212747<2147483647;omega⟩,⟨400221641,by change 400221641<2147483647;omega⟩,⟨1051150219,by change 1051150219<2147483647;omega⟩,⟨681937872,by change 681937872<2147483647;omega⟩]
theorem rawCell06 : (raw.drop 96).take 16=cell06.val := by
  simp only [raw,JFz_Scan54.data,JFz_Scan54.j00,JFz_Scan54.j01,JFz_Scan54.j02,JFz_Scan54.j03,JFz_Scan54.j04,JFz_Scan54.j05,JFz_Scan54.j06,JFz_Scan54.j07,JFz_Scan54.j08,JFz_Scan54.j09,JFz_Scan54.j10,JFz_Scan54.j11,JFz_Scan54.j12,JFz_Scan54.b00_length,JFz_Scan54.b01_length,JFz_Scan54.b02_length,JFz_Scan54.b03_length,JFz_Scan54.b04_length,JFz_Scan54.b05_length,JFz_Scan54.b06_length,JFz_Scan54.b07_length,JFz_Scan54.b08_length,JFz_Scan54.b09_length,JFz_Scan54.b10_length,JFz_Scan54.b11_length,JFz_Scan54.b12_length,JFz_Scan54.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell06
theorem encoded06 : CandidateParserByteOrder.arrayBytes16 cell06=encodeQM31LE limbs06 := by
  funext i
  fin_cases i <;> rfl
theorem parser06 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell06)=
    ok (some ⟨⟨549212747#u32,400221641#u32⟩,⟨1051150219#u32,681937872#u32⟩⟩) :=
  JFr_EncodedCell.parser cell06 limbs06 encoded06
#print axioms encoded06
#print axioms parser06
def cell07 : Array U8 16#usize := ⟨[7#u8,69#u8,34#u8,19#u8,244#u8,63#u8,74#u8,125#u8,45#u8,35#u8,194#u8,97#u8,81#u8,114#u8,197#u8,41#u8],by rfl⟩
def limbs07 : QM31Limbs := ![⟨321012999,by change 321012999<2147483647;omega⟩,⟨2102018036,by change 2102018036<2147483647;omega⟩,⟨1640112941,by change 1640112941<2147483647;omega⟩,⟨700805713,by change 700805713<2147483647;omega⟩]
theorem rawCell07 : (raw.drop 112).take 16=cell07.val := by
  simp only [raw,JFz_Scan54.data,JFz_Scan54.j00,JFz_Scan54.j01,JFz_Scan54.j02,JFz_Scan54.j03,JFz_Scan54.j04,JFz_Scan54.j05,JFz_Scan54.j06,JFz_Scan54.j07,JFz_Scan54.j08,JFz_Scan54.j09,JFz_Scan54.j10,JFz_Scan54.j11,JFz_Scan54.j12,JFz_Scan54.b00_length,JFz_Scan54.b01_length,JFz_Scan54.b02_length,JFz_Scan54.b03_length,JFz_Scan54.b04_length,JFz_Scan54.b05_length,JFz_Scan54.b06_length,JFz_Scan54.b07_length,JFz_Scan54.b08_length,JFz_Scan54.b09_length,JFz_Scan54.b10_length,JFz_Scan54.b11_length,JFz_Scan54.b12_length,JFz_Scan54.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell07
theorem encoded07 : CandidateParserByteOrder.arrayBytes16 cell07=encodeQM31LE limbs07 := by
  funext i
  fin_cases i <;> rfl
theorem parser07 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell07)=
    ok (some ⟨⟨321012999#u32,2102018036#u32⟩,⟨1640112941#u32,700805713#u32⟩⟩) :=
  JFr_EncodedCell.parser cell07 limbs07 encoded07
#print axioms encoded07
#print axioms parser07
def cell08 : Array U8 16#usize := ⟨[182#u8,195#u8,205#u8,17#u8,202#u8,165#u8,16#u8,58#u8,195#u8,198#u8,92#u8,79#u8,241#u8,134#u8,141#u8,109#u8],by rfl⟩
def limbs08 : QM31Limbs := ![⟨298697654,by change 298697654<2147483647;omega⟩,⟨974169546,by change 974169546<2147483647;omega⟩,⟨1331480259,by change 1331480259<2147483647;omega⟩,⟨1837991665,by change 1837991665<2147483647;omega⟩]
theorem rawCell08 : (raw.drop 128).take 16=cell08.val := by
  simp only [raw,JFz_Scan54.data,JFz_Scan54.j00,JFz_Scan54.j01,JFz_Scan54.j02,JFz_Scan54.j03,JFz_Scan54.j04,JFz_Scan54.j05,JFz_Scan54.j06,JFz_Scan54.j07,JFz_Scan54.j08,JFz_Scan54.j09,JFz_Scan54.j10,JFz_Scan54.j11,JFz_Scan54.j12,JFz_Scan54.b00_length,JFz_Scan54.b01_length,JFz_Scan54.b02_length,JFz_Scan54.b03_length,JFz_Scan54.b04_length,JFz_Scan54.b05_length,JFz_Scan54.b06_length,JFz_Scan54.b07_length,JFz_Scan54.b08_length,JFz_Scan54.b09_length,JFz_Scan54.b10_length,JFz_Scan54.b11_length,JFz_Scan54.b12_length,JFz_Scan54.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell08
theorem encoded08 : CandidateParserByteOrder.arrayBytes16 cell08=encodeQM31LE limbs08 := by
  funext i
  fin_cases i <;> rfl
theorem parser08 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell08)=
    ok (some ⟨⟨298697654#u32,974169546#u32⟩,⟨1331480259#u32,1837991665#u32⟩⟩) :=
  JFr_EncodedCell.parser cell08 limbs08 encoded08
#print axioms encoded08
#print axioms parser08
def cell09 : Array U8 16#usize := ⟨[153#u8,72#u8,116#u8,14#u8,225#u8,235#u8,75#u8,117#u8,0#u8,83#u8,173#u8,60#u8,173#u8,124#u8,178#u8,101#u8],by rfl⟩
def limbs09 : QM31Limbs := ![⟨242501785,by change 242501785<2147483647;omega⟩,⟨1967909857,by change 1967909857<2147483647;omega⟩,⟨1017991936,by change 1017991936<2147483647;omega⟩,⟨1706196141,by change 1706196141<2147483647;omega⟩]
theorem rawCell09 : (raw.drop 144).take 16=cell09.val := by
  simp only [raw,JFz_Scan54.data,JFz_Scan54.j00,JFz_Scan54.j01,JFz_Scan54.j02,JFz_Scan54.j03,JFz_Scan54.j04,JFz_Scan54.j05,JFz_Scan54.j06,JFz_Scan54.j07,JFz_Scan54.j08,JFz_Scan54.j09,JFz_Scan54.j10,JFz_Scan54.j11,JFz_Scan54.j12,JFz_Scan54.b00_length,JFz_Scan54.b01_length,JFz_Scan54.b02_length,JFz_Scan54.b03_length,JFz_Scan54.b04_length,JFz_Scan54.b05_length,JFz_Scan54.b06_length,JFz_Scan54.b07_length,JFz_Scan54.b08_length,JFz_Scan54.b09_length,JFz_Scan54.b10_length,JFz_Scan54.b11_length,JFz_Scan54.b12_length,JFz_Scan54.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell09
theorem encoded09 : CandidateParserByteOrder.arrayBytes16 cell09=encodeQM31LE limbs09 := by
  funext i
  fin_cases i <;> rfl
theorem parser09 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell09)=
    ok (some ⟨⟨242501785#u32,1967909857#u32⟩,⟨1017991936#u32,1706196141#u32⟩⟩) :=
  JFr_EncodedCell.parser cell09 limbs09 encoded09
#print axioms encoded09
#print axioms parser09
def cell10 : Array U8 16#usize := ⟨[111#u8,48#u8,157#u8,43#u8,236#u8,61#u8,233#u8,71#u8,173#u8,212#u8,167#u8,123#u8,146#u8,242#u8,145#u8,75#u8],by rfl⟩
def limbs10 : QM31Limbs := ![⟨731721839,by change 731721839<2147483647;omega⟩,⟨1206468076,by change 1206468076<2147483647;omega⟩,⟨2074596525,by change 2074596525<2147483647;omega⟩,⟨1267856018,by change 1267856018<2147483647;omega⟩]
theorem rawCell10 : (raw.drop 160).take 16=cell10.val := by
  simp only [raw,JFz_Scan54.data,JFz_Scan54.j00,JFz_Scan54.j01,JFz_Scan54.j02,JFz_Scan54.j03,JFz_Scan54.j04,JFz_Scan54.j05,JFz_Scan54.j06,JFz_Scan54.j07,JFz_Scan54.j08,JFz_Scan54.j09,JFz_Scan54.j10,JFz_Scan54.j11,JFz_Scan54.j12,JFz_Scan54.b00_length,JFz_Scan54.b01_length,JFz_Scan54.b02_length,JFz_Scan54.b03_length,JFz_Scan54.b04_length,JFz_Scan54.b05_length,JFz_Scan54.b06_length,JFz_Scan54.b07_length,JFz_Scan54.b08_length,JFz_Scan54.b09_length,JFz_Scan54.b10_length,JFz_Scan54.b11_length,JFz_Scan54.b12_length,JFz_Scan54.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell10
theorem encoded10 : CandidateParserByteOrder.arrayBytes16 cell10=encodeQM31LE limbs10 := by
  funext i
  fin_cases i <;> rfl
theorem parser10 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell10)=
    ok (some ⟨⟨731721839#u32,1206468076#u32⟩,⟨2074596525#u32,1267856018#u32⟩⟩) :=
  JFr_EncodedCell.parser cell10 limbs10 encoded10
#print axioms encoded10
#print axioms parser10
def cell11 : Array U8 16#usize := ⟨[122#u8,234#u8,159#u8,48#u8,160#u8,28#u8,3#u8,83#u8,101#u8,252#u8,111#u8,37#u8,29#u8,36#u8,238#u8,65#u8],by rfl⟩
def limbs11 : QM31Limbs := ![⟨815786618,by change 815786618<2147483647;omega⟩,⟨1392712864,by change 1392712864<2147483647;omega⟩,⟨628096101,by change 628096101<2147483647;omega⟩,⟨1106125853,by change 1106125853<2147483647;omega⟩]
theorem rawCell11 : (raw.drop 176).take 16=cell11.val := by
  simp only [raw,JFz_Scan54.data,JFz_Scan54.j00,JFz_Scan54.j01,JFz_Scan54.j02,JFz_Scan54.j03,JFz_Scan54.j04,JFz_Scan54.j05,JFz_Scan54.j06,JFz_Scan54.j07,JFz_Scan54.j08,JFz_Scan54.j09,JFz_Scan54.j10,JFz_Scan54.j11,JFz_Scan54.j12,JFz_Scan54.b00_length,JFz_Scan54.b01_length,JFz_Scan54.b02_length,JFz_Scan54.b03_length,JFz_Scan54.b04_length,JFz_Scan54.b05_length,JFz_Scan54.b06_length,JFz_Scan54.b07_length,JFz_Scan54.b08_length,JFz_Scan54.b09_length,JFz_Scan54.b10_length,JFz_Scan54.b11_length,JFz_Scan54.b12_length,JFz_Scan54.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell11
theorem encoded11 : CandidateParserByteOrder.arrayBytes16 cell11=encodeQM31LE limbs11 := by
  funext i
  fin_cases i <;> rfl
theorem parser11 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell11)=
    ok (some ⟨⟨815786618#u32,1392712864#u32⟩,⟨628096101#u32,1106125853#u32⟩⟩) :=
  JFr_EncodedCell.parser cell11 limbs11 encoded11
#print axioms encoded11
#print axioms parser11
def cell12 : Array U8 16#usize := ⟨[107#u8,96#u8,77#u8,28#u8,117#u8,194#u8,192#u8,38#u8,207#u8,153#u8,123#u8,58#u8,120#u8,76#u8,93#u8,105#u8],by rfl⟩
def limbs12 : QM31Limbs := ![⟨474833003,by change 474833003<2147483647;omega⟩,⟨650166901,by change 650166901<2147483647;omega⟩,⟨981178831,by change 981178831<2147483647;omega⟩,⟨1767722104,by change 1767722104<2147483647;omega⟩]
theorem rawCell12 : (raw.drop 192).take 16=cell12.val := by
  simp only [raw,JFz_Scan54.data,JFz_Scan54.j00,JFz_Scan54.j01,JFz_Scan54.j02,JFz_Scan54.j03,JFz_Scan54.j04,JFz_Scan54.j05,JFz_Scan54.j06,JFz_Scan54.j07,JFz_Scan54.j08,JFz_Scan54.j09,JFz_Scan54.j10,JFz_Scan54.j11,JFz_Scan54.j12,JFz_Scan54.b00_length,JFz_Scan54.b01_length,JFz_Scan54.b02_length,JFz_Scan54.b03_length,JFz_Scan54.b04_length,JFz_Scan54.b05_length,JFz_Scan54.b06_length,JFz_Scan54.b07_length,JFz_Scan54.b08_length,JFz_Scan54.b09_length,JFz_Scan54.b10_length,JFz_Scan54.b11_length,JFz_Scan54.b12_length,JFz_Scan54.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell12
theorem encoded12 : CandidateParserByteOrder.arrayBytes16 cell12=encodeQM31LE limbs12 := by
  funext i
  fin_cases i <;> rfl
theorem parser12 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell12)=
    ok (some ⟨⟨474833003#u32,650166901#u32⟩,⟨981178831#u32,1767722104#u32⟩⟩) :=
  JFr_EncodedCell.parser cell12 limbs12 encoded12
#print axioms encoded12
#print axioms parser12
def cell13 : Array U8 16#usize := ⟨[77#u8,191#u8,173#u8,39#u8,212#u8,214#u8,216#u8,29#u8,132#u8,150#u8,90#u8,101#u8,8#u8,55#u8,60#u8,9#u8],by rfl⟩
def limbs13 : QM31Limbs := ![⟨665698125,by change 665698125<2147483647;omega⟩,⟨500750036,by change 500750036<2147483647;omega⟩,⟨1700435588,by change 1700435588<2147483647;omega⟩,⟨154941192,by change 154941192<2147483647;omega⟩]
theorem rawCell13 : (raw.drop 208).take 16=cell13.val := by
  simp only [raw,JFz_Scan54.data,JFz_Scan54.j00,JFz_Scan54.j01,JFz_Scan54.j02,JFz_Scan54.j03,JFz_Scan54.j04,JFz_Scan54.j05,JFz_Scan54.j06,JFz_Scan54.j07,JFz_Scan54.j08,JFz_Scan54.j09,JFz_Scan54.j10,JFz_Scan54.j11,JFz_Scan54.j12,JFz_Scan54.b00_length,JFz_Scan54.b01_length,JFz_Scan54.b02_length,JFz_Scan54.b03_length,JFz_Scan54.b04_length,JFz_Scan54.b05_length,JFz_Scan54.b06_length,JFz_Scan54.b07_length,JFz_Scan54.b08_length,JFz_Scan54.b09_length,JFz_Scan54.b10_length,JFz_Scan54.b11_length,JFz_Scan54.b12_length,JFz_Scan54.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell13
theorem encoded13 : CandidateParserByteOrder.arrayBytes16 cell13=encodeQM31LE limbs13 := by
  funext i
  fin_cases i <;> rfl
theorem parser13 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell13)=
    ok (some ⟨⟨665698125#u32,500750036#u32⟩,⟨1700435588#u32,154941192#u32⟩⟩) :=
  JFr_EncodedCell.parser cell13 limbs13 encoded13
#print axioms encoded13
#print axioms parser13
def cell14 : Array U8 16#usize := ⟨[52#u8,34#u8,139#u8,70#u8,210#u8,247#u8,55#u8,109#u8,213#u8,36#u8,183#u8,70#u8,85#u8,3#u8,24#u8,116#u8],by rfl⟩
def limbs14 : QM31Limbs := ![⟨1183523380,by change 1183523380<2147483647;omega⟩,⟨1832384466,by change 1832384466<2147483647;omega⟩,⟨1186407637,by change 1186407637<2147483647;omega⟩,⟨1947730773,by change 1947730773<2147483647;omega⟩]
theorem rawCell14 : (raw.drop 224).take 16=cell14.val := by
  simp only [raw,JFz_Scan54.data,JFz_Scan54.j00,JFz_Scan54.j01,JFz_Scan54.j02,JFz_Scan54.j03,JFz_Scan54.j04,JFz_Scan54.j05,JFz_Scan54.j06,JFz_Scan54.j07,JFz_Scan54.j08,JFz_Scan54.j09,JFz_Scan54.j10,JFz_Scan54.j11,JFz_Scan54.j12,JFz_Scan54.b00_length,JFz_Scan54.b01_length,JFz_Scan54.b02_length,JFz_Scan54.b03_length,JFz_Scan54.b04_length,JFz_Scan54.b05_length,JFz_Scan54.b06_length,JFz_Scan54.b07_length,JFz_Scan54.b08_length,JFz_Scan54.b09_length,JFz_Scan54.b10_length,JFz_Scan54.b11_length,JFz_Scan54.b12_length,JFz_Scan54.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell14
theorem encoded14 : CandidateParserByteOrder.arrayBytes16 cell14=encodeQM31LE limbs14 := by
  funext i
  fin_cases i <;> rfl
theorem parser14 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell14)=
    ok (some ⟨⟨1183523380#u32,1832384466#u32⟩,⟨1186407637#u32,1947730773#u32⟩⟩) :=
  JFr_EncodedCell.parser cell14 limbs14 encoded14
#print axioms encoded14
#print axioms parser14
def cell15 : Array U8 16#usize := ⟨[252#u8,193#u8,102#u8,31#u8,151#u8,6#u8,20#u8,1#u8,222#u8,186#u8,39#u8,25#u8,1#u8,120#u8,105#u8,97#u8],by rfl⟩
def limbs15 : QM31Limbs := ![⟨526828028,by change 526828028<2147483647;omega⟩,⟨18089623,by change 18089623<2147483647;omega⟩,⟨422034142,by change 422034142<2147483647;omega⟩,⟨1634301953,by change 1634301953<2147483647;omega⟩]
theorem rawCell15 : (raw.drop 240).take 16=cell15.val := by
  simp only [raw,JFz_Scan54.data,JFz_Scan54.j00,JFz_Scan54.j01,JFz_Scan54.j02,JFz_Scan54.j03,JFz_Scan54.j04,JFz_Scan54.j05,JFz_Scan54.j06,JFz_Scan54.j07,JFz_Scan54.j08,JFz_Scan54.j09,JFz_Scan54.j10,JFz_Scan54.j11,JFz_Scan54.j12,JFz_Scan54.b00_length,JFz_Scan54.b01_length,JFz_Scan54.b02_length,JFz_Scan54.b03_length,JFz_Scan54.b04_length,JFz_Scan54.b05_length,JFz_Scan54.b06_length,JFz_Scan54.b07_length,JFz_Scan54.b08_length,JFz_Scan54.b09_length,JFz_Scan54.b10_length,JFz_Scan54.b11_length,JFz_Scan54.b12_length,JFz_Scan54.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell15
theorem encoded15 : CandidateParserByteOrder.arrayBytes16 cell15=encodeQM31LE limbs15 := by
  funext i
  fin_cases i <;> rfl
theorem parser15 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell15)=
    ok (some ⟨⟨526828028#u32,18089623#u32⟩,⟨422034142#u32,1634301953#u32⟩⟩) :=
  JFr_EncodedCell.parser cell15 limbs15 encoded15
#print axioms encoded15
#print axioms parser15
def cell16 : Array U8 16#usize := ⟨[0#u8,105#u8,98#u8,58#u8,99#u8,123#u8,119#u8,94#u8,179#u8,87#u8,196#u8,109#u8,62#u8,170#u8,70#u8,75#u8],by rfl⟩
def limbs16 : QM31Limbs := ![⟨979527936,by change 979527936<2147483647;omega⟩,⟨1584888675,by change 1584888675<2147483647;omega⟩,⟨1841584051,by change 1841584051<2147483647;omega⟩,⟨1262922302,by change 1262922302<2147483647;omega⟩]
theorem rawCell16 : (raw.drop 256).take 16=cell16.val := by
  simp only [raw,JFz_Scan54.data,JFz_Scan54.j00,JFz_Scan54.j01,JFz_Scan54.j02,JFz_Scan54.j03,JFz_Scan54.j04,JFz_Scan54.j05,JFz_Scan54.j06,JFz_Scan54.j07,JFz_Scan54.j08,JFz_Scan54.j09,JFz_Scan54.j10,JFz_Scan54.j11,JFz_Scan54.j12,JFz_Scan54.b00_length,JFz_Scan54.b01_length,JFz_Scan54.b02_length,JFz_Scan54.b03_length,JFz_Scan54.b04_length,JFz_Scan54.b05_length,JFz_Scan54.b06_length,JFz_Scan54.b07_length,JFz_Scan54.b08_length,JFz_Scan54.b09_length,JFz_Scan54.b10_length,JFz_Scan54.b11_length,JFz_Scan54.b12_length,JFz_Scan54.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell16
theorem encoded16 : CandidateParserByteOrder.arrayBytes16 cell16=encodeQM31LE limbs16 := by
  funext i
  fin_cases i <;> rfl
theorem parser16 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell16)=
    ok (some ⟨⟨979527936#u32,1584888675#u32⟩,⟨1841584051#u32,1262922302#u32⟩⟩) :=
  JFr_EncodedCell.parser cell16 limbs16 encoded16
#print axioms encoded16
#print axioms parser16
def cell17 : Array U8 16#usize := ⟨[195#u8,160#u8,208#u8,76#u8,81#u8,31#u8,50#u8,107#u8,163#u8,161#u8,168#u8,119#u8,25#u8,89#u8,2#u8,82#u8],by rfl⟩
def limbs17 : QM31Limbs := ![⟨1288741059,by change 1288741059<2147483647;omega⟩,⟨1798446929,by change 1798446929<2147483647;omega⟩,⟨2007540131,by change 2007540131<2147483647;omega⟩,⟨1375885593,by change 1375885593<2147483647;omega⟩]
theorem rawCell17 : (raw.drop 272).take 16=cell17.val := by
  simp only [raw,JFz_Scan54.data,JFz_Scan54.j00,JFz_Scan54.j01,JFz_Scan54.j02,JFz_Scan54.j03,JFz_Scan54.j04,JFz_Scan54.j05,JFz_Scan54.j06,JFz_Scan54.j07,JFz_Scan54.j08,JFz_Scan54.j09,JFz_Scan54.j10,JFz_Scan54.j11,JFz_Scan54.j12,JFz_Scan54.b00_length,JFz_Scan54.b01_length,JFz_Scan54.b02_length,JFz_Scan54.b03_length,JFz_Scan54.b04_length,JFz_Scan54.b05_length,JFz_Scan54.b06_length,JFz_Scan54.b07_length,JFz_Scan54.b08_length,JFz_Scan54.b09_length,JFz_Scan54.b10_length,JFz_Scan54.b11_length,JFz_Scan54.b12_length,JFz_Scan54.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell17
theorem encoded17 : CandidateParserByteOrder.arrayBytes16 cell17=encodeQM31LE limbs17 := by
  funext i
  fin_cases i <;> rfl
theorem parser17 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell17)=
    ok (some ⟨⟨1288741059#u32,1798446929#u32⟩,⟨2007540131#u32,1375885593#u32⟩⟩) :=
  JFr_EncodedCell.parser cell17 limbs17 encoded17
#print axioms encoded17
#print axioms parser17
def cell18 : Array U8 16#usize := ⟨[230#u8,40#u8,93#u8,103#u8,233#u8,201#u8,65#u8,92#u8,110#u8,133#u8,204#u8,15#u8,23#u8,123#u8,210#u8,90#u8],by rfl⟩
def limbs18 : QM31Limbs := ![⟨1734158566,by change 1734158566<2147483647;omega⟩,⟨1547815401,by change 1547815401<2147483647;omega⟩,⟨265061742,by change 265061742<2147483647;omega⟩,⟨1523743511,by change 1523743511<2147483647;omega⟩]
theorem rawCell18 : (raw.drop 288).take 16=cell18.val := by
  simp only [raw,JFz_Scan54.data,JFz_Scan54.j00,JFz_Scan54.j01,JFz_Scan54.j02,JFz_Scan54.j03,JFz_Scan54.j04,JFz_Scan54.j05,JFz_Scan54.j06,JFz_Scan54.j07,JFz_Scan54.j08,JFz_Scan54.j09,JFz_Scan54.j10,JFz_Scan54.j11,JFz_Scan54.j12,JFz_Scan54.b00_length,JFz_Scan54.b01_length,JFz_Scan54.b02_length,JFz_Scan54.b03_length,JFz_Scan54.b04_length,JFz_Scan54.b05_length,JFz_Scan54.b06_length,JFz_Scan54.b07_length,JFz_Scan54.b08_length,JFz_Scan54.b09_length,JFz_Scan54.b10_length,JFz_Scan54.b11_length,JFz_Scan54.b12_length,JFz_Scan54.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell18
theorem encoded18 : CandidateParserByteOrder.arrayBytes16 cell18=encodeQM31LE limbs18 := by
  funext i
  fin_cases i <;> rfl
theorem parser18 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell18)=
    ok (some ⟨⟨1734158566#u32,1547815401#u32⟩,⟨265061742#u32,1523743511#u32⟩⟩) :=
  JFr_EncodedCell.parser cell18 limbs18 encoded18
#print axioms encoded18
#print axioms parser18
def cell19 : Array U8 16#usize := ⟨[112#u8,9#u8,36#u8,19#u8,81#u8,87#u8,76#u8,51#u8,82#u8,254#u8,202#u8,12#u8,80#u8,20#u8,64#u8,73#u8],by rfl⟩
def limbs19 : QM31Limbs := ![⟨321128816,by change 321128816<2147483647;omega⟩,⟨860641105,by change 860641105<2147483647;omega⟩,⟨214629970,by change 214629970<2147483647;omega⟩,⟨1228936272,by change 1228936272<2147483647;omega⟩]
theorem rawCell19 : (raw.drop 304).take 16=cell19.val := by
  simp only [raw,JFz_Scan54.data,JFz_Scan54.j00,JFz_Scan54.j01,JFz_Scan54.j02,JFz_Scan54.j03,JFz_Scan54.j04,JFz_Scan54.j05,JFz_Scan54.j06,JFz_Scan54.j07,JFz_Scan54.j08,JFz_Scan54.j09,JFz_Scan54.j10,JFz_Scan54.j11,JFz_Scan54.j12,JFz_Scan54.b00_length,JFz_Scan54.b01_length,JFz_Scan54.b02_length,JFz_Scan54.b03_length,JFz_Scan54.b04_length,JFz_Scan54.b05_length,JFz_Scan54.b06_length,JFz_Scan54.b07_length,JFz_Scan54.b08_length,JFz_Scan54.b09_length,JFz_Scan54.b10_length,JFz_Scan54.b11_length,JFz_Scan54.b12_length,JFz_Scan54.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell19
theorem encoded19 : CandidateParserByteOrder.arrayBytes16 cell19=encodeQM31LE limbs19 := by
  funext i
  fin_cases i <;> rfl
theorem parser19 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell19)=
    ok (some ⟨⟨321128816#u32,860641105#u32⟩,⟨214629970#u32,1228936272#u32⟩⟩) :=
  JFr_EncodedCell.parser cell19 limbs19 encoded19
#print axioms encoded19
#print axioms parser19
def cell20 : Array U8 16#usize := ⟨[62#u8,254#u8,209#u8,62#u8,242#u8,49#u8,86#u8,34#u8,236#u8,178#u8,255#u8,78#u8,154#u8,119#u8,0#u8,25#u8],by rfl⟩
def limbs20 : QM31Limbs := ![⟨1053949502,by change 1053949502<2147483647;omega⟩,⟨576074226,by change 576074226<2147483647;omega⟩,⟨1325380332,by change 1325380332<2147483647;omega⟩,⟨419461018,by change 419461018<2147483647;omega⟩]
theorem rawCell20 : (raw.drop 320).take 16=cell20.val := by
  simp only [raw,JFz_Scan54.data,JFz_Scan54.j00,JFz_Scan54.j01,JFz_Scan54.j02,JFz_Scan54.j03,JFz_Scan54.j04,JFz_Scan54.j05,JFz_Scan54.j06,JFz_Scan54.j07,JFz_Scan54.j08,JFz_Scan54.j09,JFz_Scan54.j10,JFz_Scan54.j11,JFz_Scan54.j12,JFz_Scan54.b00_length,JFz_Scan54.b01_length,JFz_Scan54.b02_length,JFz_Scan54.b03_length,JFz_Scan54.b04_length,JFz_Scan54.b05_length,JFz_Scan54.b06_length,JFz_Scan54.b07_length,JFz_Scan54.b08_length,JFz_Scan54.b09_length,JFz_Scan54.b10_length,JFz_Scan54.b11_length,JFz_Scan54.b12_length,JFz_Scan54.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell20
theorem encoded20 : CandidateParserByteOrder.arrayBytes16 cell20=encodeQM31LE limbs20 := by
  funext i
  fin_cases i <;> rfl
theorem parser20 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell20)=
    ok (some ⟨⟨1053949502#u32,576074226#u32⟩,⟨1325380332#u32,419461018#u32⟩⟩) :=
  JFr_EncodedCell.parser cell20 limbs20 encoded20
#print axioms encoded20
#print axioms parser20
def cell21 : Array U8 16#usize := ⟨[245#u8,112#u8,203#u8,112#u8,210#u8,144#u8,110#u8,72#u8,209#u8,64#u8,225#u8,85#u8,142#u8,159#u8,27#u8,43#u8],by rfl⟩
def limbs21 : QM31Limbs := ![⟨1892380917,by change 1892380917<2147483647;omega⟩,⟨1215205586,by change 1215205586<2147483647;omega⟩,⟨1440825553,by change 1440825553<2147483647;omega⟩,⟨723230606,by change 723230606<2147483647;omega⟩]
theorem rawCell21 : (raw.drop 336).take 16=cell21.val := by
  simp only [raw,JFz_Scan54.data,JFz_Scan54.j00,JFz_Scan54.j01,JFz_Scan54.j02,JFz_Scan54.j03,JFz_Scan54.j04,JFz_Scan54.j05,JFz_Scan54.j06,JFz_Scan54.j07,JFz_Scan54.j08,JFz_Scan54.j09,JFz_Scan54.j10,JFz_Scan54.j11,JFz_Scan54.j12,JFz_Scan54.b00_length,JFz_Scan54.b01_length,JFz_Scan54.b02_length,JFz_Scan54.b03_length,JFz_Scan54.b04_length,JFz_Scan54.b05_length,JFz_Scan54.b06_length,JFz_Scan54.b07_length,JFz_Scan54.b08_length,JFz_Scan54.b09_length,JFz_Scan54.b10_length,JFz_Scan54.b11_length,JFz_Scan54.b12_length,JFz_Scan54.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell21
theorem encoded21 : CandidateParserByteOrder.arrayBytes16 cell21=encodeQM31LE limbs21 := by
  funext i
  fin_cases i <;> rfl
theorem parser21 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell21)=
    ok (some ⟨⟨1892380917#u32,1215205586#u32⟩,⟨1440825553#u32,723230606#u32⟩⟩) :=
  JFr_EncodedCell.parser cell21 limbs21 encoded21
#print axioms encoded21
#print axioms parser21
def cell22 : Array U8 16#usize := ⟨[138#u8,221#u8,115#u8,114#u8,144#u8,232#u8,202#u8,124#u8,93#u8,76#u8,64#u8,60#u8,27#u8,72#u8,217#u8,120#u8],by rfl⟩
def limbs22 : QM31Limbs := ![⟨1920195978,by change 1920195978<2147483647;omega⟩,⟨2093672592,by change 2093672592<2147483647;omega⟩,⟨1010846813,by change 1010846813<2147483647;omega⟩,⟨2027505691,by change 2027505691<2147483647;omega⟩]
theorem rawCell22 : (raw.drop 352).take 16=cell22.val := by
  simp only [raw,JFz_Scan54.data,JFz_Scan54.j00,JFz_Scan54.j01,JFz_Scan54.j02,JFz_Scan54.j03,JFz_Scan54.j04,JFz_Scan54.j05,JFz_Scan54.j06,JFz_Scan54.j07,JFz_Scan54.j08,JFz_Scan54.j09,JFz_Scan54.j10,JFz_Scan54.j11,JFz_Scan54.j12,JFz_Scan54.b00_length,JFz_Scan54.b01_length,JFz_Scan54.b02_length,JFz_Scan54.b03_length,JFz_Scan54.b04_length,JFz_Scan54.b05_length,JFz_Scan54.b06_length,JFz_Scan54.b07_length,JFz_Scan54.b08_length,JFz_Scan54.b09_length,JFz_Scan54.b10_length,JFz_Scan54.b11_length,JFz_Scan54.b12_length,JFz_Scan54.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell22
theorem encoded22 : CandidateParserByteOrder.arrayBytes16 cell22=encodeQM31LE limbs22 := by
  funext i
  fin_cases i <;> rfl
theorem parser22 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell22)=
    ok (some ⟨⟨1920195978#u32,2093672592#u32⟩,⟨1010846813#u32,2027505691#u32⟩⟩) :=
  JFr_EncodedCell.parser cell22 limbs22 encoded22
#print axioms encoded22
#print axioms parser22
def cell23 : Array U8 16#usize := ⟨[206#u8,231#u8,122#u8,94#u8,201#u8,163#u8,17#u8,46#u8,87#u8,101#u8,243#u8,9#u8,51#u8,247#u8,132#u8,18#u8],by rfl⟩
def limbs23 : QM31Limbs := ![⟨1585113038,by change 1585113038<2147483647;omega⟩,⟨772907977,by change 772907977<2147483647;omega⟩,⟨166946135,by change 166946135<2147483647;omega⟩,⟨310703923,by change 310703923<2147483647;omega⟩]
theorem rawCell23 : (raw.drop 368).take 16=cell23.val := by
  simp only [raw,JFz_Scan54.data,JFz_Scan54.j00,JFz_Scan54.j01,JFz_Scan54.j02,JFz_Scan54.j03,JFz_Scan54.j04,JFz_Scan54.j05,JFz_Scan54.j06,JFz_Scan54.j07,JFz_Scan54.j08,JFz_Scan54.j09,JFz_Scan54.j10,JFz_Scan54.j11,JFz_Scan54.j12,JFz_Scan54.b00_length,JFz_Scan54.b01_length,JFz_Scan54.b02_length,JFz_Scan54.b03_length,JFz_Scan54.b04_length,JFz_Scan54.b05_length,JFz_Scan54.b06_length,JFz_Scan54.b07_length,JFz_Scan54.b08_length,JFz_Scan54.b09_length,JFz_Scan54.b10_length,JFz_Scan54.b11_length,JFz_Scan54.b12_length,JFz_Scan54.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell23
theorem encoded23 : CandidateParserByteOrder.arrayBytes16 cell23=encodeQM31LE limbs23 := by
  funext i
  fin_cases i <;> rfl
theorem parser23 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell23)=
    ok (some ⟨⟨1585113038#u32,772907977#u32⟩,⟨166946135#u32,310703923#u32⟩⟩) :=
  JFr_EncodedCell.parser cell23 limbs23 encoded23
#print axioms encoded23
#print axioms parser23
def cell24 : Array U8 16#usize := ⟨[176#u8,209#u8,188#u8,30#u8,198#u8,220#u8,161#u8,27#u8,82#u8,140#u8,155#u8,111#u8,160#u8,79#u8,21#u8,106#u8],by rfl⟩
def limbs24 : QM31Limbs := ![⟨515690928,by change 515690928<2147483647;omega⟩,⟨463592646,by change 463592646<2147483647;omega⟩,⟨1872464978,by change 1872464978<2147483647;omega⟩,⟨1779781536,by change 1779781536<2147483647;omega⟩]
theorem rawCell24 : (raw.drop 384).take 16=cell24.val := by
  simp only [raw,JFz_Scan54.data,JFz_Scan54.j00,JFz_Scan54.j01,JFz_Scan54.j02,JFz_Scan54.j03,JFz_Scan54.j04,JFz_Scan54.j05,JFz_Scan54.j06,JFz_Scan54.j07,JFz_Scan54.j08,JFz_Scan54.j09,JFz_Scan54.j10,JFz_Scan54.j11,JFz_Scan54.j12,JFz_Scan54.b00_length,JFz_Scan54.b01_length,JFz_Scan54.b02_length,JFz_Scan54.b03_length,JFz_Scan54.b04_length,JFz_Scan54.b05_length,JFz_Scan54.b06_length,JFz_Scan54.b07_length,JFz_Scan54.b08_length,JFz_Scan54.b09_length,JFz_Scan54.b10_length,JFz_Scan54.b11_length,JFz_Scan54.b12_length,JFz_Scan54.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell24
theorem encoded24 : CandidateParserByteOrder.arrayBytes16 cell24=encodeQM31LE limbs24 := by
  funext i
  fin_cases i <;> rfl
theorem parser24 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell24)=
    ok (some ⟨⟨515690928#u32,463592646#u32⟩,⟨1872464978#u32,1779781536#u32⟩⟩) :=
  JFr_EncodedCell.parser cell24 limbs24 encoded24
#print axioms encoded24
#print axioms parser24
def cell25 : Array U8 16#usize := ⟨[27#u8,129#u8,117#u8,16#u8,22#u8,239#u8,232#u8,47#u8,166#u8,183#u8,247#u8,25#u8,158#u8,223#u8,32#u8,107#u8],by rfl⟩
def limbs25 : QM31Limbs := ![⟨276136219,by change 276136219<2147483647;omega⟩,⟨803794710,by change 803794710<2147483647;omega⟩,⟨435664806,by change 435664806<2147483647;omega⟩,⟨1797316510,by change 1797316510<2147483647;omega⟩]
theorem rawCell25 : (raw.drop 400).take 16=cell25.val := by
  simp only [raw,JFz_Scan54.data,JFz_Scan54.j00,JFz_Scan54.j01,JFz_Scan54.j02,JFz_Scan54.j03,JFz_Scan54.j04,JFz_Scan54.j05,JFz_Scan54.j06,JFz_Scan54.j07,JFz_Scan54.j08,JFz_Scan54.j09,JFz_Scan54.j10,JFz_Scan54.j11,JFz_Scan54.j12,JFz_Scan54.b00_length,JFz_Scan54.b01_length,JFz_Scan54.b02_length,JFz_Scan54.b03_length,JFz_Scan54.b04_length,JFz_Scan54.b05_length,JFz_Scan54.b06_length,JFz_Scan54.b07_length,JFz_Scan54.b08_length,JFz_Scan54.b09_length,JFz_Scan54.b10_length,JFz_Scan54.b11_length,JFz_Scan54.b12_length,JFz_Scan54.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell25
theorem encoded25 : CandidateParserByteOrder.arrayBytes16 cell25=encodeQM31LE limbs25 := by
  funext i
  fin_cases i <;> rfl
theorem parser25 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell25)=
    ok (some ⟨⟨276136219#u32,803794710#u32⟩,⟨435664806#u32,1797316510#u32⟩⟩) :=
  JFr_EncodedCell.parser cell25 limbs25 encoded25
#print axioms encoded25
#print axioms parser25
def cell26 : Array U8 16#usize := ⟨[173#u8,245#u8,218#u8,71#u8,132#u8,40#u8,24#u8,98#u8,1#u8,168#u8,197#u8,103#u8,192#u8,222#u8,204#u8,53#u8],by rfl⟩
def limbs26 : QM31Limbs := ![⟨1205532077,by change 1205532077<2147483647;omega⟩,⟨1645750404,by change 1645750404<2147483647;omega⟩,⟨1741006849,by change 1741006849<2147483647;omega⟩,⟨902618816,by change 902618816<2147483647;omega⟩]
theorem rawCell26 : (raw.drop 416).take 16=cell26.val := by
  simp only [raw,JFz_Scan54.data,JFz_Scan54.j00,JFz_Scan54.j01,JFz_Scan54.j02,JFz_Scan54.j03,JFz_Scan54.j04,JFz_Scan54.j05,JFz_Scan54.j06,JFz_Scan54.j07,JFz_Scan54.j08,JFz_Scan54.j09,JFz_Scan54.j10,JFz_Scan54.j11,JFz_Scan54.j12,JFz_Scan54.b00_length,JFz_Scan54.b01_length,JFz_Scan54.b02_length,JFz_Scan54.b03_length,JFz_Scan54.b04_length,JFz_Scan54.b05_length,JFz_Scan54.b06_length,JFz_Scan54.b07_length,JFz_Scan54.b08_length,JFz_Scan54.b09_length,JFz_Scan54.b10_length,JFz_Scan54.b11_length,JFz_Scan54.b12_length,JFz_Scan54.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell26
theorem encoded26 : CandidateParserByteOrder.arrayBytes16 cell26=encodeQM31LE limbs26 := by
  funext i
  fin_cases i <;> rfl
theorem parser26 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell26)=
    ok (some ⟨⟨1205532077#u32,1645750404#u32⟩,⟨1741006849#u32,902618816#u32⟩⟩) :=
  JFr_EncodedCell.parser cell26 limbs26 encoded26
#print axioms encoded26
#print axioms parser26
def cell27 : Array U8 16#usize := ⟨[233#u8,57#u8,173#u8,11#u8,191#u8,178#u8,191#u8,118#u8,180#u8,41#u8,171#u8,22#u8,199#u8,151#u8,185#u8,14#u8],by rfl⟩
def limbs27 : QM31Limbs := ![⟨195901929,by change 195901929<2147483647;omega⟩,⟨1992274623,by change 1992274623<2147483647;omega⟩,⟨380316084,by change 380316084<2147483647;omega⟩,⟨247044039,by change 247044039<2147483647;omega⟩]
theorem rawCell27 : (raw.drop 432).take 16=cell27.val := by
  simp only [raw,JFz_Scan54.data,JFz_Scan54.j00,JFz_Scan54.j01,JFz_Scan54.j02,JFz_Scan54.j03,JFz_Scan54.j04,JFz_Scan54.j05,JFz_Scan54.j06,JFz_Scan54.j07,JFz_Scan54.j08,JFz_Scan54.j09,JFz_Scan54.j10,JFz_Scan54.j11,JFz_Scan54.j12,JFz_Scan54.b00_length,JFz_Scan54.b01_length,JFz_Scan54.b02_length,JFz_Scan54.b03_length,JFz_Scan54.b04_length,JFz_Scan54.b05_length,JFz_Scan54.b06_length,JFz_Scan54.b07_length,JFz_Scan54.b08_length,JFz_Scan54.b09_length,JFz_Scan54.b10_length,JFz_Scan54.b11_length,JFz_Scan54.b12_length,JFz_Scan54.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell27
theorem encoded27 : CandidateParserByteOrder.arrayBytes16 cell27=encodeQM31LE limbs27 := by
  funext i
  fin_cases i <;> rfl
theorem parser27 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell27)=
    ok (some ⟨⟨195901929#u32,1992274623#u32⟩,⟨380316084#u32,247044039#u32⟩⟩) :=
  JFr_EncodedCell.parser cell27 limbs27 encoded27
#print axioms encoded27
#print axioms parser27
end AspisR1.JFr_Bytes06
