import NDO_JFr_Data00
import NDO_JFr_EncodedCell
import NDO_JFz_Scan48
set_option autoImplicit false
namespace AspisR1.JFr_Bytes00
open Aeneas Aeneas.Std Result RetainedFieldByteCodec
open AspisR1PublicPreparation
open AspisS1ExtractedRoundChildren
def raw : List U8 := JFz_Scan48.data
theorem rawLength : raw.length=448 := JFz_Scan48.length
#print axioms rawLength
theorem selected : (JFx_NativeBytes.proof.val.drop 176).take 448=raw := JFz_Scan48.selected
#print axioms selected
def cell00 : Array U8 16#usize := ⟨[209#u8,2#u8,233#u8,82#u8,5#u8,31#u8,179#u8,98#u8,208#u8,240#u8,20#u8,61#u8,47#u8,184#u8,147#u8,70#u8],by rfl⟩
def limbs00 : QM31Limbs := ![⟨1391002321,by change 1391002321<2147483647;omega⟩,⟨1655906053,by change 1655906053<2147483647;omega⟩,⟨1024782544,by change 1024782544<2147483647;omega⟩,⟨1184086063,by change 1184086063<2147483647;omega⟩]
theorem rawCell00 : (raw.drop 0).take 16=cell00.val := by
  simp only [raw,JFz_Scan48.data,JFz_Scan48.j00,JFz_Scan48.j01,JFz_Scan48.j02,JFz_Scan48.j03,JFz_Scan48.j04,JFz_Scan48.j05,JFz_Scan48.j06,JFz_Scan48.j07,JFz_Scan48.j08,JFz_Scan48.j09,JFz_Scan48.j10,JFz_Scan48.j11,JFz_Scan48.j12,JFz_Scan48.b00_length,JFz_Scan48.b01_length,JFz_Scan48.b02_length,JFz_Scan48.b03_length,JFz_Scan48.b04_length,JFz_Scan48.b05_length,JFz_Scan48.b06_length,JFz_Scan48.b07_length,JFz_Scan48.b08_length,JFz_Scan48.b09_length,JFz_Scan48.b10_length,JFz_Scan48.b11_length,JFz_Scan48.b12_length,JFz_Scan48.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell00
theorem encoded00 : CandidateParserByteOrder.arrayBytes16 cell00=encodeQM31LE limbs00 := by
  funext i
  fin_cases i <;> rfl
theorem parser00 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell00)=
    ok (some ⟨⟨1391002321#u32,1655906053#u32⟩,⟨1024782544#u32,1184086063#u32⟩⟩) :=
  JFr_EncodedCell.parser cell00 limbs00 encoded00
#print axioms encoded00
#print axioms parser00
def cell01 : Array U8 16#usize := ⟨[185#u8,248#u8,35#u8,90#u8,79#u8,148#u8,234#u8,50#u8,108#u8,46#u8,141#u8,39#u8,142#u8,177#u8,205#u8,37#u8],by rfl⟩
def limbs01 : QM31Limbs := ![⟨1512306873,by change 1512306873<2147483647;omega⟩,⟨854234191,by change 854234191<2147483647;omega⟩,⟨663563884,by change 663563884<2147483647;omega⟩,⟨634237326,by change 634237326<2147483647;omega⟩]
theorem rawCell01 : (raw.drop 16).take 16=cell01.val := by
  simp only [raw,JFz_Scan48.data,JFz_Scan48.j00,JFz_Scan48.j01,JFz_Scan48.j02,JFz_Scan48.j03,JFz_Scan48.j04,JFz_Scan48.j05,JFz_Scan48.j06,JFz_Scan48.j07,JFz_Scan48.j08,JFz_Scan48.j09,JFz_Scan48.j10,JFz_Scan48.j11,JFz_Scan48.j12,JFz_Scan48.b00_length,JFz_Scan48.b01_length,JFz_Scan48.b02_length,JFz_Scan48.b03_length,JFz_Scan48.b04_length,JFz_Scan48.b05_length,JFz_Scan48.b06_length,JFz_Scan48.b07_length,JFz_Scan48.b08_length,JFz_Scan48.b09_length,JFz_Scan48.b10_length,JFz_Scan48.b11_length,JFz_Scan48.b12_length,JFz_Scan48.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell01
theorem encoded01 : CandidateParserByteOrder.arrayBytes16 cell01=encodeQM31LE limbs01 := by
  funext i
  fin_cases i <;> rfl
theorem parser01 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell01)=
    ok (some ⟨⟨1512306873#u32,854234191#u32⟩,⟨663563884#u32,634237326#u32⟩⟩) :=
  JFr_EncodedCell.parser cell01 limbs01 encoded01
#print axioms encoded01
#print axioms parser01
def cell02 : Array U8 16#usize := ⟨[19#u8,97#u8,243#u8,10#u8,232#u8,209#u8,211#u8,30#u8,192#u8,103#u8,101#u8,120#u8,231#u8,104#u8,15#u8,51#u8],by rfl⟩
def limbs02 : QM31Limbs := ![⟨183722259,by change 183722259<2147483647;omega⟩,⟨517198312,by change 517198312<2147483647;omega⟩,⟨2019911616,by change 2019911616<2147483647;omega⟩,⟨856647911,by change 856647911<2147483647;omega⟩]
theorem rawCell02 : (raw.drop 32).take 16=cell02.val := by
  simp only [raw,JFz_Scan48.data,JFz_Scan48.j00,JFz_Scan48.j01,JFz_Scan48.j02,JFz_Scan48.j03,JFz_Scan48.j04,JFz_Scan48.j05,JFz_Scan48.j06,JFz_Scan48.j07,JFz_Scan48.j08,JFz_Scan48.j09,JFz_Scan48.j10,JFz_Scan48.j11,JFz_Scan48.j12,JFz_Scan48.b00_length,JFz_Scan48.b01_length,JFz_Scan48.b02_length,JFz_Scan48.b03_length,JFz_Scan48.b04_length,JFz_Scan48.b05_length,JFz_Scan48.b06_length,JFz_Scan48.b07_length,JFz_Scan48.b08_length,JFz_Scan48.b09_length,JFz_Scan48.b10_length,JFz_Scan48.b11_length,JFz_Scan48.b12_length,JFz_Scan48.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell02
theorem encoded02 : CandidateParserByteOrder.arrayBytes16 cell02=encodeQM31LE limbs02 := by
  funext i
  fin_cases i <;> rfl
theorem parser02 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell02)=
    ok (some ⟨⟨183722259#u32,517198312#u32⟩,⟨2019911616#u32,856647911#u32⟩⟩) :=
  JFr_EncodedCell.parser cell02 limbs02 encoded02
#print axioms encoded02
#print axioms parser02
def cell03 : Array U8 16#usize := ⟨[36#u8,47#u8,4#u8,76#u8,251#u8,74#u8,195#u8,90#u8,69#u8,200#u8,139#u8,106#u8,97#u8,201#u8,191#u8,100#u8],by rfl⟩
def limbs03 : QM31Limbs := ![⟨1275342628,by change 1275342628<2147483647;omega⟩,⟨1522748155,by change 1522748155<2147483647;omega⟩,⟨1787545669,by change 1787545669<2147483647;omega⟩,⟨1690290529,by change 1690290529<2147483647;omega⟩]
theorem rawCell03 : (raw.drop 48).take 16=cell03.val := by
  simp only [raw,JFz_Scan48.data,JFz_Scan48.j00,JFz_Scan48.j01,JFz_Scan48.j02,JFz_Scan48.j03,JFz_Scan48.j04,JFz_Scan48.j05,JFz_Scan48.j06,JFz_Scan48.j07,JFz_Scan48.j08,JFz_Scan48.j09,JFz_Scan48.j10,JFz_Scan48.j11,JFz_Scan48.j12,JFz_Scan48.b00_length,JFz_Scan48.b01_length,JFz_Scan48.b02_length,JFz_Scan48.b03_length,JFz_Scan48.b04_length,JFz_Scan48.b05_length,JFz_Scan48.b06_length,JFz_Scan48.b07_length,JFz_Scan48.b08_length,JFz_Scan48.b09_length,JFz_Scan48.b10_length,JFz_Scan48.b11_length,JFz_Scan48.b12_length,JFz_Scan48.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell03
theorem encoded03 : CandidateParserByteOrder.arrayBytes16 cell03=encodeQM31LE limbs03 := by
  funext i
  fin_cases i <;> rfl
theorem parser03 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell03)=
    ok (some ⟨⟨1275342628#u32,1522748155#u32⟩,⟨1787545669#u32,1690290529#u32⟩⟩) :=
  JFr_EncodedCell.parser cell03 limbs03 encoded03
#print axioms encoded03
#print axioms parser03
def cell04 : Array U8 16#usize := ⟨[140#u8,101#u8,122#u8,78#u8,194#u8,219#u8,129#u8,98#u8,162#u8,236#u8,136#u8,122#u8,86#u8,232#u8,151#u8,114#u8],by rfl⟩
def limbs04 : QM31Limbs := ![⟨1316644236,by change 1316644236<2147483647;omega⟩,⟨1652677570,by change 1652677570<2147483647;omega⟩,⟨2055793826,by change 2055793826<2147483647;omega⟩,⟨1922558038,by change 1922558038<2147483647;omega⟩]
theorem rawCell04 : (raw.drop 64).take 16=cell04.val := by
  simp only [raw,JFz_Scan48.data,JFz_Scan48.j00,JFz_Scan48.j01,JFz_Scan48.j02,JFz_Scan48.j03,JFz_Scan48.j04,JFz_Scan48.j05,JFz_Scan48.j06,JFz_Scan48.j07,JFz_Scan48.j08,JFz_Scan48.j09,JFz_Scan48.j10,JFz_Scan48.j11,JFz_Scan48.j12,JFz_Scan48.b00_length,JFz_Scan48.b01_length,JFz_Scan48.b02_length,JFz_Scan48.b03_length,JFz_Scan48.b04_length,JFz_Scan48.b05_length,JFz_Scan48.b06_length,JFz_Scan48.b07_length,JFz_Scan48.b08_length,JFz_Scan48.b09_length,JFz_Scan48.b10_length,JFz_Scan48.b11_length,JFz_Scan48.b12_length,JFz_Scan48.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell04
theorem encoded04 : CandidateParserByteOrder.arrayBytes16 cell04=encodeQM31LE limbs04 := by
  funext i
  fin_cases i <;> rfl
theorem parser04 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell04)=
    ok (some ⟨⟨1316644236#u32,1652677570#u32⟩,⟨2055793826#u32,1922558038#u32⟩⟩) :=
  JFr_EncodedCell.parser cell04 limbs04 encoded04
#print axioms encoded04
#print axioms parser04
def cell05 : Array U8 16#usize := ⟨[162#u8,200#u8,44#u8,63#u8,139#u8,248#u8,173#u8,95#u8,232#u8,3#u8,90#u8,4#u8,93#u8,135#u8,183#u8,20#u8],by rfl⟩
def limbs05 : QM31Limbs := ![⟨1059899554,by change 1059899554<2147483647;omega⟩,⟨1605236875,by change 1605236875<2147483647;omega⟩,⟨73008104,by change 73008104<2147483647;omega⟩,⟨347572061,by change 347572061<2147483647;omega⟩]
theorem rawCell05 : (raw.drop 80).take 16=cell05.val := by
  simp only [raw,JFz_Scan48.data,JFz_Scan48.j00,JFz_Scan48.j01,JFz_Scan48.j02,JFz_Scan48.j03,JFz_Scan48.j04,JFz_Scan48.j05,JFz_Scan48.j06,JFz_Scan48.j07,JFz_Scan48.j08,JFz_Scan48.j09,JFz_Scan48.j10,JFz_Scan48.j11,JFz_Scan48.j12,JFz_Scan48.b00_length,JFz_Scan48.b01_length,JFz_Scan48.b02_length,JFz_Scan48.b03_length,JFz_Scan48.b04_length,JFz_Scan48.b05_length,JFz_Scan48.b06_length,JFz_Scan48.b07_length,JFz_Scan48.b08_length,JFz_Scan48.b09_length,JFz_Scan48.b10_length,JFz_Scan48.b11_length,JFz_Scan48.b12_length,JFz_Scan48.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell05
theorem encoded05 : CandidateParserByteOrder.arrayBytes16 cell05=encodeQM31LE limbs05 := by
  funext i
  fin_cases i <;> rfl
theorem parser05 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell05)=
    ok (some ⟨⟨1059899554#u32,1605236875#u32⟩,⟨73008104#u32,347572061#u32⟩⟩) :=
  JFr_EncodedCell.parser cell05 limbs05 encoded05
#print axioms encoded05
#print axioms parser05
def cell06 : Array U8 16#usize := ⟨[68#u8,240#u8,42#u8,19#u8,92#u8,139#u8,222#u8,94#u8,112#u8,215#u8,7#u8,24#u8,45#u8,176#u8,211#u8,107#u8],by rfl⟩
def limbs06 : QM31Limbs := ![⟨321581124,by change 321581124<2147483647;omega⟩,⟨1591642972,by change 1591642972<2147483647;omega⟩,⟨403167088,by change 403167088<2147483647;omega⟩,⟨1809035309,by change 1809035309<2147483647;omega⟩]
theorem rawCell06 : (raw.drop 96).take 16=cell06.val := by
  simp only [raw,JFz_Scan48.data,JFz_Scan48.j00,JFz_Scan48.j01,JFz_Scan48.j02,JFz_Scan48.j03,JFz_Scan48.j04,JFz_Scan48.j05,JFz_Scan48.j06,JFz_Scan48.j07,JFz_Scan48.j08,JFz_Scan48.j09,JFz_Scan48.j10,JFz_Scan48.j11,JFz_Scan48.j12,JFz_Scan48.b00_length,JFz_Scan48.b01_length,JFz_Scan48.b02_length,JFz_Scan48.b03_length,JFz_Scan48.b04_length,JFz_Scan48.b05_length,JFz_Scan48.b06_length,JFz_Scan48.b07_length,JFz_Scan48.b08_length,JFz_Scan48.b09_length,JFz_Scan48.b10_length,JFz_Scan48.b11_length,JFz_Scan48.b12_length,JFz_Scan48.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell06
theorem encoded06 : CandidateParserByteOrder.arrayBytes16 cell06=encodeQM31LE limbs06 := by
  funext i
  fin_cases i <;> rfl
theorem parser06 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell06)=
    ok (some ⟨⟨321581124#u32,1591642972#u32⟩,⟨403167088#u32,1809035309#u32⟩⟩) :=
  JFr_EncodedCell.parser cell06 limbs06 encoded06
#print axioms encoded06
#print axioms parser06
def cell07 : Array U8 16#usize := ⟨[206#u8,135#u8,36#u8,16#u8,71#u8,11#u8,202#u8,36#u8,8#u8,88#u8,33#u8,68#u8,76#u8,172#u8,183#u8,43#u8],by rfl⟩
def limbs07 : QM31Limbs := ![⟨270829518,by change 270829518<2147483647;omega⟩,⟨617220935,by change 617220935<2147483647;omega⟩,⟨1143035912,by change 1143035912<2147483647;omega⟩,⟨733457484,by change 733457484<2147483647;omega⟩]
theorem rawCell07 : (raw.drop 112).take 16=cell07.val := by
  simp only [raw,JFz_Scan48.data,JFz_Scan48.j00,JFz_Scan48.j01,JFz_Scan48.j02,JFz_Scan48.j03,JFz_Scan48.j04,JFz_Scan48.j05,JFz_Scan48.j06,JFz_Scan48.j07,JFz_Scan48.j08,JFz_Scan48.j09,JFz_Scan48.j10,JFz_Scan48.j11,JFz_Scan48.j12,JFz_Scan48.b00_length,JFz_Scan48.b01_length,JFz_Scan48.b02_length,JFz_Scan48.b03_length,JFz_Scan48.b04_length,JFz_Scan48.b05_length,JFz_Scan48.b06_length,JFz_Scan48.b07_length,JFz_Scan48.b08_length,JFz_Scan48.b09_length,JFz_Scan48.b10_length,JFz_Scan48.b11_length,JFz_Scan48.b12_length,JFz_Scan48.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell07
theorem encoded07 : CandidateParserByteOrder.arrayBytes16 cell07=encodeQM31LE limbs07 := by
  funext i
  fin_cases i <;> rfl
theorem parser07 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell07)=
    ok (some ⟨⟨270829518#u32,617220935#u32⟩,⟨1143035912#u32,733457484#u32⟩⟩) :=
  JFr_EncodedCell.parser cell07 limbs07 encoded07
#print axioms encoded07
#print axioms parser07
def cell08 : Array U8 16#usize := ⟨[138#u8,247#u8,61#u8,6#u8,224#u8,146#u8,169#u8,83#u8,42#u8,102#u8,50#u8,80#u8,183#u8,115#u8,125#u8,35#u8],by rfl⟩
def limbs08 : QM31Limbs := ![⟨104724362,by change 104724362<2147483647;omega⟩,⟨1403622112,by change 1403622112<2147483647;omega⟩,⟨1345480234,by change 1345480234<2147483647;omega⟩,⟨595424183,by change 595424183<2147483647;omega⟩]
theorem rawCell08 : (raw.drop 128).take 16=cell08.val := by
  simp only [raw,JFz_Scan48.data,JFz_Scan48.j00,JFz_Scan48.j01,JFz_Scan48.j02,JFz_Scan48.j03,JFz_Scan48.j04,JFz_Scan48.j05,JFz_Scan48.j06,JFz_Scan48.j07,JFz_Scan48.j08,JFz_Scan48.j09,JFz_Scan48.j10,JFz_Scan48.j11,JFz_Scan48.j12,JFz_Scan48.b00_length,JFz_Scan48.b01_length,JFz_Scan48.b02_length,JFz_Scan48.b03_length,JFz_Scan48.b04_length,JFz_Scan48.b05_length,JFz_Scan48.b06_length,JFz_Scan48.b07_length,JFz_Scan48.b08_length,JFz_Scan48.b09_length,JFz_Scan48.b10_length,JFz_Scan48.b11_length,JFz_Scan48.b12_length,JFz_Scan48.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell08
theorem encoded08 : CandidateParserByteOrder.arrayBytes16 cell08=encodeQM31LE limbs08 := by
  funext i
  fin_cases i <;> rfl
theorem parser08 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell08)=
    ok (some ⟨⟨104724362#u32,1403622112#u32⟩,⟨1345480234#u32,595424183#u32⟩⟩) :=
  JFr_EncodedCell.parser cell08 limbs08 encoded08
#print axioms encoded08
#print axioms parser08
def cell09 : Array U8 16#usize := ⟨[66#u8,72#u8,174#u8,38#u8,149#u8,229#u8,162#u8,96#u8,56#u8,117#u8,181#u8,48#u8,167#u8,33#u8,88#u8,96#u8],by rfl⟩
def limbs09 : QM31Limbs := ![⟨648955970,by change 648955970<2147483647;omega⟩,⟨1621288341,by change 1621288341<2147483647;omega⟩,⟨817198392,by change 817198392<2147483647;omega⟩,⟨1616388519,by change 1616388519<2147483647;omega⟩]
theorem rawCell09 : (raw.drop 144).take 16=cell09.val := by
  simp only [raw,JFz_Scan48.data,JFz_Scan48.j00,JFz_Scan48.j01,JFz_Scan48.j02,JFz_Scan48.j03,JFz_Scan48.j04,JFz_Scan48.j05,JFz_Scan48.j06,JFz_Scan48.j07,JFz_Scan48.j08,JFz_Scan48.j09,JFz_Scan48.j10,JFz_Scan48.j11,JFz_Scan48.j12,JFz_Scan48.b00_length,JFz_Scan48.b01_length,JFz_Scan48.b02_length,JFz_Scan48.b03_length,JFz_Scan48.b04_length,JFz_Scan48.b05_length,JFz_Scan48.b06_length,JFz_Scan48.b07_length,JFz_Scan48.b08_length,JFz_Scan48.b09_length,JFz_Scan48.b10_length,JFz_Scan48.b11_length,JFz_Scan48.b12_length,JFz_Scan48.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell09
theorem encoded09 : CandidateParserByteOrder.arrayBytes16 cell09=encodeQM31LE limbs09 := by
  funext i
  fin_cases i <;> rfl
theorem parser09 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell09)=
    ok (some ⟨⟨648955970#u32,1621288341#u32⟩,⟨817198392#u32,1616388519#u32⟩⟩) :=
  JFr_EncodedCell.parser cell09 limbs09 encoded09
#print axioms encoded09
#print axioms parser09
def cell10 : Array U8 16#usize := ⟨[76#u8,221#u8,173#u8,81#u8,222#u8,245#u8,139#u8,117#u8,172#u8,243#u8,54#u8,53#u8,149#u8,74#u8,33#u8,4#u8],by rfl⟩
def limbs10 : QM31Limbs := ![⟨1370348876,by change 1370348876<2147483647;omega⟩,⟨1972106718,by change 1972106718<2147483647;omega⟩,⟨892793772,by change 892793772<2147483647;omega⟩,⟨69290645,by change 69290645<2147483647;omega⟩]
theorem rawCell10 : (raw.drop 160).take 16=cell10.val := by
  simp only [raw,JFz_Scan48.data,JFz_Scan48.j00,JFz_Scan48.j01,JFz_Scan48.j02,JFz_Scan48.j03,JFz_Scan48.j04,JFz_Scan48.j05,JFz_Scan48.j06,JFz_Scan48.j07,JFz_Scan48.j08,JFz_Scan48.j09,JFz_Scan48.j10,JFz_Scan48.j11,JFz_Scan48.j12,JFz_Scan48.b00_length,JFz_Scan48.b01_length,JFz_Scan48.b02_length,JFz_Scan48.b03_length,JFz_Scan48.b04_length,JFz_Scan48.b05_length,JFz_Scan48.b06_length,JFz_Scan48.b07_length,JFz_Scan48.b08_length,JFz_Scan48.b09_length,JFz_Scan48.b10_length,JFz_Scan48.b11_length,JFz_Scan48.b12_length,JFz_Scan48.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell10
theorem encoded10 : CandidateParserByteOrder.arrayBytes16 cell10=encodeQM31LE limbs10 := by
  funext i
  fin_cases i <;> rfl
theorem parser10 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell10)=
    ok (some ⟨⟨1370348876#u32,1972106718#u32⟩,⟨892793772#u32,69290645#u32⟩⟩) :=
  JFr_EncodedCell.parser cell10 limbs10 encoded10
#print axioms encoded10
#print axioms parser10
def cell11 : Array U8 16#usize := ⟨[194#u8,67#u8,60#u8,28#u8,153#u8,158#u8,75#u8,9#u8,214#u8,150#u8,86#u8,28#u8,205#u8,158#u8,179#u8,15#u8],by rfl⟩
def limbs11 : QM31Limbs := ![⟨473711554,by change 473711554<2147483647;omega⟩,⟨155950745,by change 155950745<2147483647;omega⟩,⟨475436758,by change 475436758<2147483647;omega⟩,⟨263429837,by change 263429837<2147483647;omega⟩]
theorem rawCell11 : (raw.drop 176).take 16=cell11.val := by
  simp only [raw,JFz_Scan48.data,JFz_Scan48.j00,JFz_Scan48.j01,JFz_Scan48.j02,JFz_Scan48.j03,JFz_Scan48.j04,JFz_Scan48.j05,JFz_Scan48.j06,JFz_Scan48.j07,JFz_Scan48.j08,JFz_Scan48.j09,JFz_Scan48.j10,JFz_Scan48.j11,JFz_Scan48.j12,JFz_Scan48.b00_length,JFz_Scan48.b01_length,JFz_Scan48.b02_length,JFz_Scan48.b03_length,JFz_Scan48.b04_length,JFz_Scan48.b05_length,JFz_Scan48.b06_length,JFz_Scan48.b07_length,JFz_Scan48.b08_length,JFz_Scan48.b09_length,JFz_Scan48.b10_length,JFz_Scan48.b11_length,JFz_Scan48.b12_length,JFz_Scan48.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell11
theorem encoded11 : CandidateParserByteOrder.arrayBytes16 cell11=encodeQM31LE limbs11 := by
  funext i
  fin_cases i <;> rfl
theorem parser11 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell11)=
    ok (some ⟨⟨473711554#u32,155950745#u32⟩,⟨475436758#u32,263429837#u32⟩⟩) :=
  JFr_EncodedCell.parser cell11 limbs11 encoded11
#print axioms encoded11
#print axioms parser11
def cell12 : Array U8 16#usize := ⟨[84#u8,156#u8,7#u8,81#u8,71#u8,105#u8,193#u8,119#u8,149#u8,71#u8,216#u8,61#u8,69#u8,10#u8,71#u8,26#u8],by rfl⟩
def limbs12 : QM31Limbs := ![⟨1359453268,by change 1359453268<2147483647;omega⟩,⟨2009164103,by change 2009164103<2147483647;omega⟩,⟨1037584277,by change 1037584277<2147483647;omega⟩,⟨440863301,by change 440863301<2147483647;omega⟩]
theorem rawCell12 : (raw.drop 192).take 16=cell12.val := by
  simp only [raw,JFz_Scan48.data,JFz_Scan48.j00,JFz_Scan48.j01,JFz_Scan48.j02,JFz_Scan48.j03,JFz_Scan48.j04,JFz_Scan48.j05,JFz_Scan48.j06,JFz_Scan48.j07,JFz_Scan48.j08,JFz_Scan48.j09,JFz_Scan48.j10,JFz_Scan48.j11,JFz_Scan48.j12,JFz_Scan48.b00_length,JFz_Scan48.b01_length,JFz_Scan48.b02_length,JFz_Scan48.b03_length,JFz_Scan48.b04_length,JFz_Scan48.b05_length,JFz_Scan48.b06_length,JFz_Scan48.b07_length,JFz_Scan48.b08_length,JFz_Scan48.b09_length,JFz_Scan48.b10_length,JFz_Scan48.b11_length,JFz_Scan48.b12_length,JFz_Scan48.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell12
theorem encoded12 : CandidateParserByteOrder.arrayBytes16 cell12=encodeQM31LE limbs12 := by
  funext i
  fin_cases i <;> rfl
theorem parser12 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell12)=
    ok (some ⟨⟨1359453268#u32,2009164103#u32⟩,⟨1037584277#u32,440863301#u32⟩⟩) :=
  JFr_EncodedCell.parser cell12 limbs12 encoded12
#print axioms encoded12
#print axioms parser12
def cell13 : Array U8 16#usize := ⟨[35#u8,101#u8,69#u8,29#u8,235#u8,1#u8,116#u8,62#u8,19#u8,96#u8,208#u8,57#u8,48#u8,205#u8,144#u8,113#u8],by rfl⟩
def limbs13 : QM31Limbs := ![⟨491087139,by change 491087139<2147483647;omega⟩,⟨1047790059,by change 1047790059<2147483647;omega⟩,⟨969957395,by change 969957395<2147483647;omega⟩,⟨1905315120,by change 1905315120<2147483647;omega⟩]
theorem rawCell13 : (raw.drop 208).take 16=cell13.val := by
  simp only [raw,JFz_Scan48.data,JFz_Scan48.j00,JFz_Scan48.j01,JFz_Scan48.j02,JFz_Scan48.j03,JFz_Scan48.j04,JFz_Scan48.j05,JFz_Scan48.j06,JFz_Scan48.j07,JFz_Scan48.j08,JFz_Scan48.j09,JFz_Scan48.j10,JFz_Scan48.j11,JFz_Scan48.j12,JFz_Scan48.b00_length,JFz_Scan48.b01_length,JFz_Scan48.b02_length,JFz_Scan48.b03_length,JFz_Scan48.b04_length,JFz_Scan48.b05_length,JFz_Scan48.b06_length,JFz_Scan48.b07_length,JFz_Scan48.b08_length,JFz_Scan48.b09_length,JFz_Scan48.b10_length,JFz_Scan48.b11_length,JFz_Scan48.b12_length,JFz_Scan48.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell13
theorem encoded13 : CandidateParserByteOrder.arrayBytes16 cell13=encodeQM31LE limbs13 := by
  funext i
  fin_cases i <;> rfl
theorem parser13 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell13)=
    ok (some ⟨⟨491087139#u32,1047790059#u32⟩,⟨969957395#u32,1905315120#u32⟩⟩) :=
  JFr_EncodedCell.parser cell13 limbs13 encoded13
#print axioms encoded13
#print axioms parser13
def cell14 : Array U8 16#usize := ⟨[238#u8,212#u8,154#u8,113#u8,143#u8,244#u8,115#u8,113#u8,244#u8,33#u8,19#u8,112#u8,109#u8,230#u8,160#u8,104#u8],by rfl⟩
def limbs14 : QM31Limbs := ![⟨1905972462,by change 1905972462<2147483647;omega⟩,⟨1903424655,by change 1903424655<2147483647;omega⟩,⟨1880302068,by change 1880302068<2147483647;omega⟩,⟨1755375213,by change 1755375213<2147483647;omega⟩]
theorem rawCell14 : (raw.drop 224).take 16=cell14.val := by
  simp only [raw,JFz_Scan48.data,JFz_Scan48.j00,JFz_Scan48.j01,JFz_Scan48.j02,JFz_Scan48.j03,JFz_Scan48.j04,JFz_Scan48.j05,JFz_Scan48.j06,JFz_Scan48.j07,JFz_Scan48.j08,JFz_Scan48.j09,JFz_Scan48.j10,JFz_Scan48.j11,JFz_Scan48.j12,JFz_Scan48.b00_length,JFz_Scan48.b01_length,JFz_Scan48.b02_length,JFz_Scan48.b03_length,JFz_Scan48.b04_length,JFz_Scan48.b05_length,JFz_Scan48.b06_length,JFz_Scan48.b07_length,JFz_Scan48.b08_length,JFz_Scan48.b09_length,JFz_Scan48.b10_length,JFz_Scan48.b11_length,JFz_Scan48.b12_length,JFz_Scan48.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell14
theorem encoded14 : CandidateParserByteOrder.arrayBytes16 cell14=encodeQM31LE limbs14 := by
  funext i
  fin_cases i <;> rfl
theorem parser14 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell14)=
    ok (some ⟨⟨1905972462#u32,1903424655#u32⟩,⟨1880302068#u32,1755375213#u32⟩⟩) :=
  JFr_EncodedCell.parser cell14 limbs14 encoded14
#print axioms encoded14
#print axioms parser14
def cell15 : Array U8 16#usize := ⟨[115#u8,94#u8,51#u8,32#u8,160#u8,12#u8,89#u8,50#u8,208#u8,116#u8,102#u8,126#u8,106#u8,4#u8,53#u8,44#u8],by rfl⟩
def limbs15 : QM31Limbs := ![⟨540237427,by change 540237427<2147483647;omega⟩,⟨844696736,by change 844696736<2147483647;omega⟩,⟨2120643792,by change 2120643792<2147483647;omega⟩,⟨741672042,by change 741672042<2147483647;omega⟩]
theorem rawCell15 : (raw.drop 240).take 16=cell15.val := by
  simp only [raw,JFz_Scan48.data,JFz_Scan48.j00,JFz_Scan48.j01,JFz_Scan48.j02,JFz_Scan48.j03,JFz_Scan48.j04,JFz_Scan48.j05,JFz_Scan48.j06,JFz_Scan48.j07,JFz_Scan48.j08,JFz_Scan48.j09,JFz_Scan48.j10,JFz_Scan48.j11,JFz_Scan48.j12,JFz_Scan48.b00_length,JFz_Scan48.b01_length,JFz_Scan48.b02_length,JFz_Scan48.b03_length,JFz_Scan48.b04_length,JFz_Scan48.b05_length,JFz_Scan48.b06_length,JFz_Scan48.b07_length,JFz_Scan48.b08_length,JFz_Scan48.b09_length,JFz_Scan48.b10_length,JFz_Scan48.b11_length,JFz_Scan48.b12_length,JFz_Scan48.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell15
theorem encoded15 : CandidateParserByteOrder.arrayBytes16 cell15=encodeQM31LE limbs15 := by
  funext i
  fin_cases i <;> rfl
theorem parser15 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell15)=
    ok (some ⟨⟨540237427#u32,844696736#u32⟩,⟨2120643792#u32,741672042#u32⟩⟩) :=
  JFr_EncodedCell.parser cell15 limbs15 encoded15
#print axioms encoded15
#print axioms parser15
def cell16 : Array U8 16#usize := ⟨[188#u8,136#u8,157#u8,2#u8,158#u8,228#u8,182#u8,43#u8,48#u8,210#u8,133#u8,11#u8,58#u8,88#u8,61#u8,77#u8],by rfl⟩
def limbs16 : QM31Limbs := ![⟨43878588,by change 43878588<2147483647;omega⟩,⟨733406366,by change 733406366<2147483647;omega⟩,⟨193319472,by change 193319472<2147483647;omega⟩,⟨1295865914,by change 1295865914<2147483647;omega⟩]
theorem rawCell16 : (raw.drop 256).take 16=cell16.val := by
  simp only [raw,JFz_Scan48.data,JFz_Scan48.j00,JFz_Scan48.j01,JFz_Scan48.j02,JFz_Scan48.j03,JFz_Scan48.j04,JFz_Scan48.j05,JFz_Scan48.j06,JFz_Scan48.j07,JFz_Scan48.j08,JFz_Scan48.j09,JFz_Scan48.j10,JFz_Scan48.j11,JFz_Scan48.j12,JFz_Scan48.b00_length,JFz_Scan48.b01_length,JFz_Scan48.b02_length,JFz_Scan48.b03_length,JFz_Scan48.b04_length,JFz_Scan48.b05_length,JFz_Scan48.b06_length,JFz_Scan48.b07_length,JFz_Scan48.b08_length,JFz_Scan48.b09_length,JFz_Scan48.b10_length,JFz_Scan48.b11_length,JFz_Scan48.b12_length,JFz_Scan48.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell16
theorem encoded16 : CandidateParserByteOrder.arrayBytes16 cell16=encodeQM31LE limbs16 := by
  funext i
  fin_cases i <;> rfl
theorem parser16 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell16)=
    ok (some ⟨⟨43878588#u32,733406366#u32⟩,⟨193319472#u32,1295865914#u32⟩⟩) :=
  JFr_EncodedCell.parser cell16 limbs16 encoded16
#print axioms encoded16
#print axioms parser16
def cell17 : Array U8 16#usize := ⟨[160#u8,87#u8,166#u8,75#u8,78#u8,35#u8,175#u8,91#u8,201#u8,198#u8,169#u8,41#u8,116#u8,229#u8,5#u8,110#u8],by rfl⟩
def limbs17 : QM31Limbs := ![⟨1269192608,by change 1269192608<2147483647;omega⟩,⟨1538204494,by change 1538204494<2147483647;omega⟩,⟨698992329,by change 698992329<2147483647;omega⟩,⟨1845880180,by change 1845880180<2147483647;omega⟩]
theorem rawCell17 : (raw.drop 272).take 16=cell17.val := by
  simp only [raw,JFz_Scan48.data,JFz_Scan48.j00,JFz_Scan48.j01,JFz_Scan48.j02,JFz_Scan48.j03,JFz_Scan48.j04,JFz_Scan48.j05,JFz_Scan48.j06,JFz_Scan48.j07,JFz_Scan48.j08,JFz_Scan48.j09,JFz_Scan48.j10,JFz_Scan48.j11,JFz_Scan48.j12,JFz_Scan48.b00_length,JFz_Scan48.b01_length,JFz_Scan48.b02_length,JFz_Scan48.b03_length,JFz_Scan48.b04_length,JFz_Scan48.b05_length,JFz_Scan48.b06_length,JFz_Scan48.b07_length,JFz_Scan48.b08_length,JFz_Scan48.b09_length,JFz_Scan48.b10_length,JFz_Scan48.b11_length,JFz_Scan48.b12_length,JFz_Scan48.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell17
theorem encoded17 : CandidateParserByteOrder.arrayBytes16 cell17=encodeQM31LE limbs17 := by
  funext i
  fin_cases i <;> rfl
theorem parser17 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell17)=
    ok (some ⟨⟨1269192608#u32,1538204494#u32⟩,⟨698992329#u32,1845880180#u32⟩⟩) :=
  JFr_EncodedCell.parser cell17 limbs17 encoded17
#print axioms encoded17
#print axioms parser17
def cell18 : Array U8 16#usize := ⟨[3#u8,179#u8,255#u8,86#u8,156#u8,23#u8,142#u8,23#u8,163#u8,26#u8,141#u8,112#u8,44#u8,95#u8,107#u8,83#u8],by rfl⟩
def limbs18 : QM31Limbs := ![⟨1459598083,by change 1459598083<2147483647;omega⟩,⟨395188124,by change 395188124<2147483647;omega⟩,⟨1888295587,by change 1888295587<2147483647;omega⟩,⟨1399545644,by change 1399545644<2147483647;omega⟩]
theorem rawCell18 : (raw.drop 288).take 16=cell18.val := by
  simp only [raw,JFz_Scan48.data,JFz_Scan48.j00,JFz_Scan48.j01,JFz_Scan48.j02,JFz_Scan48.j03,JFz_Scan48.j04,JFz_Scan48.j05,JFz_Scan48.j06,JFz_Scan48.j07,JFz_Scan48.j08,JFz_Scan48.j09,JFz_Scan48.j10,JFz_Scan48.j11,JFz_Scan48.j12,JFz_Scan48.b00_length,JFz_Scan48.b01_length,JFz_Scan48.b02_length,JFz_Scan48.b03_length,JFz_Scan48.b04_length,JFz_Scan48.b05_length,JFz_Scan48.b06_length,JFz_Scan48.b07_length,JFz_Scan48.b08_length,JFz_Scan48.b09_length,JFz_Scan48.b10_length,JFz_Scan48.b11_length,JFz_Scan48.b12_length,JFz_Scan48.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell18
theorem encoded18 : CandidateParserByteOrder.arrayBytes16 cell18=encodeQM31LE limbs18 := by
  funext i
  fin_cases i <;> rfl
theorem parser18 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell18)=
    ok (some ⟨⟨1459598083#u32,395188124#u32⟩,⟨1888295587#u32,1399545644#u32⟩⟩) :=
  JFr_EncodedCell.parser cell18 limbs18 encoded18
#print axioms encoded18
#print axioms parser18
def cell19 : Array U8 16#usize := ⟨[219#u8,196#u8,186#u8,9#u8,171#u8,65#u8,164#u8,110#u8,212#u8,131#u8,158#u8,36#u8,238#u8,121#u8,135#u8,88#u8],by rfl⟩
def limbs19 : QM31Limbs := ![⟨163235035,by change 163235035<2147483647;omega⟩,⟨1856258475,by change 1856258475<2147483647;omega⟩,⟨614368212,by change 614368212<2147483647;omega⟩,⟨1485273582,by change 1485273582<2147483647;omega⟩]
theorem rawCell19 : (raw.drop 304).take 16=cell19.val := by
  simp only [raw,JFz_Scan48.data,JFz_Scan48.j00,JFz_Scan48.j01,JFz_Scan48.j02,JFz_Scan48.j03,JFz_Scan48.j04,JFz_Scan48.j05,JFz_Scan48.j06,JFz_Scan48.j07,JFz_Scan48.j08,JFz_Scan48.j09,JFz_Scan48.j10,JFz_Scan48.j11,JFz_Scan48.j12,JFz_Scan48.b00_length,JFz_Scan48.b01_length,JFz_Scan48.b02_length,JFz_Scan48.b03_length,JFz_Scan48.b04_length,JFz_Scan48.b05_length,JFz_Scan48.b06_length,JFz_Scan48.b07_length,JFz_Scan48.b08_length,JFz_Scan48.b09_length,JFz_Scan48.b10_length,JFz_Scan48.b11_length,JFz_Scan48.b12_length,JFz_Scan48.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell19
theorem encoded19 : CandidateParserByteOrder.arrayBytes16 cell19=encodeQM31LE limbs19 := by
  funext i
  fin_cases i <;> rfl
theorem parser19 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell19)=
    ok (some ⟨⟨163235035#u32,1856258475#u32⟩,⟨614368212#u32,1485273582#u32⟩⟩) :=
  JFr_EncodedCell.parser cell19 limbs19 encoded19
#print axioms encoded19
#print axioms parser19
def cell20 : Array U8 16#usize := ⟨[128#u8,196#u8,225#u8,40#u8,176#u8,225#u8,168#u8,26#u8,49#u8,33#u8,74#u8,86#u8,211#u8,132#u8,76#u8,97#u8],by rfl⟩
def limbs20 : QM31Limbs := ![⟨685884544,by change 685884544<2147483647;omega⟩,⟨447275440,by change 447275440<2147483647;omega⟩,⟨1447698737,by change 1447698737<2147483647;omega⟩,⟨1632404691,by change 1632404691<2147483647;omega⟩]
theorem rawCell20 : (raw.drop 320).take 16=cell20.val := by
  simp only [raw,JFz_Scan48.data,JFz_Scan48.j00,JFz_Scan48.j01,JFz_Scan48.j02,JFz_Scan48.j03,JFz_Scan48.j04,JFz_Scan48.j05,JFz_Scan48.j06,JFz_Scan48.j07,JFz_Scan48.j08,JFz_Scan48.j09,JFz_Scan48.j10,JFz_Scan48.j11,JFz_Scan48.j12,JFz_Scan48.b00_length,JFz_Scan48.b01_length,JFz_Scan48.b02_length,JFz_Scan48.b03_length,JFz_Scan48.b04_length,JFz_Scan48.b05_length,JFz_Scan48.b06_length,JFz_Scan48.b07_length,JFz_Scan48.b08_length,JFz_Scan48.b09_length,JFz_Scan48.b10_length,JFz_Scan48.b11_length,JFz_Scan48.b12_length,JFz_Scan48.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell20
theorem encoded20 : CandidateParserByteOrder.arrayBytes16 cell20=encodeQM31LE limbs20 := by
  funext i
  fin_cases i <;> rfl
theorem parser20 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell20)=
    ok (some ⟨⟨685884544#u32,447275440#u32⟩,⟨1447698737#u32,1632404691#u32⟩⟩) :=
  JFr_EncodedCell.parser cell20 limbs20 encoded20
#print axioms encoded20
#print axioms parser20
def cell21 : Array U8 16#usize := ⟨[67#u8,233#u8,178#u8,84#u8,23#u8,93#u8,98#u8,47#u8,51#u8,216#u8,249#u8,27#u8,152#u8,79#u8,231#u8,64#u8],by rfl⟩
def limbs21 : QM31Limbs := ![⟨1421011267,by change 1421011267<2147483647;omega⟩,⟨794975511,by change 794975511<2147483647;omega⟩,⟨469358643,by change 469358643<2147483647;omega⟩,⟨1088901016,by change 1088901016<2147483647;omega⟩]
theorem rawCell21 : (raw.drop 336).take 16=cell21.val := by
  simp only [raw,JFz_Scan48.data,JFz_Scan48.j00,JFz_Scan48.j01,JFz_Scan48.j02,JFz_Scan48.j03,JFz_Scan48.j04,JFz_Scan48.j05,JFz_Scan48.j06,JFz_Scan48.j07,JFz_Scan48.j08,JFz_Scan48.j09,JFz_Scan48.j10,JFz_Scan48.j11,JFz_Scan48.j12,JFz_Scan48.b00_length,JFz_Scan48.b01_length,JFz_Scan48.b02_length,JFz_Scan48.b03_length,JFz_Scan48.b04_length,JFz_Scan48.b05_length,JFz_Scan48.b06_length,JFz_Scan48.b07_length,JFz_Scan48.b08_length,JFz_Scan48.b09_length,JFz_Scan48.b10_length,JFz_Scan48.b11_length,JFz_Scan48.b12_length,JFz_Scan48.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell21
theorem encoded21 : CandidateParserByteOrder.arrayBytes16 cell21=encodeQM31LE limbs21 := by
  funext i
  fin_cases i <;> rfl
theorem parser21 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell21)=
    ok (some ⟨⟨1421011267#u32,794975511#u32⟩,⟨469358643#u32,1088901016#u32⟩⟩) :=
  JFr_EncodedCell.parser cell21 limbs21 encoded21
#print axioms encoded21
#print axioms parser21
def cell22 : Array U8 16#usize := ⟨[199#u8,144#u8,131#u8,27#u8,88#u8,254#u8,70#u8,108#u8,131#u8,202#u8,55#u8,100#u8,79#u8,73#u8,157#u8,39#u8],by rfl⟩
def limbs22 : QM31Limbs := ![⟨461607111,by change 461607111<2147483647;omega⟩,⟨1816591960,by change 1816591960<2147483647;omega⟩,⟨1681377923,by change 1681377923<2147483647;omega⟩,⟨664619343,by change 664619343<2147483647;omega⟩]
theorem rawCell22 : (raw.drop 352).take 16=cell22.val := by
  simp only [raw,JFz_Scan48.data,JFz_Scan48.j00,JFz_Scan48.j01,JFz_Scan48.j02,JFz_Scan48.j03,JFz_Scan48.j04,JFz_Scan48.j05,JFz_Scan48.j06,JFz_Scan48.j07,JFz_Scan48.j08,JFz_Scan48.j09,JFz_Scan48.j10,JFz_Scan48.j11,JFz_Scan48.j12,JFz_Scan48.b00_length,JFz_Scan48.b01_length,JFz_Scan48.b02_length,JFz_Scan48.b03_length,JFz_Scan48.b04_length,JFz_Scan48.b05_length,JFz_Scan48.b06_length,JFz_Scan48.b07_length,JFz_Scan48.b08_length,JFz_Scan48.b09_length,JFz_Scan48.b10_length,JFz_Scan48.b11_length,JFz_Scan48.b12_length,JFz_Scan48.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell22
theorem encoded22 : CandidateParserByteOrder.arrayBytes16 cell22=encodeQM31LE limbs22 := by
  funext i
  fin_cases i <;> rfl
theorem parser22 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell22)=
    ok (some ⟨⟨461607111#u32,1816591960#u32⟩,⟨1681377923#u32,664619343#u32⟩⟩) :=
  JFr_EncodedCell.parser cell22 limbs22 encoded22
#print axioms encoded22
#print axioms parser22
def cell23 : Array U8 16#usize := ⟨[183#u8,63#u8,168#u8,57#u8,250#u8,101#u8,2#u8,55#u8,192#u8,32#u8,215#u8,120#u8,25#u8,174#u8,190#u8,117#u8],by rfl⟩
def limbs23 : QM31Limbs := ![⟨967327671,by change 967327671<2147483647;omega⟩,⟨922904058,by change 922904058<2147483647;omega⟩,⟨2027364544,by change 2027364544<2147483647;omega⟩,⟨1975430681,by change 1975430681<2147483647;omega⟩]
theorem rawCell23 : (raw.drop 368).take 16=cell23.val := by
  simp only [raw,JFz_Scan48.data,JFz_Scan48.j00,JFz_Scan48.j01,JFz_Scan48.j02,JFz_Scan48.j03,JFz_Scan48.j04,JFz_Scan48.j05,JFz_Scan48.j06,JFz_Scan48.j07,JFz_Scan48.j08,JFz_Scan48.j09,JFz_Scan48.j10,JFz_Scan48.j11,JFz_Scan48.j12,JFz_Scan48.b00_length,JFz_Scan48.b01_length,JFz_Scan48.b02_length,JFz_Scan48.b03_length,JFz_Scan48.b04_length,JFz_Scan48.b05_length,JFz_Scan48.b06_length,JFz_Scan48.b07_length,JFz_Scan48.b08_length,JFz_Scan48.b09_length,JFz_Scan48.b10_length,JFz_Scan48.b11_length,JFz_Scan48.b12_length,JFz_Scan48.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell23
theorem encoded23 : CandidateParserByteOrder.arrayBytes16 cell23=encodeQM31LE limbs23 := by
  funext i
  fin_cases i <;> rfl
theorem parser23 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell23)=
    ok (some ⟨⟨967327671#u32,922904058#u32⟩,⟨2027364544#u32,1975430681#u32⟩⟩) :=
  JFr_EncodedCell.parser cell23 limbs23 encoded23
#print axioms encoded23
#print axioms parser23
def cell24 : Array U8 16#usize := ⟨[212#u8,91#u8,209#u8,78#u8,106#u8,22#u8,137#u8,47#u8,132#u8,235#u8,14#u8,64#u8,182#u8,4#u8,133#u8,9#u8],by rfl⟩
def limbs24 : QM31Limbs := ![⟨1322343380,by change 1322343380<2147483647;omega⟩,⟨797513322,by change 797513322<2147483647;omega⟩,⟨1074719620,by change 1074719620<2147483647;omega⟩,⟨159712438,by change 159712438<2147483647;omega⟩]
theorem rawCell24 : (raw.drop 384).take 16=cell24.val := by
  simp only [raw,JFz_Scan48.data,JFz_Scan48.j00,JFz_Scan48.j01,JFz_Scan48.j02,JFz_Scan48.j03,JFz_Scan48.j04,JFz_Scan48.j05,JFz_Scan48.j06,JFz_Scan48.j07,JFz_Scan48.j08,JFz_Scan48.j09,JFz_Scan48.j10,JFz_Scan48.j11,JFz_Scan48.j12,JFz_Scan48.b00_length,JFz_Scan48.b01_length,JFz_Scan48.b02_length,JFz_Scan48.b03_length,JFz_Scan48.b04_length,JFz_Scan48.b05_length,JFz_Scan48.b06_length,JFz_Scan48.b07_length,JFz_Scan48.b08_length,JFz_Scan48.b09_length,JFz_Scan48.b10_length,JFz_Scan48.b11_length,JFz_Scan48.b12_length,JFz_Scan48.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell24
theorem encoded24 : CandidateParserByteOrder.arrayBytes16 cell24=encodeQM31LE limbs24 := by
  funext i
  fin_cases i <;> rfl
theorem parser24 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell24)=
    ok (some ⟨⟨1322343380#u32,797513322#u32⟩,⟨1074719620#u32,159712438#u32⟩⟩) :=
  JFr_EncodedCell.parser cell24 limbs24 encoded24
#print axioms encoded24
#print axioms parser24
def cell25 : Array U8 16#usize := ⟨[100#u8,242#u8,128#u8,57#u8,6#u8,89#u8,156#u8,19#u8,190#u8,142#u8,146#u8,56#u8,127#u8,232#u8,41#u8,76#u8],by rfl⟩
def limbs25 : QM31Limbs := ![⟨964751972,by change 964751972<2147483647;omega⟩,⟨329013510,by change 329013510<2147483647;omega⟩,⟨949128894,by change 949128894<2147483647;omega⟩,⟨1277814911,by change 1277814911<2147483647;omega⟩]
theorem rawCell25 : (raw.drop 400).take 16=cell25.val := by
  simp only [raw,JFz_Scan48.data,JFz_Scan48.j00,JFz_Scan48.j01,JFz_Scan48.j02,JFz_Scan48.j03,JFz_Scan48.j04,JFz_Scan48.j05,JFz_Scan48.j06,JFz_Scan48.j07,JFz_Scan48.j08,JFz_Scan48.j09,JFz_Scan48.j10,JFz_Scan48.j11,JFz_Scan48.j12,JFz_Scan48.b00_length,JFz_Scan48.b01_length,JFz_Scan48.b02_length,JFz_Scan48.b03_length,JFz_Scan48.b04_length,JFz_Scan48.b05_length,JFz_Scan48.b06_length,JFz_Scan48.b07_length,JFz_Scan48.b08_length,JFz_Scan48.b09_length,JFz_Scan48.b10_length,JFz_Scan48.b11_length,JFz_Scan48.b12_length,JFz_Scan48.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell25
theorem encoded25 : CandidateParserByteOrder.arrayBytes16 cell25=encodeQM31LE limbs25 := by
  funext i
  fin_cases i <;> rfl
theorem parser25 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell25)=
    ok (some ⟨⟨964751972#u32,329013510#u32⟩,⟨949128894#u32,1277814911#u32⟩⟩) :=
  JFr_EncodedCell.parser cell25 limbs25 encoded25
#print axioms encoded25
#print axioms parser25
def cell26 : Array U8 16#usize := ⟨[213#u8,154#u8,128#u8,43#u8,34#u8,59#u8,11#u8,73#u8,50#u8,155#u8,129#u8,76#u8,225#u8,92#u8,206#u8,41#u8],by rfl⟩
def limbs26 : QM31Limbs := ![⟨729848533,by change 729848533<2147483647;omega⟩,⟨1225472802,by change 1225472802<2147483647;omega⟩,⟨1283562290,by change 1283562290<2147483647;omega⟩,⟨701390049,by change 701390049<2147483647;omega⟩]
theorem rawCell26 : (raw.drop 416).take 16=cell26.val := by
  simp only [raw,JFz_Scan48.data,JFz_Scan48.j00,JFz_Scan48.j01,JFz_Scan48.j02,JFz_Scan48.j03,JFz_Scan48.j04,JFz_Scan48.j05,JFz_Scan48.j06,JFz_Scan48.j07,JFz_Scan48.j08,JFz_Scan48.j09,JFz_Scan48.j10,JFz_Scan48.j11,JFz_Scan48.j12,JFz_Scan48.b00_length,JFz_Scan48.b01_length,JFz_Scan48.b02_length,JFz_Scan48.b03_length,JFz_Scan48.b04_length,JFz_Scan48.b05_length,JFz_Scan48.b06_length,JFz_Scan48.b07_length,JFz_Scan48.b08_length,JFz_Scan48.b09_length,JFz_Scan48.b10_length,JFz_Scan48.b11_length,JFz_Scan48.b12_length,JFz_Scan48.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell26
theorem encoded26 : CandidateParserByteOrder.arrayBytes16 cell26=encodeQM31LE limbs26 := by
  funext i
  fin_cases i <;> rfl
theorem parser26 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell26)=
    ok (some ⟨⟨729848533#u32,1225472802#u32⟩,⟨1283562290#u32,701390049#u32⟩⟩) :=
  JFr_EncodedCell.parser cell26 limbs26 encoded26
#print axioms encoded26
#print axioms parser26
def cell27 : Array U8 16#usize := ⟨[100#u8,152#u8,13#u8,34#u8,46#u8,55#u8,49#u8,69#u8,102#u8,205#u8,129#u8,77#u8,63#u8,28#u8,218#u8,124#u8],by rfl⟩
def limbs27 : QM31Limbs := ![⟨571316324,by change 571316324<2147483647;omega⟩,⟨1160853294,by change 1160853294<2147483647;omega⟩,⟨1300352358,by change 1300352358<2147483647;omega⟩,⟨2094668863,by change 2094668863<2147483647;omega⟩]
theorem rawCell27 : (raw.drop 432).take 16=cell27.val := by
  simp only [raw,JFz_Scan48.data,JFz_Scan48.j00,JFz_Scan48.j01,JFz_Scan48.j02,JFz_Scan48.j03,JFz_Scan48.j04,JFz_Scan48.j05,JFz_Scan48.j06,JFz_Scan48.j07,JFz_Scan48.j08,JFz_Scan48.j09,JFz_Scan48.j10,JFz_Scan48.j11,JFz_Scan48.j12,JFz_Scan48.b00_length,JFz_Scan48.b01_length,JFz_Scan48.b02_length,JFz_Scan48.b03_length,JFz_Scan48.b04_length,JFz_Scan48.b05_length,JFz_Scan48.b06_length,JFz_Scan48.b07_length,JFz_Scan48.b08_length,JFz_Scan48.b09_length,JFz_Scan48.b10_length,JFz_Scan48.b11_length,JFz_Scan48.b12_length,JFz_Scan48.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell27
theorem encoded27 : CandidateParserByteOrder.arrayBytes16 cell27=encodeQM31LE limbs27 := by
  funext i
  fin_cases i <;> rfl
theorem parser27 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell27)=
    ok (some ⟨⟨571316324#u32,1160853294#u32⟩,⟨1300352358#u32,2094668863#u32⟩⟩) :=
  JFr_EncodedCell.parser cell27 limbs27 encoded27
#print axioms encoded27
#print axioms parser27
end AspisR1.JFr_Bytes00
