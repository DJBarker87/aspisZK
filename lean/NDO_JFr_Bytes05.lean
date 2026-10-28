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
def cell00 : Array U8 16#usize := ⟨[90#u8,57#u8,38#u8,85#u8,75#u8,78#u8,1#u8,88#u8,21#u8,34#u8,107#u8,98#u8,53#u8,39#u8,100#u8,119#u8],by rfl⟩
def limbs00 : QM31Limbs := ![⟨1428568410,by change 1428568410<2147483647;omega⟩,⟨1476480587,by change 1476480587<2147483647;omega⟩,⟨1651188245,by change 1651188245<2147483647;omega⟩,⟨2003052341,by change 2003052341<2147483647;omega⟩]
theorem rawCell00 : (raw.drop 0).take 16=cell00.val := by
  simp only [raw,JFz_Scan53.data,JFz_Scan53.j00,JFz_Scan53.j01,JFz_Scan53.j02,JFz_Scan53.j03,JFz_Scan53.j04,JFz_Scan53.j05,JFz_Scan53.j06,JFz_Scan53.j07,JFz_Scan53.j08,JFz_Scan53.j09,JFz_Scan53.j10,JFz_Scan53.j11,JFz_Scan53.j12,JFz_Scan53.b00_length,JFz_Scan53.b01_length,JFz_Scan53.b02_length,JFz_Scan53.b03_length,JFz_Scan53.b04_length,JFz_Scan53.b05_length,JFz_Scan53.b06_length,JFz_Scan53.b07_length,JFz_Scan53.b08_length,JFz_Scan53.b09_length,JFz_Scan53.b10_length,JFz_Scan53.b11_length,JFz_Scan53.b12_length,JFz_Scan53.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell00
theorem encoded00 : CandidateParserByteOrder.arrayBytes16 cell00=encodeQM31LE limbs00 := by
  funext i
  fin_cases i <;> rfl
theorem parser00 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell00)=
    ok (some ⟨⟨1428568410#u32,1476480587#u32⟩,⟨1651188245#u32,2003052341#u32⟩⟩) :=
  JFr_EncodedCell.parser cell00 limbs00 encoded00
#print axioms encoded00
#print axioms parser00
def cell01 : Array U8 16#usize := ⟨[183#u8,177#u8,210#u8,61#u8,182#u8,8#u8,142#u8,60#u8,26#u8,253#u8,204#u8,47#u8,112#u8,50#u8,2#u8,69#u8],by rfl⟩
def limbs01 : QM31Limbs := ![⟨1037218231,by change 1037218231<2147483647;omega⟩,⟨1015941302,by change 1015941302<2147483647;omega⟩,⟨801963290,by change 801963290<2147483647;omega⟩,⟨1157771888,by change 1157771888<2147483647;omega⟩]
theorem rawCell01 : (raw.drop 16).take 16=cell01.val := by
  simp only [raw,JFz_Scan53.data,JFz_Scan53.j00,JFz_Scan53.j01,JFz_Scan53.j02,JFz_Scan53.j03,JFz_Scan53.j04,JFz_Scan53.j05,JFz_Scan53.j06,JFz_Scan53.j07,JFz_Scan53.j08,JFz_Scan53.j09,JFz_Scan53.j10,JFz_Scan53.j11,JFz_Scan53.j12,JFz_Scan53.b00_length,JFz_Scan53.b01_length,JFz_Scan53.b02_length,JFz_Scan53.b03_length,JFz_Scan53.b04_length,JFz_Scan53.b05_length,JFz_Scan53.b06_length,JFz_Scan53.b07_length,JFz_Scan53.b08_length,JFz_Scan53.b09_length,JFz_Scan53.b10_length,JFz_Scan53.b11_length,JFz_Scan53.b12_length,JFz_Scan53.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell01
theorem encoded01 : CandidateParserByteOrder.arrayBytes16 cell01=encodeQM31LE limbs01 := by
  funext i
  fin_cases i <;> rfl
theorem parser01 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell01)=
    ok (some ⟨⟨1037218231#u32,1015941302#u32⟩,⟨801963290#u32,1157771888#u32⟩⟩) :=
  JFr_EncodedCell.parser cell01 limbs01 encoded01
#print axioms encoded01
#print axioms parser01
def cell02 : Array U8 16#usize := ⟨[61#u8,18#u8,239#u8,122#u8,113#u8,175#u8,150#u8,11#u8,230#u8,107#u8,166#u8,46#u8,81#u8,93#u8,164#u8,101#u8],by rfl⟩
def limbs02 : QM31Limbs := ![⟨2062488125,by change 2062488125<2147483647;omega⟩,⟨194424689,by change 194424689<2147483647;omega⟩,⟨782658534,by change 782658534<2147483647;omega⟩,⟨1705270609,by change 1705270609<2147483647;omega⟩]
theorem rawCell02 : (raw.drop 32).take 16=cell02.val := by
  simp only [raw,JFz_Scan53.data,JFz_Scan53.j00,JFz_Scan53.j01,JFz_Scan53.j02,JFz_Scan53.j03,JFz_Scan53.j04,JFz_Scan53.j05,JFz_Scan53.j06,JFz_Scan53.j07,JFz_Scan53.j08,JFz_Scan53.j09,JFz_Scan53.j10,JFz_Scan53.j11,JFz_Scan53.j12,JFz_Scan53.b00_length,JFz_Scan53.b01_length,JFz_Scan53.b02_length,JFz_Scan53.b03_length,JFz_Scan53.b04_length,JFz_Scan53.b05_length,JFz_Scan53.b06_length,JFz_Scan53.b07_length,JFz_Scan53.b08_length,JFz_Scan53.b09_length,JFz_Scan53.b10_length,JFz_Scan53.b11_length,JFz_Scan53.b12_length,JFz_Scan53.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell02
theorem encoded02 : CandidateParserByteOrder.arrayBytes16 cell02=encodeQM31LE limbs02 := by
  funext i
  fin_cases i <;> rfl
theorem parser02 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell02)=
    ok (some ⟨⟨2062488125#u32,194424689#u32⟩,⟨782658534#u32,1705270609#u32⟩⟩) :=
  JFr_EncodedCell.parser cell02 limbs02 encoded02
#print axioms encoded02
#print axioms parser02
def cell03 : Array U8 16#usize := ⟨[106#u8,241#u8,128#u8,71#u8,143#u8,233#u8,94#u8,8#u8,222#u8,57#u8,192#u8,49#u8,138#u8,31#u8,149#u8,119#u8],by rfl⟩
def limbs03 : QM31Limbs := ![⟨1199632746,by change 1199632746<2147483647;omega⟩,⟨140437903,by change 140437903<2147483647;omega⟩,⟨834681310,by change 834681310<2147483647;omega⟩,⟨2006261642,by change 2006261642<2147483647;omega⟩]
theorem rawCell03 : (raw.drop 48).take 16=cell03.val := by
  simp only [raw,JFz_Scan53.data,JFz_Scan53.j00,JFz_Scan53.j01,JFz_Scan53.j02,JFz_Scan53.j03,JFz_Scan53.j04,JFz_Scan53.j05,JFz_Scan53.j06,JFz_Scan53.j07,JFz_Scan53.j08,JFz_Scan53.j09,JFz_Scan53.j10,JFz_Scan53.j11,JFz_Scan53.j12,JFz_Scan53.b00_length,JFz_Scan53.b01_length,JFz_Scan53.b02_length,JFz_Scan53.b03_length,JFz_Scan53.b04_length,JFz_Scan53.b05_length,JFz_Scan53.b06_length,JFz_Scan53.b07_length,JFz_Scan53.b08_length,JFz_Scan53.b09_length,JFz_Scan53.b10_length,JFz_Scan53.b11_length,JFz_Scan53.b12_length,JFz_Scan53.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell03
theorem encoded03 : CandidateParserByteOrder.arrayBytes16 cell03=encodeQM31LE limbs03 := by
  funext i
  fin_cases i <;> rfl
theorem parser03 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell03)=
    ok (some ⟨⟨1199632746#u32,140437903#u32⟩,⟨834681310#u32,2006261642#u32⟩⟩) :=
  JFr_EncodedCell.parser cell03 limbs03 encoded03
#print axioms encoded03
#print axioms parser03
def cell04 : Array U8 16#usize := ⟨[71#u8,80#u8,252#u8,83#u8,89#u8,45#u8,53#u8,23#u8,143#u8,40#u8,241#u8,58#u8,145#u8,142#u8,163#u8,34#u8],by rfl⟩
def limbs04 : QM31Limbs := ![⟨1409044551,by change 1409044551<2147483647;omega⟩,⟨389360985,by change 389360985<2147483647;omega⟩,⟨988883087,by change 988883087<2147483647;omega⟩,⟨581144209,by change 581144209<2147483647;omega⟩]
theorem rawCell04 : (raw.drop 64).take 16=cell04.val := by
  simp only [raw,JFz_Scan53.data,JFz_Scan53.j00,JFz_Scan53.j01,JFz_Scan53.j02,JFz_Scan53.j03,JFz_Scan53.j04,JFz_Scan53.j05,JFz_Scan53.j06,JFz_Scan53.j07,JFz_Scan53.j08,JFz_Scan53.j09,JFz_Scan53.j10,JFz_Scan53.j11,JFz_Scan53.j12,JFz_Scan53.b00_length,JFz_Scan53.b01_length,JFz_Scan53.b02_length,JFz_Scan53.b03_length,JFz_Scan53.b04_length,JFz_Scan53.b05_length,JFz_Scan53.b06_length,JFz_Scan53.b07_length,JFz_Scan53.b08_length,JFz_Scan53.b09_length,JFz_Scan53.b10_length,JFz_Scan53.b11_length,JFz_Scan53.b12_length,JFz_Scan53.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell04
theorem encoded04 : CandidateParserByteOrder.arrayBytes16 cell04=encodeQM31LE limbs04 := by
  funext i
  fin_cases i <;> rfl
theorem parser04 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell04)=
    ok (some ⟨⟨1409044551#u32,389360985#u32⟩,⟨988883087#u32,581144209#u32⟩⟩) :=
  JFr_EncodedCell.parser cell04 limbs04 encoded04
#print axioms encoded04
#print axioms parser04
def cell05 : Array U8 16#usize := ⟨[163#u8,6#u8,73#u8,63#u8,129#u8,183#u8,146#u8,87#u8,145#u8,216#u8,61#u8,11#u8,173#u8,123#u8,40#u8,78#u8],by rfl⟩
def limbs05 : QM31Limbs := ![⟨1061750435,by change 1061750435<2147483647;omega⟩,⟨1469233025,by change 1469233025<2147483647;omega⟩,⟨188602513,by change 188602513<2147483647;omega⟩,⟨1311275949,by change 1311275949<2147483647;omega⟩]
theorem rawCell05 : (raw.drop 80).take 16=cell05.val := by
  simp only [raw,JFz_Scan53.data,JFz_Scan53.j00,JFz_Scan53.j01,JFz_Scan53.j02,JFz_Scan53.j03,JFz_Scan53.j04,JFz_Scan53.j05,JFz_Scan53.j06,JFz_Scan53.j07,JFz_Scan53.j08,JFz_Scan53.j09,JFz_Scan53.j10,JFz_Scan53.j11,JFz_Scan53.j12,JFz_Scan53.b00_length,JFz_Scan53.b01_length,JFz_Scan53.b02_length,JFz_Scan53.b03_length,JFz_Scan53.b04_length,JFz_Scan53.b05_length,JFz_Scan53.b06_length,JFz_Scan53.b07_length,JFz_Scan53.b08_length,JFz_Scan53.b09_length,JFz_Scan53.b10_length,JFz_Scan53.b11_length,JFz_Scan53.b12_length,JFz_Scan53.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell05
theorem encoded05 : CandidateParserByteOrder.arrayBytes16 cell05=encodeQM31LE limbs05 := by
  funext i
  fin_cases i <;> rfl
theorem parser05 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell05)=
    ok (some ⟨⟨1061750435#u32,1469233025#u32⟩,⟨188602513#u32,1311275949#u32⟩⟩) :=
  JFr_EncodedCell.parser cell05 limbs05 encoded05
#print axioms encoded05
#print axioms parser05
def cell06 : Array U8 16#usize := ⟨[104#u8,122#u8,200#u8,6#u8,150#u8,48#u8,126#u8,96#u8,36#u8,139#u8,174#u8,99#u8,226#u8,212#u8,206#u8,38#u8],by rfl⟩
def limbs06 : QM31Limbs := ![⟨113801832,by change 113801832<2147483647;omega⟩,⟨1618882710,by change 1618882710<2147483647;omega⟩,⟨1672383268,by change 1672383268<2147483647;omega⟩,⟨651089122,by change 651089122<2147483647;omega⟩]
theorem rawCell06 : (raw.drop 96).take 16=cell06.val := by
  simp only [raw,JFz_Scan53.data,JFz_Scan53.j00,JFz_Scan53.j01,JFz_Scan53.j02,JFz_Scan53.j03,JFz_Scan53.j04,JFz_Scan53.j05,JFz_Scan53.j06,JFz_Scan53.j07,JFz_Scan53.j08,JFz_Scan53.j09,JFz_Scan53.j10,JFz_Scan53.j11,JFz_Scan53.j12,JFz_Scan53.b00_length,JFz_Scan53.b01_length,JFz_Scan53.b02_length,JFz_Scan53.b03_length,JFz_Scan53.b04_length,JFz_Scan53.b05_length,JFz_Scan53.b06_length,JFz_Scan53.b07_length,JFz_Scan53.b08_length,JFz_Scan53.b09_length,JFz_Scan53.b10_length,JFz_Scan53.b11_length,JFz_Scan53.b12_length,JFz_Scan53.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell06
theorem encoded06 : CandidateParserByteOrder.arrayBytes16 cell06=encodeQM31LE limbs06 := by
  funext i
  fin_cases i <;> rfl
theorem parser06 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell06)=
    ok (some ⟨⟨113801832#u32,1618882710#u32⟩,⟨1672383268#u32,651089122#u32⟩⟩) :=
  JFr_EncodedCell.parser cell06 limbs06 encoded06
#print axioms encoded06
#print axioms parser06
def cell07 : Array U8 16#usize := ⟨[25#u8,207#u8,102#u8,36#u8,49#u8,116#u8,34#u8,98#u8,224#u8,113#u8,178#u8,24#u8,160#u8,68#u8,101#u8,1#u8],by rfl⟩
def limbs07 : QM31Limbs := ![⟨610717465,by change 610717465<2147483647;omega⟩,⟨1646425137,by change 1646425137<2147483647;omega⟩,⟨414347744,by change 414347744<2147483647;omega⟩,⟨23413920,by change 23413920<2147483647;omega⟩]
theorem rawCell07 : (raw.drop 112).take 16=cell07.val := by
  simp only [raw,JFz_Scan53.data,JFz_Scan53.j00,JFz_Scan53.j01,JFz_Scan53.j02,JFz_Scan53.j03,JFz_Scan53.j04,JFz_Scan53.j05,JFz_Scan53.j06,JFz_Scan53.j07,JFz_Scan53.j08,JFz_Scan53.j09,JFz_Scan53.j10,JFz_Scan53.j11,JFz_Scan53.j12,JFz_Scan53.b00_length,JFz_Scan53.b01_length,JFz_Scan53.b02_length,JFz_Scan53.b03_length,JFz_Scan53.b04_length,JFz_Scan53.b05_length,JFz_Scan53.b06_length,JFz_Scan53.b07_length,JFz_Scan53.b08_length,JFz_Scan53.b09_length,JFz_Scan53.b10_length,JFz_Scan53.b11_length,JFz_Scan53.b12_length,JFz_Scan53.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell07
theorem encoded07 : CandidateParserByteOrder.arrayBytes16 cell07=encodeQM31LE limbs07 := by
  funext i
  fin_cases i <;> rfl
theorem parser07 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell07)=
    ok (some ⟨⟨610717465#u32,1646425137#u32⟩,⟨414347744#u32,23413920#u32⟩⟩) :=
  JFr_EncodedCell.parser cell07 limbs07 encoded07
#print axioms encoded07
#print axioms parser07
def cell08 : Array U8 16#usize := ⟨[214#u8,170#u8,131#u8,51#u8,185#u8,194#u8,138#u8,15#u8,54#u8,97#u8,125#u8,18#u8,200#u8,111#u8,69#u8,25#u8],by rfl⟩
def limbs08 : QM31Limbs := ![⟨864266966,by change 864266966<2147483647;omega⟩,⟨260752057,by change 260752057<2147483647;omega⟩,⟨310206774,by change 310206774<2147483647;omega⟩,⟨423981000,by change 423981000<2147483647;omega⟩]
theorem rawCell08 : (raw.drop 128).take 16=cell08.val := by
  simp only [raw,JFz_Scan53.data,JFz_Scan53.j00,JFz_Scan53.j01,JFz_Scan53.j02,JFz_Scan53.j03,JFz_Scan53.j04,JFz_Scan53.j05,JFz_Scan53.j06,JFz_Scan53.j07,JFz_Scan53.j08,JFz_Scan53.j09,JFz_Scan53.j10,JFz_Scan53.j11,JFz_Scan53.j12,JFz_Scan53.b00_length,JFz_Scan53.b01_length,JFz_Scan53.b02_length,JFz_Scan53.b03_length,JFz_Scan53.b04_length,JFz_Scan53.b05_length,JFz_Scan53.b06_length,JFz_Scan53.b07_length,JFz_Scan53.b08_length,JFz_Scan53.b09_length,JFz_Scan53.b10_length,JFz_Scan53.b11_length,JFz_Scan53.b12_length,JFz_Scan53.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell08
theorem encoded08 : CandidateParserByteOrder.arrayBytes16 cell08=encodeQM31LE limbs08 := by
  funext i
  fin_cases i <;> rfl
theorem parser08 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell08)=
    ok (some ⟨⟨864266966#u32,260752057#u32⟩,⟨310206774#u32,423981000#u32⟩⟩) :=
  JFr_EncodedCell.parser cell08 limbs08 encoded08
#print axioms encoded08
#print axioms parser08
def cell09 : Array U8 16#usize := ⟨[91#u8,5#u8,206#u8,28#u8,90#u8,219#u8,238#u8,7#u8,122#u8,242#u8,116#u8,69#u8,1#u8,35#u8,138#u8,7#u8],by rfl⟩
def limbs09 : QM31Limbs := ![⟨483263835,by change 483263835<2147483647;omega⟩,⟨133094234,by change 133094234<2147483647;omega⟩,⟨1165292154,by change 1165292154<2147483647;omega⟩,⟨126493441,by change 126493441<2147483647;omega⟩]
theorem rawCell09 : (raw.drop 144).take 16=cell09.val := by
  simp only [raw,JFz_Scan53.data,JFz_Scan53.j00,JFz_Scan53.j01,JFz_Scan53.j02,JFz_Scan53.j03,JFz_Scan53.j04,JFz_Scan53.j05,JFz_Scan53.j06,JFz_Scan53.j07,JFz_Scan53.j08,JFz_Scan53.j09,JFz_Scan53.j10,JFz_Scan53.j11,JFz_Scan53.j12,JFz_Scan53.b00_length,JFz_Scan53.b01_length,JFz_Scan53.b02_length,JFz_Scan53.b03_length,JFz_Scan53.b04_length,JFz_Scan53.b05_length,JFz_Scan53.b06_length,JFz_Scan53.b07_length,JFz_Scan53.b08_length,JFz_Scan53.b09_length,JFz_Scan53.b10_length,JFz_Scan53.b11_length,JFz_Scan53.b12_length,JFz_Scan53.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell09
theorem encoded09 : CandidateParserByteOrder.arrayBytes16 cell09=encodeQM31LE limbs09 := by
  funext i
  fin_cases i <;> rfl
theorem parser09 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell09)=
    ok (some ⟨⟨483263835#u32,133094234#u32⟩,⟨1165292154#u32,126493441#u32⟩⟩) :=
  JFr_EncodedCell.parser cell09 limbs09 encoded09
#print axioms encoded09
#print axioms parser09
def cell10 : Array U8 16#usize := ⟨[241#u8,26#u8,238#u8,102#u8,20#u8,90#u8,50#u8,73#u8,39#u8,187#u8,255#u8,5#u8,182#u8,168#u8,149#u8,120#u8],by rfl⟩
def limbs10 : QM31Limbs := ![⟨1726880497,by change 1726880497<2147483647;omega⟩,⟨1228036628,by change 1228036628<2147483647;omega⟩,⟨100645671,by change 100645671<2147483647;omega⟩,⟨2023073974,by change 2023073974<2147483647;omega⟩]
theorem rawCell10 : (raw.drop 160).take 16=cell10.val := by
  simp only [raw,JFz_Scan53.data,JFz_Scan53.j00,JFz_Scan53.j01,JFz_Scan53.j02,JFz_Scan53.j03,JFz_Scan53.j04,JFz_Scan53.j05,JFz_Scan53.j06,JFz_Scan53.j07,JFz_Scan53.j08,JFz_Scan53.j09,JFz_Scan53.j10,JFz_Scan53.j11,JFz_Scan53.j12,JFz_Scan53.b00_length,JFz_Scan53.b01_length,JFz_Scan53.b02_length,JFz_Scan53.b03_length,JFz_Scan53.b04_length,JFz_Scan53.b05_length,JFz_Scan53.b06_length,JFz_Scan53.b07_length,JFz_Scan53.b08_length,JFz_Scan53.b09_length,JFz_Scan53.b10_length,JFz_Scan53.b11_length,JFz_Scan53.b12_length,JFz_Scan53.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell10
theorem encoded10 : CandidateParserByteOrder.arrayBytes16 cell10=encodeQM31LE limbs10 := by
  funext i
  fin_cases i <;> rfl
theorem parser10 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell10)=
    ok (some ⟨⟨1726880497#u32,1228036628#u32⟩,⟨100645671#u32,2023073974#u32⟩⟩) :=
  JFr_EncodedCell.parser cell10 limbs10 encoded10
#print axioms encoded10
#print axioms parser10
def cell11 : Array U8 16#usize := ⟨[236#u8,202#u8,175#u8,0#u8,206#u8,49#u8,131#u8,52#u8,241#u8,99#u8,60#u8,2#u8,134#u8,221#u8,164#u8,74#u8],by rfl⟩
def limbs11 : QM31Limbs := ![⟨11520748,by change 11520748<2147483647;omega⟩,⟨881013198,by change 881013198<2147483647;omega⟩,⟨37512177,by change 37512177<2147483647;omega⟩,⟨1252318598,by change 1252318598<2147483647;omega⟩]
theorem rawCell11 : (raw.drop 176).take 16=cell11.val := by
  simp only [raw,JFz_Scan53.data,JFz_Scan53.j00,JFz_Scan53.j01,JFz_Scan53.j02,JFz_Scan53.j03,JFz_Scan53.j04,JFz_Scan53.j05,JFz_Scan53.j06,JFz_Scan53.j07,JFz_Scan53.j08,JFz_Scan53.j09,JFz_Scan53.j10,JFz_Scan53.j11,JFz_Scan53.j12,JFz_Scan53.b00_length,JFz_Scan53.b01_length,JFz_Scan53.b02_length,JFz_Scan53.b03_length,JFz_Scan53.b04_length,JFz_Scan53.b05_length,JFz_Scan53.b06_length,JFz_Scan53.b07_length,JFz_Scan53.b08_length,JFz_Scan53.b09_length,JFz_Scan53.b10_length,JFz_Scan53.b11_length,JFz_Scan53.b12_length,JFz_Scan53.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell11
theorem encoded11 : CandidateParserByteOrder.arrayBytes16 cell11=encodeQM31LE limbs11 := by
  funext i
  fin_cases i <;> rfl
theorem parser11 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell11)=
    ok (some ⟨⟨11520748#u32,881013198#u32⟩,⟨37512177#u32,1252318598#u32⟩⟩) :=
  JFr_EncodedCell.parser cell11 limbs11 encoded11
#print axioms encoded11
#print axioms parser11
def cell12 : Array U8 16#usize := ⟨[237#u8,202#u8,200#u8,100#u8,143#u8,88#u8,181#u8,53#u8,237#u8,139#u8,140#u8,69#u8,10#u8,110#u8,2#u8,15#u8],by rfl⟩
def limbs12 : QM31Limbs := ![⟨1690880749,by change 1690880749<2147483647;omega⟩,⟨901077135,by change 901077135<2147483647;omega⟩,⟨1166838765,by change 1166838765<2147483647;omega⟩,⟨251817482,by change 251817482<2147483647;omega⟩]
theorem rawCell12 : (raw.drop 192).take 16=cell12.val := by
  simp only [raw,JFz_Scan53.data,JFz_Scan53.j00,JFz_Scan53.j01,JFz_Scan53.j02,JFz_Scan53.j03,JFz_Scan53.j04,JFz_Scan53.j05,JFz_Scan53.j06,JFz_Scan53.j07,JFz_Scan53.j08,JFz_Scan53.j09,JFz_Scan53.j10,JFz_Scan53.j11,JFz_Scan53.j12,JFz_Scan53.b00_length,JFz_Scan53.b01_length,JFz_Scan53.b02_length,JFz_Scan53.b03_length,JFz_Scan53.b04_length,JFz_Scan53.b05_length,JFz_Scan53.b06_length,JFz_Scan53.b07_length,JFz_Scan53.b08_length,JFz_Scan53.b09_length,JFz_Scan53.b10_length,JFz_Scan53.b11_length,JFz_Scan53.b12_length,JFz_Scan53.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell12
theorem encoded12 : CandidateParserByteOrder.arrayBytes16 cell12=encodeQM31LE limbs12 := by
  funext i
  fin_cases i <;> rfl
theorem parser12 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell12)=
    ok (some ⟨⟨1690880749#u32,901077135#u32⟩,⟨1166838765#u32,251817482#u32⟩⟩) :=
  JFr_EncodedCell.parser cell12 limbs12 encoded12
#print axioms encoded12
#print axioms parser12
def cell13 : Array U8 16#usize := ⟨[126#u8,201#u8,208#u8,44#u8,211#u8,125#u8,2#u8,55#u8,194#u8,30#u8,195#u8,10#u8,128#u8,251#u8,223#u8,79#u8],by rfl⟩
def limbs13 : QM31Limbs := ![⟨751880574,by change 751880574<2147483647;omega⟩,⟨922910163,by change 922910163<2147483647;omega⟩,⟨180559554,by change 180559554<2147483647;omega⟩,⟨1340078976,by change 1340078976<2147483647;omega⟩]
theorem rawCell13 : (raw.drop 208).take 16=cell13.val := by
  simp only [raw,JFz_Scan53.data,JFz_Scan53.j00,JFz_Scan53.j01,JFz_Scan53.j02,JFz_Scan53.j03,JFz_Scan53.j04,JFz_Scan53.j05,JFz_Scan53.j06,JFz_Scan53.j07,JFz_Scan53.j08,JFz_Scan53.j09,JFz_Scan53.j10,JFz_Scan53.j11,JFz_Scan53.j12,JFz_Scan53.b00_length,JFz_Scan53.b01_length,JFz_Scan53.b02_length,JFz_Scan53.b03_length,JFz_Scan53.b04_length,JFz_Scan53.b05_length,JFz_Scan53.b06_length,JFz_Scan53.b07_length,JFz_Scan53.b08_length,JFz_Scan53.b09_length,JFz_Scan53.b10_length,JFz_Scan53.b11_length,JFz_Scan53.b12_length,JFz_Scan53.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell13
theorem encoded13 : CandidateParserByteOrder.arrayBytes16 cell13=encodeQM31LE limbs13 := by
  funext i
  fin_cases i <;> rfl
theorem parser13 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell13)=
    ok (some ⟨⟨751880574#u32,922910163#u32⟩,⟨180559554#u32,1340078976#u32⟩⟩) :=
  JFr_EncodedCell.parser cell13 limbs13 encoded13
#print axioms encoded13
#print axioms parser13
def cell14 : Array U8 16#usize := ⟨[198#u8,120#u8,195#u8,60#u8,42#u8,78#u8,149#u8,67#u8,201#u8,22#u8,90#u8,72#u8,114#u8,171#u8,148#u8,70#u8],by rfl⟩
def limbs14 : QM31Limbs := ![⟨1019443398,by change 1019443398<2147483647;omega⟩,⟨1133858346,by change 1133858346<2147483647;omega⟩,⟨1213863625,by change 1213863625<2147483647;omega⟩,⟨1184148338,by change 1184148338<2147483647;omega⟩]
theorem rawCell14 : (raw.drop 224).take 16=cell14.val := by
  simp only [raw,JFz_Scan53.data,JFz_Scan53.j00,JFz_Scan53.j01,JFz_Scan53.j02,JFz_Scan53.j03,JFz_Scan53.j04,JFz_Scan53.j05,JFz_Scan53.j06,JFz_Scan53.j07,JFz_Scan53.j08,JFz_Scan53.j09,JFz_Scan53.j10,JFz_Scan53.j11,JFz_Scan53.j12,JFz_Scan53.b00_length,JFz_Scan53.b01_length,JFz_Scan53.b02_length,JFz_Scan53.b03_length,JFz_Scan53.b04_length,JFz_Scan53.b05_length,JFz_Scan53.b06_length,JFz_Scan53.b07_length,JFz_Scan53.b08_length,JFz_Scan53.b09_length,JFz_Scan53.b10_length,JFz_Scan53.b11_length,JFz_Scan53.b12_length,JFz_Scan53.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell14
theorem encoded14 : CandidateParserByteOrder.arrayBytes16 cell14=encodeQM31LE limbs14 := by
  funext i
  fin_cases i <;> rfl
theorem parser14 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell14)=
    ok (some ⟨⟨1019443398#u32,1133858346#u32⟩,⟨1213863625#u32,1184148338#u32⟩⟩) :=
  JFr_EncodedCell.parser cell14 limbs14 encoded14
#print axioms encoded14
#print axioms parser14
def cell15 : Array U8 16#usize := ⟨[201#u8,239#u8,112#u8,76#u8,224#u8,84#u8,145#u8,94#u8,242#u8,180#u8,13#u8,29#u8,141#u8,60#u8,187#u8,40#u8],by rfl⟩
def limbs15 : QM31Limbs := ![⟨1282469833,by change 1282469833<2147483647;omega⟩,⟨1586582752,by change 1586582752<2147483647;omega⟩,⟨487437554,by change 487437554<2147483647;omega⟩,⟨683359373,by change 683359373<2147483647;omega⟩]
theorem rawCell15 : (raw.drop 240).take 16=cell15.val := by
  simp only [raw,JFz_Scan53.data,JFz_Scan53.j00,JFz_Scan53.j01,JFz_Scan53.j02,JFz_Scan53.j03,JFz_Scan53.j04,JFz_Scan53.j05,JFz_Scan53.j06,JFz_Scan53.j07,JFz_Scan53.j08,JFz_Scan53.j09,JFz_Scan53.j10,JFz_Scan53.j11,JFz_Scan53.j12,JFz_Scan53.b00_length,JFz_Scan53.b01_length,JFz_Scan53.b02_length,JFz_Scan53.b03_length,JFz_Scan53.b04_length,JFz_Scan53.b05_length,JFz_Scan53.b06_length,JFz_Scan53.b07_length,JFz_Scan53.b08_length,JFz_Scan53.b09_length,JFz_Scan53.b10_length,JFz_Scan53.b11_length,JFz_Scan53.b12_length,JFz_Scan53.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell15
theorem encoded15 : CandidateParserByteOrder.arrayBytes16 cell15=encodeQM31LE limbs15 := by
  funext i
  fin_cases i <;> rfl
theorem parser15 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell15)=
    ok (some ⟨⟨1282469833#u32,1586582752#u32⟩,⟨487437554#u32,683359373#u32⟩⟩) :=
  JFr_EncodedCell.parser cell15 limbs15 encoded15
#print axioms encoded15
#print axioms parser15
def cell16 : Array U8 16#usize := ⟨[241#u8,39#u8,162#u8,88#u8,216#u8,49#u8,223#u8,9#u8,75#u8,199#u8,37#u8,4#u8,255#u8,208#u8,180#u8,77#u8],by rfl⟩
def limbs16 : QM31Limbs := ![⟨1487022065,by change 1487022065<2147483647;omega⟩,⟨165622232,by change 165622232<2147483647;omega⟩,⟨69584715,by change 69584715<2147483647;omega⟩,⟨1303695615,by change 1303695615<2147483647;omega⟩]
theorem rawCell16 : (raw.drop 256).take 16=cell16.val := by
  simp only [raw,JFz_Scan53.data,JFz_Scan53.j00,JFz_Scan53.j01,JFz_Scan53.j02,JFz_Scan53.j03,JFz_Scan53.j04,JFz_Scan53.j05,JFz_Scan53.j06,JFz_Scan53.j07,JFz_Scan53.j08,JFz_Scan53.j09,JFz_Scan53.j10,JFz_Scan53.j11,JFz_Scan53.j12,JFz_Scan53.b00_length,JFz_Scan53.b01_length,JFz_Scan53.b02_length,JFz_Scan53.b03_length,JFz_Scan53.b04_length,JFz_Scan53.b05_length,JFz_Scan53.b06_length,JFz_Scan53.b07_length,JFz_Scan53.b08_length,JFz_Scan53.b09_length,JFz_Scan53.b10_length,JFz_Scan53.b11_length,JFz_Scan53.b12_length,JFz_Scan53.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell16
theorem encoded16 : CandidateParserByteOrder.arrayBytes16 cell16=encodeQM31LE limbs16 := by
  funext i
  fin_cases i <;> rfl
theorem parser16 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell16)=
    ok (some ⟨⟨1487022065#u32,165622232#u32⟩,⟨69584715#u32,1303695615#u32⟩⟩) :=
  JFr_EncodedCell.parser cell16 limbs16 encoded16
#print axioms encoded16
#print axioms parser16
def cell17 : Array U8 16#usize := ⟨[201#u8,196#u8,90#u8,28#u8,113#u8,78#u8,227#u8,82#u8,56#u8,50#u8,34#u8,84#u8,27#u8,137#u8,145#u8,91#u8],by rfl⟩
def limbs17 : QM31Limbs := ![⟨475710665,by change 475710665<2147483647;omega⟩,⟨1390628465,by change 1390628465<2147483647;omega⟩,⟨1411527224,by change 1411527224<2147483647;omega⟩,⟨1536264475,by change 1536264475<2147483647;omega⟩]
theorem rawCell17 : (raw.drop 272).take 16=cell17.val := by
  simp only [raw,JFz_Scan53.data,JFz_Scan53.j00,JFz_Scan53.j01,JFz_Scan53.j02,JFz_Scan53.j03,JFz_Scan53.j04,JFz_Scan53.j05,JFz_Scan53.j06,JFz_Scan53.j07,JFz_Scan53.j08,JFz_Scan53.j09,JFz_Scan53.j10,JFz_Scan53.j11,JFz_Scan53.j12,JFz_Scan53.b00_length,JFz_Scan53.b01_length,JFz_Scan53.b02_length,JFz_Scan53.b03_length,JFz_Scan53.b04_length,JFz_Scan53.b05_length,JFz_Scan53.b06_length,JFz_Scan53.b07_length,JFz_Scan53.b08_length,JFz_Scan53.b09_length,JFz_Scan53.b10_length,JFz_Scan53.b11_length,JFz_Scan53.b12_length,JFz_Scan53.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell17
theorem encoded17 : CandidateParserByteOrder.arrayBytes16 cell17=encodeQM31LE limbs17 := by
  funext i
  fin_cases i <;> rfl
theorem parser17 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell17)=
    ok (some ⟨⟨475710665#u32,1390628465#u32⟩,⟨1411527224#u32,1536264475#u32⟩⟩) :=
  JFr_EncodedCell.parser cell17 limbs17 encoded17
#print axioms encoded17
#print axioms parser17
def cell18 : Array U8 16#usize := ⟨[71#u8,125#u8,226#u8,68#u8,150#u8,10#u8,147#u8,23#u8,144#u8,248#u8,163#u8,77#u8,133#u8,104#u8,254#u8,57#u8],by rfl⟩
def limbs18 : QM31Limbs := ![⟨1155693895,by change 1155693895<2147483647;omega⟩,⟨395512470,by change 395512470<2147483647;omega⟩,⟨1302591632,by change 1302591632<2147483647;omega⟩,⟨972974213,by change 972974213<2147483647;omega⟩]
theorem rawCell18 : (raw.drop 288).take 16=cell18.val := by
  simp only [raw,JFz_Scan53.data,JFz_Scan53.j00,JFz_Scan53.j01,JFz_Scan53.j02,JFz_Scan53.j03,JFz_Scan53.j04,JFz_Scan53.j05,JFz_Scan53.j06,JFz_Scan53.j07,JFz_Scan53.j08,JFz_Scan53.j09,JFz_Scan53.j10,JFz_Scan53.j11,JFz_Scan53.j12,JFz_Scan53.b00_length,JFz_Scan53.b01_length,JFz_Scan53.b02_length,JFz_Scan53.b03_length,JFz_Scan53.b04_length,JFz_Scan53.b05_length,JFz_Scan53.b06_length,JFz_Scan53.b07_length,JFz_Scan53.b08_length,JFz_Scan53.b09_length,JFz_Scan53.b10_length,JFz_Scan53.b11_length,JFz_Scan53.b12_length,JFz_Scan53.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell18
theorem encoded18 : CandidateParserByteOrder.arrayBytes16 cell18=encodeQM31LE limbs18 := by
  funext i
  fin_cases i <;> rfl
theorem parser18 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell18)=
    ok (some ⟨⟨1155693895#u32,395512470#u32⟩,⟨1302591632#u32,972974213#u32⟩⟩) :=
  JFr_EncodedCell.parser cell18 limbs18 encoded18
#print axioms encoded18
#print axioms parser18
def cell19 : Array U8 16#usize := ⟨[22#u8,35#u8,235#u8,124#u8,198#u8,36#u8,254#u8,46#u8,117#u8,234#u8,12#u8,4#u8,15#u8,9#u8,115#u8,25#u8],by rfl⟩
def limbs19 : QM31Limbs := ![⟨2095784726,by change 2095784726<2147483647;omega⟩,⟨788407494,by change 788407494<2147483647;omega⟩,⟨67955317,by change 67955317<2147483647;omega⟩,⟨426969359,by change 426969359<2147483647;omega⟩]
theorem rawCell19 : (raw.drop 304).take 16=cell19.val := by
  simp only [raw,JFz_Scan53.data,JFz_Scan53.j00,JFz_Scan53.j01,JFz_Scan53.j02,JFz_Scan53.j03,JFz_Scan53.j04,JFz_Scan53.j05,JFz_Scan53.j06,JFz_Scan53.j07,JFz_Scan53.j08,JFz_Scan53.j09,JFz_Scan53.j10,JFz_Scan53.j11,JFz_Scan53.j12,JFz_Scan53.b00_length,JFz_Scan53.b01_length,JFz_Scan53.b02_length,JFz_Scan53.b03_length,JFz_Scan53.b04_length,JFz_Scan53.b05_length,JFz_Scan53.b06_length,JFz_Scan53.b07_length,JFz_Scan53.b08_length,JFz_Scan53.b09_length,JFz_Scan53.b10_length,JFz_Scan53.b11_length,JFz_Scan53.b12_length,JFz_Scan53.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell19
theorem encoded19 : CandidateParserByteOrder.arrayBytes16 cell19=encodeQM31LE limbs19 := by
  funext i
  fin_cases i <;> rfl
theorem parser19 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell19)=
    ok (some ⟨⟨2095784726#u32,788407494#u32⟩,⟨67955317#u32,426969359#u32⟩⟩) :=
  JFr_EncodedCell.parser cell19 limbs19 encoded19
#print axioms encoded19
#print axioms parser19
def cell20 : Array U8 16#usize := ⟨[187#u8,165#u8,89#u8,45#u8,249#u8,193#u8,173#u8,35#u8,84#u8,232#u8,101#u8,127#u8,49#u8,36#u8,23#u8,68#u8],by rfl⟩
def limbs20 : QM31Limbs := ![⟨760849851,by change 760849851<2147483647;omega⟩,⟨598589945,by change 598589945<2147483647;omega⟩,⟨2137385044,by change 2137385044<2147483647;omega⟩,⟨1142367281,by change 1142367281<2147483647;omega⟩]
theorem rawCell20 : (raw.drop 320).take 16=cell20.val := by
  simp only [raw,JFz_Scan53.data,JFz_Scan53.j00,JFz_Scan53.j01,JFz_Scan53.j02,JFz_Scan53.j03,JFz_Scan53.j04,JFz_Scan53.j05,JFz_Scan53.j06,JFz_Scan53.j07,JFz_Scan53.j08,JFz_Scan53.j09,JFz_Scan53.j10,JFz_Scan53.j11,JFz_Scan53.j12,JFz_Scan53.b00_length,JFz_Scan53.b01_length,JFz_Scan53.b02_length,JFz_Scan53.b03_length,JFz_Scan53.b04_length,JFz_Scan53.b05_length,JFz_Scan53.b06_length,JFz_Scan53.b07_length,JFz_Scan53.b08_length,JFz_Scan53.b09_length,JFz_Scan53.b10_length,JFz_Scan53.b11_length,JFz_Scan53.b12_length,JFz_Scan53.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell20
theorem encoded20 : CandidateParserByteOrder.arrayBytes16 cell20=encodeQM31LE limbs20 := by
  funext i
  fin_cases i <;> rfl
theorem parser20 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell20)=
    ok (some ⟨⟨760849851#u32,598589945#u32⟩,⟨2137385044#u32,1142367281#u32⟩⟩) :=
  JFr_EncodedCell.parser cell20 limbs20 encoded20
#print axioms encoded20
#print axioms parser20
def cell21 : Array U8 16#usize := ⟨[244#u8,121#u8,251#u8,15#u8,47#u8,195#u8,162#u8,19#u8,73#u8,108#u8,120#u8,63#u8,121#u8,42#u8,119#u8,6#u8],by rfl⟩
def limbs21 : QM31Limbs := ![⟨268138996,by change 268138996<2147483647;omega⟩,⟨329433903,by change 329433903<2147483647;omega⟩,⟨1064856649,by change 1064856649<2147483647;omega⟩,⟨108472953,by change 108472953<2147483647;omega⟩]
theorem rawCell21 : (raw.drop 336).take 16=cell21.val := by
  simp only [raw,JFz_Scan53.data,JFz_Scan53.j00,JFz_Scan53.j01,JFz_Scan53.j02,JFz_Scan53.j03,JFz_Scan53.j04,JFz_Scan53.j05,JFz_Scan53.j06,JFz_Scan53.j07,JFz_Scan53.j08,JFz_Scan53.j09,JFz_Scan53.j10,JFz_Scan53.j11,JFz_Scan53.j12,JFz_Scan53.b00_length,JFz_Scan53.b01_length,JFz_Scan53.b02_length,JFz_Scan53.b03_length,JFz_Scan53.b04_length,JFz_Scan53.b05_length,JFz_Scan53.b06_length,JFz_Scan53.b07_length,JFz_Scan53.b08_length,JFz_Scan53.b09_length,JFz_Scan53.b10_length,JFz_Scan53.b11_length,JFz_Scan53.b12_length,JFz_Scan53.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell21
theorem encoded21 : CandidateParserByteOrder.arrayBytes16 cell21=encodeQM31LE limbs21 := by
  funext i
  fin_cases i <;> rfl
theorem parser21 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell21)=
    ok (some ⟨⟨268138996#u32,329433903#u32⟩,⟨1064856649#u32,108472953#u32⟩⟩) :=
  JFr_EncodedCell.parser cell21 limbs21 encoded21
#print axioms encoded21
#print axioms parser21
def cell22 : Array U8 16#usize := ⟨[98#u8,79#u8,116#u8,14#u8,170#u8,186#u8,92#u8,118#u8,17#u8,111#u8,199#u8,4#u8,24#u8,176#u8,110#u8,76#u8],by rfl⟩
def limbs22 : QM31Limbs := ![⟨242503522,by change 242503522<2147483647;omega⟩,⟨1985788586,by change 1985788586<2147483647;omega⟩,⟨80178961,by change 80178961<2147483647;omega⟩,⟨1282322456,by change 1282322456<2147483647;omega⟩]
theorem rawCell22 : (raw.drop 352).take 16=cell22.val := by
  simp only [raw,JFz_Scan53.data,JFz_Scan53.j00,JFz_Scan53.j01,JFz_Scan53.j02,JFz_Scan53.j03,JFz_Scan53.j04,JFz_Scan53.j05,JFz_Scan53.j06,JFz_Scan53.j07,JFz_Scan53.j08,JFz_Scan53.j09,JFz_Scan53.j10,JFz_Scan53.j11,JFz_Scan53.j12,JFz_Scan53.b00_length,JFz_Scan53.b01_length,JFz_Scan53.b02_length,JFz_Scan53.b03_length,JFz_Scan53.b04_length,JFz_Scan53.b05_length,JFz_Scan53.b06_length,JFz_Scan53.b07_length,JFz_Scan53.b08_length,JFz_Scan53.b09_length,JFz_Scan53.b10_length,JFz_Scan53.b11_length,JFz_Scan53.b12_length,JFz_Scan53.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell22
theorem encoded22 : CandidateParserByteOrder.arrayBytes16 cell22=encodeQM31LE limbs22 := by
  funext i
  fin_cases i <;> rfl
theorem parser22 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell22)=
    ok (some ⟨⟨242503522#u32,1985788586#u32⟩,⟨80178961#u32,1282322456#u32⟩⟩) :=
  JFr_EncodedCell.parser cell22 limbs22 encoded22
#print axioms encoded22
#print axioms parser22
def cell23 : Array U8 16#usize := ⟨[237#u8,247#u8,237#u8,5#u8,7#u8,25#u8,90#u8,83#u8,95#u8,208#u8,12#u8,40#u8,224#u8,216#u8,155#u8,33#u8],by rfl⟩
def limbs23 : QM31Limbs := ![⟨99481581,by change 99481581<2147483647;omega⟩,⟨1398413575,by change 1398413575<2147483647;omega⟩,⟨671928415,by change 671928415<2147483647;omega⟩,⟨563861728,by change 563861728<2147483647;omega⟩]
theorem rawCell23 : (raw.drop 368).take 16=cell23.val := by
  simp only [raw,JFz_Scan53.data,JFz_Scan53.j00,JFz_Scan53.j01,JFz_Scan53.j02,JFz_Scan53.j03,JFz_Scan53.j04,JFz_Scan53.j05,JFz_Scan53.j06,JFz_Scan53.j07,JFz_Scan53.j08,JFz_Scan53.j09,JFz_Scan53.j10,JFz_Scan53.j11,JFz_Scan53.j12,JFz_Scan53.b00_length,JFz_Scan53.b01_length,JFz_Scan53.b02_length,JFz_Scan53.b03_length,JFz_Scan53.b04_length,JFz_Scan53.b05_length,JFz_Scan53.b06_length,JFz_Scan53.b07_length,JFz_Scan53.b08_length,JFz_Scan53.b09_length,JFz_Scan53.b10_length,JFz_Scan53.b11_length,JFz_Scan53.b12_length,JFz_Scan53.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell23
theorem encoded23 : CandidateParserByteOrder.arrayBytes16 cell23=encodeQM31LE limbs23 := by
  funext i
  fin_cases i <;> rfl
theorem parser23 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell23)=
    ok (some ⟨⟨99481581#u32,1398413575#u32⟩,⟨671928415#u32,563861728#u32⟩⟩) :=
  JFr_EncodedCell.parser cell23 limbs23 encoded23
#print axioms encoded23
#print axioms parser23
def cell24 : Array U8 16#usize := ⟨[87#u8,185#u8,91#u8,85#u8,187#u8,55#u8,140#u8,105#u8,27#u8,181#u8,84#u8,125#u8,112#u8,101#u8,205#u8,45#u8],by rfl⟩
def limbs24 : QM31Limbs := ![⟨1432074583,by change 1432074583<2147483647;omega⟩,⟨1770796987,by change 1770796987<2147483647;omega⟩,⟨2102703387,by change 2102703387<2147483647;omega⟩,⟨768435568,by change 768435568<2147483647;omega⟩]
theorem rawCell24 : (raw.drop 384).take 16=cell24.val := by
  simp only [raw,JFz_Scan53.data,JFz_Scan53.j00,JFz_Scan53.j01,JFz_Scan53.j02,JFz_Scan53.j03,JFz_Scan53.j04,JFz_Scan53.j05,JFz_Scan53.j06,JFz_Scan53.j07,JFz_Scan53.j08,JFz_Scan53.j09,JFz_Scan53.j10,JFz_Scan53.j11,JFz_Scan53.j12,JFz_Scan53.b00_length,JFz_Scan53.b01_length,JFz_Scan53.b02_length,JFz_Scan53.b03_length,JFz_Scan53.b04_length,JFz_Scan53.b05_length,JFz_Scan53.b06_length,JFz_Scan53.b07_length,JFz_Scan53.b08_length,JFz_Scan53.b09_length,JFz_Scan53.b10_length,JFz_Scan53.b11_length,JFz_Scan53.b12_length,JFz_Scan53.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell24
theorem encoded24 : CandidateParserByteOrder.arrayBytes16 cell24=encodeQM31LE limbs24 := by
  funext i
  fin_cases i <;> rfl
theorem parser24 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell24)=
    ok (some ⟨⟨1432074583#u32,1770796987#u32⟩,⟨2102703387#u32,768435568#u32⟩⟩) :=
  JFr_EncodedCell.parser cell24 limbs24 encoded24
#print axioms encoded24
#print axioms parser24
def cell25 : Array U8 16#usize := ⟨[253#u8,16#u8,130#u8,70#u8,143#u8,156#u8,123#u8,55#u8,18#u8,98#u8,68#u8,85#u8,223#u8,217#u8,246#u8,87#u8],by rfl⟩
def limbs25 : QM31Limbs := ![⟨1182929149,by change 1182929149<2147483647;omega⟩,⟨930847887,by change 930847887<2147483647;omega⟩,⟨1430544914,by change 1430544914<2147483647;omega⟩,⟨1475795423,by change 1475795423<2147483647;omega⟩]
theorem rawCell25 : (raw.drop 400).take 16=cell25.val := by
  simp only [raw,JFz_Scan53.data,JFz_Scan53.j00,JFz_Scan53.j01,JFz_Scan53.j02,JFz_Scan53.j03,JFz_Scan53.j04,JFz_Scan53.j05,JFz_Scan53.j06,JFz_Scan53.j07,JFz_Scan53.j08,JFz_Scan53.j09,JFz_Scan53.j10,JFz_Scan53.j11,JFz_Scan53.j12,JFz_Scan53.b00_length,JFz_Scan53.b01_length,JFz_Scan53.b02_length,JFz_Scan53.b03_length,JFz_Scan53.b04_length,JFz_Scan53.b05_length,JFz_Scan53.b06_length,JFz_Scan53.b07_length,JFz_Scan53.b08_length,JFz_Scan53.b09_length,JFz_Scan53.b10_length,JFz_Scan53.b11_length,JFz_Scan53.b12_length,JFz_Scan53.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell25
theorem encoded25 : CandidateParserByteOrder.arrayBytes16 cell25=encodeQM31LE limbs25 := by
  funext i
  fin_cases i <;> rfl
theorem parser25 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell25)=
    ok (some ⟨⟨1182929149#u32,930847887#u32⟩,⟨1430544914#u32,1475795423#u32⟩⟩) :=
  JFr_EncodedCell.parser cell25 limbs25 encoded25
#print axioms encoded25
#print axioms parser25
def cell26 : Array U8 16#usize := ⟨[154#u8,147#u8,68#u8,69#u8,77#u8,64#u8,109#u8,85#u8,242#u8,104#u8,137#u8,84#u8,154#u8,126#u8,61#u8,62#u8],by rfl⟩
def limbs26 : QM31Limbs := ![⟨1162122138,by change 1162122138<2147483647;omega⟩,⟨1433223245,by change 1433223245<2147483647;omega⟩,⟨1418291442,by change 1418291442<2147483647;omega⟩,⟨1044217498,by change 1044217498<2147483647;omega⟩]
theorem rawCell26 : (raw.drop 416).take 16=cell26.val := by
  simp only [raw,JFz_Scan53.data,JFz_Scan53.j00,JFz_Scan53.j01,JFz_Scan53.j02,JFz_Scan53.j03,JFz_Scan53.j04,JFz_Scan53.j05,JFz_Scan53.j06,JFz_Scan53.j07,JFz_Scan53.j08,JFz_Scan53.j09,JFz_Scan53.j10,JFz_Scan53.j11,JFz_Scan53.j12,JFz_Scan53.b00_length,JFz_Scan53.b01_length,JFz_Scan53.b02_length,JFz_Scan53.b03_length,JFz_Scan53.b04_length,JFz_Scan53.b05_length,JFz_Scan53.b06_length,JFz_Scan53.b07_length,JFz_Scan53.b08_length,JFz_Scan53.b09_length,JFz_Scan53.b10_length,JFz_Scan53.b11_length,JFz_Scan53.b12_length,JFz_Scan53.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell26
theorem encoded26 : CandidateParserByteOrder.arrayBytes16 cell26=encodeQM31LE limbs26 := by
  funext i
  fin_cases i <;> rfl
theorem parser26 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell26)=
    ok (some ⟨⟨1162122138#u32,1433223245#u32⟩,⟨1418291442#u32,1044217498#u32⟩⟩) :=
  JFr_EncodedCell.parser cell26 limbs26 encoded26
#print axioms encoded26
#print axioms parser26
def cell27 : Array U8 16#usize := ⟨[21#u8,195#u8,51#u8,25#u8,168#u8,137#u8,154#u8,79#u8,245#u8,214#u8,109#u8,111#u8,224#u8,168#u8,36#u8,44#u8],by rfl⟩
def limbs27 : QM31Limbs := ![⟨422822677,by change 422822677<2147483647;omega⟩,⟨1335527848,by change 1335527848<2147483647;omega⟩,⟨1869469429,by change 1869469429<2147483647;omega⟩,⟨740600032,by change 740600032<2147483647;omega⟩]
theorem rawCell27 : (raw.drop 432).take 16=cell27.val := by
  simp only [raw,JFz_Scan53.data,JFz_Scan53.j00,JFz_Scan53.j01,JFz_Scan53.j02,JFz_Scan53.j03,JFz_Scan53.j04,JFz_Scan53.j05,JFz_Scan53.j06,JFz_Scan53.j07,JFz_Scan53.j08,JFz_Scan53.j09,JFz_Scan53.j10,JFz_Scan53.j11,JFz_Scan53.j12,JFz_Scan53.b00_length,JFz_Scan53.b01_length,JFz_Scan53.b02_length,JFz_Scan53.b03_length,JFz_Scan53.b04_length,JFz_Scan53.b05_length,JFz_Scan53.b06_length,JFz_Scan53.b07_length,JFz_Scan53.b08_length,JFz_Scan53.b09_length,JFz_Scan53.b10_length,JFz_Scan53.b11_length,JFz_Scan53.b12_length,JFz_Scan53.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell27
theorem encoded27 : CandidateParserByteOrder.arrayBytes16 cell27=encodeQM31LE limbs27 := by
  funext i
  fin_cases i <;> rfl
theorem parser27 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell27)=
    ok (some ⟨⟨422822677#u32,1335527848#u32⟩,⟨1869469429#u32,740600032#u32⟩⟩) :=
  JFr_EncodedCell.parser cell27 limbs27 encoded27
#print axioms encoded27
#print axioms parser27
end AspisR1.JFr_Bytes05
