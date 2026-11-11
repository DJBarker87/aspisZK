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
def cell00 : Array U8 16#usize := ⟨[226#u8,0#u8,230#u8,75#u8,165#u8,169#u8,151#u8,67#u8,131#u8,57#u8,107#u8,104#u8,112#u8,243#u8,171#u8,85#u8],by rfl⟩
def limbs00 : QM31Limbs := ![⟨1273364706,by change 1273364706<2147483647;omega⟩,⟨1134012837,by change 1134012837<2147483647;omega⟩,⟨1751857539,by change 1751857539<2147483647;omega⟩,⟨1437332336,by change 1437332336<2147483647;omega⟩]
theorem rawCell00 : (raw.drop 0).take 16=cell00.val := by
  simp only [raw,JFz_Scan55.data,JFz_Scan55.j00,JFz_Scan55.j01,JFz_Scan55.j02,JFz_Scan55.j03,JFz_Scan55.j04,JFz_Scan55.j05,JFz_Scan55.j06,JFz_Scan55.j07,JFz_Scan55.j08,JFz_Scan55.j09,JFz_Scan55.j10,JFz_Scan55.j11,JFz_Scan55.j12,JFz_Scan55.b00_length,JFz_Scan55.b01_length,JFz_Scan55.b02_length,JFz_Scan55.b03_length,JFz_Scan55.b04_length,JFz_Scan55.b05_length,JFz_Scan55.b06_length,JFz_Scan55.b07_length,JFz_Scan55.b08_length,JFz_Scan55.b09_length,JFz_Scan55.b10_length,JFz_Scan55.b11_length,JFz_Scan55.b12_length,JFz_Scan55.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell00
theorem encoded00 : CandidateParserByteOrder.arrayBytes16 cell00=encodeQM31LE limbs00 := by
  funext i
  fin_cases i <;> rfl
theorem parser00 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell00)=
    ok (some ⟨⟨1273364706#u32,1134012837#u32⟩,⟨1751857539#u32,1437332336#u32⟩⟩) :=
  JFr_EncodedCell.parser cell00 limbs00 encoded00
#print axioms encoded00
#print axioms parser00
def cell01 : Array U8 16#usize := ⟨[70#u8,140#u8,31#u8,68#u8,218#u8,184#u8,232#u8,47#u8,217#u8,128#u8,226#u8,38#u8,69#u8,87#u8,226#u8,104#u8],by rfl⟩
def limbs01 : QM31Limbs := ![⟨1142918214,by change 1142918214<2147483647;omega⟩,⟨803780826,by change 803780826<2147483647;omega⟩,⟨652378329,by change 652378329<2147483647;omega⟩,⟨1759663941,by change 1759663941<2147483647;omega⟩]
theorem rawCell01 : (raw.drop 16).take 16=cell01.val := by
  simp only [raw,JFz_Scan55.data,JFz_Scan55.j00,JFz_Scan55.j01,JFz_Scan55.j02,JFz_Scan55.j03,JFz_Scan55.j04,JFz_Scan55.j05,JFz_Scan55.j06,JFz_Scan55.j07,JFz_Scan55.j08,JFz_Scan55.j09,JFz_Scan55.j10,JFz_Scan55.j11,JFz_Scan55.j12,JFz_Scan55.b00_length,JFz_Scan55.b01_length,JFz_Scan55.b02_length,JFz_Scan55.b03_length,JFz_Scan55.b04_length,JFz_Scan55.b05_length,JFz_Scan55.b06_length,JFz_Scan55.b07_length,JFz_Scan55.b08_length,JFz_Scan55.b09_length,JFz_Scan55.b10_length,JFz_Scan55.b11_length,JFz_Scan55.b12_length,JFz_Scan55.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell01
theorem encoded01 : CandidateParserByteOrder.arrayBytes16 cell01=encodeQM31LE limbs01 := by
  funext i
  fin_cases i <;> rfl
theorem parser01 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell01)=
    ok (some ⟨⟨1142918214#u32,803780826#u32⟩,⟨652378329#u32,1759663941#u32⟩⟩) :=
  JFr_EncodedCell.parser cell01 limbs01 encoded01
#print axioms encoded01
#print axioms parser01
def cell02 : Array U8 16#usize := ⟨[101#u8,106#u8,246#u8,48#u8,189#u8,144#u8,155#u8,84#u8,208#u8,193#u8,113#u8,112#u8,200#u8,204#u8,247#u8,64#u8],by rfl⟩
def limbs02 : QM31Limbs := ![⟨821455461,by change 821455461<2147483647;omega⟩,⟨1419481277,by change 1419481277<2147483647;omega⟩,⟨1886503376,by change 1886503376<2147483647;omega⟩,⟨1089981640,by change 1089981640<2147483647;omega⟩]
theorem rawCell02 : (raw.drop 32).take 16=cell02.val := by
  simp only [raw,JFz_Scan55.data,JFz_Scan55.j00,JFz_Scan55.j01,JFz_Scan55.j02,JFz_Scan55.j03,JFz_Scan55.j04,JFz_Scan55.j05,JFz_Scan55.j06,JFz_Scan55.j07,JFz_Scan55.j08,JFz_Scan55.j09,JFz_Scan55.j10,JFz_Scan55.j11,JFz_Scan55.j12,JFz_Scan55.b00_length,JFz_Scan55.b01_length,JFz_Scan55.b02_length,JFz_Scan55.b03_length,JFz_Scan55.b04_length,JFz_Scan55.b05_length,JFz_Scan55.b06_length,JFz_Scan55.b07_length,JFz_Scan55.b08_length,JFz_Scan55.b09_length,JFz_Scan55.b10_length,JFz_Scan55.b11_length,JFz_Scan55.b12_length,JFz_Scan55.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell02
theorem encoded02 : CandidateParserByteOrder.arrayBytes16 cell02=encodeQM31LE limbs02 := by
  funext i
  fin_cases i <;> rfl
theorem parser02 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell02)=
    ok (some ⟨⟨821455461#u32,1419481277#u32⟩,⟨1886503376#u32,1089981640#u32⟩⟩) :=
  JFr_EncodedCell.parser cell02 limbs02 encoded02
#print axioms encoded02
#print axioms parser02
def cell03 : Array U8 16#usize := ⟨[99#u8,184#u8,132#u8,56#u8,1#u8,24#u8,230#u8,75#u8,177#u8,16#u8,78#u8,62#u8,97#u8,16#u8,86#u8,68#u8],by rfl⟩
def limbs03 : QM31Limbs := ![⟨948222051,by change 948222051<2147483647;omega⟩,⟨1273370625,by change 1273370625<2147483647;omega⟩,⟨1045303473,by change 1045303473<2147483647;omega⟩,⟨1146490977,by change 1146490977<2147483647;omega⟩]
theorem rawCell03 : (raw.drop 48).take 16=cell03.val := by
  simp only [raw,JFz_Scan55.data,JFz_Scan55.j00,JFz_Scan55.j01,JFz_Scan55.j02,JFz_Scan55.j03,JFz_Scan55.j04,JFz_Scan55.j05,JFz_Scan55.j06,JFz_Scan55.j07,JFz_Scan55.j08,JFz_Scan55.j09,JFz_Scan55.j10,JFz_Scan55.j11,JFz_Scan55.j12,JFz_Scan55.b00_length,JFz_Scan55.b01_length,JFz_Scan55.b02_length,JFz_Scan55.b03_length,JFz_Scan55.b04_length,JFz_Scan55.b05_length,JFz_Scan55.b06_length,JFz_Scan55.b07_length,JFz_Scan55.b08_length,JFz_Scan55.b09_length,JFz_Scan55.b10_length,JFz_Scan55.b11_length,JFz_Scan55.b12_length,JFz_Scan55.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell03
theorem encoded03 : CandidateParserByteOrder.arrayBytes16 cell03=encodeQM31LE limbs03 := by
  funext i
  fin_cases i <;> rfl
theorem parser03 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell03)=
    ok (some ⟨⟨948222051#u32,1273370625#u32⟩,⟨1045303473#u32,1146490977#u32⟩⟩) :=
  JFr_EncodedCell.parser cell03 limbs03 encoded03
#print axioms encoded03
#print axioms parser03
def cell04 : Array U8 16#usize := ⟨[57#u8,163#u8,136#u8,4#u8,8#u8,107#u8,121#u8,34#u8,60#u8,250#u8,232#u8,126#u8,225#u8,183#u8,135#u8,102#u8],by rfl⟩
def limbs04 : QM31Limbs := ![⟨76063545,by change 76063545<2147483647;omega⟩,⟨578382600,by change 578382600<2147483647;omega⟩,⟨2129197628,by change 2129197628<2147483647;omega⟩,⟨1720170465,by change 1720170465<2147483647;omega⟩]
theorem rawCell04 : (raw.drop 64).take 16=cell04.val := by
  simp only [raw,JFz_Scan55.data,JFz_Scan55.j00,JFz_Scan55.j01,JFz_Scan55.j02,JFz_Scan55.j03,JFz_Scan55.j04,JFz_Scan55.j05,JFz_Scan55.j06,JFz_Scan55.j07,JFz_Scan55.j08,JFz_Scan55.j09,JFz_Scan55.j10,JFz_Scan55.j11,JFz_Scan55.j12,JFz_Scan55.b00_length,JFz_Scan55.b01_length,JFz_Scan55.b02_length,JFz_Scan55.b03_length,JFz_Scan55.b04_length,JFz_Scan55.b05_length,JFz_Scan55.b06_length,JFz_Scan55.b07_length,JFz_Scan55.b08_length,JFz_Scan55.b09_length,JFz_Scan55.b10_length,JFz_Scan55.b11_length,JFz_Scan55.b12_length,JFz_Scan55.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell04
theorem encoded04 : CandidateParserByteOrder.arrayBytes16 cell04=encodeQM31LE limbs04 := by
  funext i
  fin_cases i <;> rfl
theorem parser04 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell04)=
    ok (some ⟨⟨76063545#u32,578382600#u32⟩,⟨2129197628#u32,1720170465#u32⟩⟩) :=
  JFr_EncodedCell.parser cell04 limbs04 encoded04
#print axioms encoded04
#print axioms parser04
def cell05 : Array U8 16#usize := ⟨[240#u8,141#u8,181#u8,70#u8,101#u8,71#u8,196#u8,99#u8,175#u8,85#u8,68#u8,99#u8,174#u8,154#u8,149#u8,89#u8],by rfl⟩
def limbs05 : QM31Limbs := ![⟨1186303472,by change 1186303472<2147483647;omega⟩,⟨1673807717,by change 1673807717<2147483647;omega⟩,⟨1665422767,by change 1665422767<2147483647;omega⟩,⟨1502976686,by change 1502976686<2147483647;omega⟩]
theorem rawCell05 : (raw.drop 80).take 16=cell05.val := by
  simp only [raw,JFz_Scan55.data,JFz_Scan55.j00,JFz_Scan55.j01,JFz_Scan55.j02,JFz_Scan55.j03,JFz_Scan55.j04,JFz_Scan55.j05,JFz_Scan55.j06,JFz_Scan55.j07,JFz_Scan55.j08,JFz_Scan55.j09,JFz_Scan55.j10,JFz_Scan55.j11,JFz_Scan55.j12,JFz_Scan55.b00_length,JFz_Scan55.b01_length,JFz_Scan55.b02_length,JFz_Scan55.b03_length,JFz_Scan55.b04_length,JFz_Scan55.b05_length,JFz_Scan55.b06_length,JFz_Scan55.b07_length,JFz_Scan55.b08_length,JFz_Scan55.b09_length,JFz_Scan55.b10_length,JFz_Scan55.b11_length,JFz_Scan55.b12_length,JFz_Scan55.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell05
theorem encoded05 : CandidateParserByteOrder.arrayBytes16 cell05=encodeQM31LE limbs05 := by
  funext i
  fin_cases i <;> rfl
theorem parser05 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell05)=
    ok (some ⟨⟨1186303472#u32,1673807717#u32⟩,⟨1665422767#u32,1502976686#u32⟩⟩) :=
  JFr_EncodedCell.parser cell05 limbs05 encoded05
#print axioms encoded05
#print axioms parser05
def cell06 : Array U8 16#usize := ⟨[99#u8,197#u8,167#u8,46#u8,210#u8,58#u8,142#u8,103#u8,227#u8,161#u8,104#u8,124#u8,62#u8,101#u8,41#u8,47#u8],by rfl⟩
def limbs06 : QM31Limbs := ![⟨782746979,by change 782746979<2147483647;omega⟩,⟨1737374418,by change 1737374418<2147483647;omega⟩,⟨2087231971,by change 2087231971<2147483647;omega⟩,⟨791242046,by change 791242046<2147483647;omega⟩]
theorem rawCell06 : (raw.drop 96).take 16=cell06.val := by
  simp only [raw,JFz_Scan55.data,JFz_Scan55.j00,JFz_Scan55.j01,JFz_Scan55.j02,JFz_Scan55.j03,JFz_Scan55.j04,JFz_Scan55.j05,JFz_Scan55.j06,JFz_Scan55.j07,JFz_Scan55.j08,JFz_Scan55.j09,JFz_Scan55.j10,JFz_Scan55.j11,JFz_Scan55.j12,JFz_Scan55.b00_length,JFz_Scan55.b01_length,JFz_Scan55.b02_length,JFz_Scan55.b03_length,JFz_Scan55.b04_length,JFz_Scan55.b05_length,JFz_Scan55.b06_length,JFz_Scan55.b07_length,JFz_Scan55.b08_length,JFz_Scan55.b09_length,JFz_Scan55.b10_length,JFz_Scan55.b11_length,JFz_Scan55.b12_length,JFz_Scan55.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell06
theorem encoded06 : CandidateParserByteOrder.arrayBytes16 cell06=encodeQM31LE limbs06 := by
  funext i
  fin_cases i <;> rfl
theorem parser06 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell06)=
    ok (some ⟨⟨782746979#u32,1737374418#u32⟩,⟨2087231971#u32,791242046#u32⟩⟩) :=
  JFr_EncodedCell.parser cell06 limbs06 encoded06
#print axioms encoded06
#print axioms parser06
def cell07 : Array U8 16#usize := ⟨[38#u8,168#u8,152#u8,99#u8,206#u8,160#u8,116#u8,21#u8,102#u8,34#u8,106#u8,61#u8,95#u8,237#u8,60#u8,60#u8],by rfl⟩
def limbs07 : QM31Limbs := ![⟨1670948902,by change 1670948902<2147483647;omega⟩,⟨359964878,by change 359964878<2147483647;omega⟩,⟨1030365798,by change 1030365798<2147483647;omega⟩,⟨1010625887,by change 1010625887<2147483647;omega⟩]
theorem rawCell07 : (raw.drop 112).take 16=cell07.val := by
  simp only [raw,JFz_Scan55.data,JFz_Scan55.j00,JFz_Scan55.j01,JFz_Scan55.j02,JFz_Scan55.j03,JFz_Scan55.j04,JFz_Scan55.j05,JFz_Scan55.j06,JFz_Scan55.j07,JFz_Scan55.j08,JFz_Scan55.j09,JFz_Scan55.j10,JFz_Scan55.j11,JFz_Scan55.j12,JFz_Scan55.b00_length,JFz_Scan55.b01_length,JFz_Scan55.b02_length,JFz_Scan55.b03_length,JFz_Scan55.b04_length,JFz_Scan55.b05_length,JFz_Scan55.b06_length,JFz_Scan55.b07_length,JFz_Scan55.b08_length,JFz_Scan55.b09_length,JFz_Scan55.b10_length,JFz_Scan55.b11_length,JFz_Scan55.b12_length,JFz_Scan55.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell07
theorem encoded07 : CandidateParserByteOrder.arrayBytes16 cell07=encodeQM31LE limbs07 := by
  funext i
  fin_cases i <;> rfl
theorem parser07 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell07)=
    ok (some ⟨⟨1670948902#u32,359964878#u32⟩,⟨1030365798#u32,1010625887#u32⟩⟩) :=
  JFr_EncodedCell.parser cell07 limbs07 encoded07
#print axioms encoded07
#print axioms parser07
def cell08 : Array U8 16#usize := ⟨[243#u8,91#u8,246#u8,119#u8,73#u8,121#u8,17#u8,5#u8,30#u8,209#u8,39#u8,83#u8,160#u8,198#u8,75#u8,28#u8],by rfl⟩
def limbs08 : QM31Limbs := ![⟨2012634099,by change 2012634099<2147483647;omega⟩,⟨85031241,by change 85031241<2147483647;omega⟩,⟨1395118366,by change 1395118366<2147483647;omega⟩,⟨474728096,by change 474728096<2147483647;omega⟩]
theorem rawCell08 : (raw.drop 128).take 16=cell08.val := by
  simp only [raw,JFz_Scan55.data,JFz_Scan55.j00,JFz_Scan55.j01,JFz_Scan55.j02,JFz_Scan55.j03,JFz_Scan55.j04,JFz_Scan55.j05,JFz_Scan55.j06,JFz_Scan55.j07,JFz_Scan55.j08,JFz_Scan55.j09,JFz_Scan55.j10,JFz_Scan55.j11,JFz_Scan55.j12,JFz_Scan55.b00_length,JFz_Scan55.b01_length,JFz_Scan55.b02_length,JFz_Scan55.b03_length,JFz_Scan55.b04_length,JFz_Scan55.b05_length,JFz_Scan55.b06_length,JFz_Scan55.b07_length,JFz_Scan55.b08_length,JFz_Scan55.b09_length,JFz_Scan55.b10_length,JFz_Scan55.b11_length,JFz_Scan55.b12_length,JFz_Scan55.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell08
theorem encoded08 : CandidateParserByteOrder.arrayBytes16 cell08=encodeQM31LE limbs08 := by
  funext i
  fin_cases i <;> rfl
theorem parser08 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell08)=
    ok (some ⟨⟨2012634099#u32,85031241#u32⟩,⟨1395118366#u32,474728096#u32⟩⟩) :=
  JFr_EncodedCell.parser cell08 limbs08 encoded08
#print axioms encoded08
#print axioms parser08
def cell09 : Array U8 16#usize := ⟨[115#u8,166#u8,137#u8,71#u8,181#u8,8#u8,36#u8,65#u8,143#u8,169#u8,125#u8,45#u8,201#u8,53#u8,120#u8,48#u8],by rfl⟩
def limbs09 : QM31Limbs := ![⟨1200203379,by change 1200203379<2147483647;omega⟩,⟨1092880565,by change 1092880565<2147483647;omega⟩,⟨763210127,by change 763210127<2147483647;omega⟩,⟨813184457,by change 813184457<2147483647;omega⟩]
theorem rawCell09 : (raw.drop 144).take 16=cell09.val := by
  simp only [raw,JFz_Scan55.data,JFz_Scan55.j00,JFz_Scan55.j01,JFz_Scan55.j02,JFz_Scan55.j03,JFz_Scan55.j04,JFz_Scan55.j05,JFz_Scan55.j06,JFz_Scan55.j07,JFz_Scan55.j08,JFz_Scan55.j09,JFz_Scan55.j10,JFz_Scan55.j11,JFz_Scan55.j12,JFz_Scan55.b00_length,JFz_Scan55.b01_length,JFz_Scan55.b02_length,JFz_Scan55.b03_length,JFz_Scan55.b04_length,JFz_Scan55.b05_length,JFz_Scan55.b06_length,JFz_Scan55.b07_length,JFz_Scan55.b08_length,JFz_Scan55.b09_length,JFz_Scan55.b10_length,JFz_Scan55.b11_length,JFz_Scan55.b12_length,JFz_Scan55.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell09
theorem encoded09 : CandidateParserByteOrder.arrayBytes16 cell09=encodeQM31LE limbs09 := by
  funext i
  fin_cases i <;> rfl
theorem parser09 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell09)=
    ok (some ⟨⟨1200203379#u32,1092880565#u32⟩,⟨763210127#u32,813184457#u32⟩⟩) :=
  JFr_EncodedCell.parser cell09 limbs09 encoded09
#print axioms encoded09
#print axioms parser09
def cell10 : Array U8 16#usize := ⟨[212#u8,171#u8,61#u8,42#u8,169#u8,208#u8,187#u8,6#u8,236#u8,151#u8,79#u8,56#u8,183#u8,144#u8,27#u8,104#u8],by rfl⟩
def limbs10 : QM31Limbs := ![⟨708684756,by change 708684756<2147483647;omega⟩,⟨112971945,by change 112971945<2147483647;omega⟩,⟨944740332,by change 944740332<2147483647;omega⟩,⟨1746636983,by change 1746636983<2147483647;omega⟩]
theorem rawCell10 : (raw.drop 160).take 16=cell10.val := by
  simp only [raw,JFz_Scan55.data,JFz_Scan55.j00,JFz_Scan55.j01,JFz_Scan55.j02,JFz_Scan55.j03,JFz_Scan55.j04,JFz_Scan55.j05,JFz_Scan55.j06,JFz_Scan55.j07,JFz_Scan55.j08,JFz_Scan55.j09,JFz_Scan55.j10,JFz_Scan55.j11,JFz_Scan55.j12,JFz_Scan55.b00_length,JFz_Scan55.b01_length,JFz_Scan55.b02_length,JFz_Scan55.b03_length,JFz_Scan55.b04_length,JFz_Scan55.b05_length,JFz_Scan55.b06_length,JFz_Scan55.b07_length,JFz_Scan55.b08_length,JFz_Scan55.b09_length,JFz_Scan55.b10_length,JFz_Scan55.b11_length,JFz_Scan55.b12_length,JFz_Scan55.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell10
theorem encoded10 : CandidateParserByteOrder.arrayBytes16 cell10=encodeQM31LE limbs10 := by
  funext i
  fin_cases i <;> rfl
theorem parser10 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell10)=
    ok (some ⟨⟨708684756#u32,112971945#u32⟩,⟨944740332#u32,1746636983#u32⟩⟩) :=
  JFr_EncodedCell.parser cell10 limbs10 encoded10
#print axioms encoded10
#print axioms parser10
def cell11 : Array U8 16#usize := ⟨[78#u8,39#u8,211#u8,73#u8,251#u8,70#u8,143#u8,19#u8,40#u8,98#u8,218#u8,72#u8,3#u8,113#u8,186#u8,23#u8],by rfl⟩
def limbs11 : QM31Limbs := ![⟨1238574926,by change 1238574926<2147483647;omega⟩,⟨328156923,by change 328156923<2147483647;omega⟩,⟨1222271528,by change 1222271528<2147483647;omega⟩,⟨398094595,by change 398094595<2147483647;omega⟩]
theorem rawCell11 : (raw.drop 176).take 16=cell11.val := by
  simp only [raw,JFz_Scan55.data,JFz_Scan55.j00,JFz_Scan55.j01,JFz_Scan55.j02,JFz_Scan55.j03,JFz_Scan55.j04,JFz_Scan55.j05,JFz_Scan55.j06,JFz_Scan55.j07,JFz_Scan55.j08,JFz_Scan55.j09,JFz_Scan55.j10,JFz_Scan55.j11,JFz_Scan55.j12,JFz_Scan55.b00_length,JFz_Scan55.b01_length,JFz_Scan55.b02_length,JFz_Scan55.b03_length,JFz_Scan55.b04_length,JFz_Scan55.b05_length,JFz_Scan55.b06_length,JFz_Scan55.b07_length,JFz_Scan55.b08_length,JFz_Scan55.b09_length,JFz_Scan55.b10_length,JFz_Scan55.b11_length,JFz_Scan55.b12_length,JFz_Scan55.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell11
theorem encoded11 : CandidateParserByteOrder.arrayBytes16 cell11=encodeQM31LE limbs11 := by
  funext i
  fin_cases i <;> rfl
theorem parser11 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell11)=
    ok (some ⟨⟨1238574926#u32,328156923#u32⟩,⟨1222271528#u32,398094595#u32⟩⟩) :=
  JFr_EncodedCell.parser cell11 limbs11 encoded11
#print axioms encoded11
#print axioms parser11
def cell12 : Array U8 16#usize := ⟨[52#u8,173#u8,139#u8,41#u8,175#u8,39#u8,219#u8,71#u8,204#u8,151#u8,102#u8,35#u8,16#u8,27#u8,179#u8,69#u8],by rfl⟩
def limbs12 : QM31Limbs := ![⟨697019700,by change 697019700<2147483647;omega⟩,⟨1205544879,by change 1205544879<2147483647;omega⟩,⟨593926092,by change 593926092<2147483647;omega⟩,⟨1169365776,by change 1169365776<2147483647;omega⟩]
theorem rawCell12 : (raw.drop 192).take 16=cell12.val := by
  simp only [raw,JFz_Scan55.data,JFz_Scan55.j00,JFz_Scan55.j01,JFz_Scan55.j02,JFz_Scan55.j03,JFz_Scan55.j04,JFz_Scan55.j05,JFz_Scan55.j06,JFz_Scan55.j07,JFz_Scan55.j08,JFz_Scan55.j09,JFz_Scan55.j10,JFz_Scan55.j11,JFz_Scan55.j12,JFz_Scan55.b00_length,JFz_Scan55.b01_length,JFz_Scan55.b02_length,JFz_Scan55.b03_length,JFz_Scan55.b04_length,JFz_Scan55.b05_length,JFz_Scan55.b06_length,JFz_Scan55.b07_length,JFz_Scan55.b08_length,JFz_Scan55.b09_length,JFz_Scan55.b10_length,JFz_Scan55.b11_length,JFz_Scan55.b12_length,JFz_Scan55.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell12
theorem encoded12 : CandidateParserByteOrder.arrayBytes16 cell12=encodeQM31LE limbs12 := by
  funext i
  fin_cases i <;> rfl
theorem parser12 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell12)=
    ok (some ⟨⟨697019700#u32,1205544879#u32⟩,⟨593926092#u32,1169365776#u32⟩⟩) :=
  JFr_EncodedCell.parser cell12 limbs12 encoded12
#print axioms encoded12
#print axioms parser12
def cell13 : Array U8 16#usize := ⟨[96#u8,226#u8,8#u8,10#u8,99#u8,251#u8,166#u8,62#u8,176#u8,232#u8,241#u8,2#u8,179#u8,15#u8,129#u8,9#u8],by rfl⟩
def limbs13 : QM31Limbs := ![⟨168354400,by change 168354400<2147483647;omega⟩,⟨1051130723,by change 1051130723<2147483647;omega⟩,⟨49408176,by change 49408176<2147483647;omega⟩,⟨159453107,by change 159453107<2147483647;omega⟩]
theorem rawCell13 : (raw.drop 208).take 16=cell13.val := by
  simp only [raw,JFz_Scan55.data,JFz_Scan55.j00,JFz_Scan55.j01,JFz_Scan55.j02,JFz_Scan55.j03,JFz_Scan55.j04,JFz_Scan55.j05,JFz_Scan55.j06,JFz_Scan55.j07,JFz_Scan55.j08,JFz_Scan55.j09,JFz_Scan55.j10,JFz_Scan55.j11,JFz_Scan55.j12,JFz_Scan55.b00_length,JFz_Scan55.b01_length,JFz_Scan55.b02_length,JFz_Scan55.b03_length,JFz_Scan55.b04_length,JFz_Scan55.b05_length,JFz_Scan55.b06_length,JFz_Scan55.b07_length,JFz_Scan55.b08_length,JFz_Scan55.b09_length,JFz_Scan55.b10_length,JFz_Scan55.b11_length,JFz_Scan55.b12_length,JFz_Scan55.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell13
theorem encoded13 : CandidateParserByteOrder.arrayBytes16 cell13=encodeQM31LE limbs13 := by
  funext i
  fin_cases i <;> rfl
theorem parser13 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell13)=
    ok (some ⟨⟨168354400#u32,1051130723#u32⟩,⟨49408176#u32,159453107#u32⟩⟩) :=
  JFr_EncodedCell.parser cell13 limbs13 encoded13
#print axioms encoded13
#print axioms parser13
def cell14 : Array U8 16#usize := ⟨[117#u8,227#u8,147#u8,99#u8,120#u8,49#u8,205#u8,126#u8,103#u8,111#u8,99#u8,19#u8,142#u8,210#u8,84#u8,82#u8],by rfl⟩
def limbs14 : QM31Limbs := ![⟨1670636405,by change 1670636405<2147483647;omega⟩,⟨2127376760,by change 2127376760<2147483647;omega⟩,⟨325283687,by change 325283687<2147483647;omega⟩,⟨1381290638,by change 1381290638<2147483647;omega⟩]
theorem rawCell14 : (raw.drop 224).take 16=cell14.val := by
  simp only [raw,JFz_Scan55.data,JFz_Scan55.j00,JFz_Scan55.j01,JFz_Scan55.j02,JFz_Scan55.j03,JFz_Scan55.j04,JFz_Scan55.j05,JFz_Scan55.j06,JFz_Scan55.j07,JFz_Scan55.j08,JFz_Scan55.j09,JFz_Scan55.j10,JFz_Scan55.j11,JFz_Scan55.j12,JFz_Scan55.b00_length,JFz_Scan55.b01_length,JFz_Scan55.b02_length,JFz_Scan55.b03_length,JFz_Scan55.b04_length,JFz_Scan55.b05_length,JFz_Scan55.b06_length,JFz_Scan55.b07_length,JFz_Scan55.b08_length,JFz_Scan55.b09_length,JFz_Scan55.b10_length,JFz_Scan55.b11_length,JFz_Scan55.b12_length,JFz_Scan55.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell14
theorem encoded14 : CandidateParserByteOrder.arrayBytes16 cell14=encodeQM31LE limbs14 := by
  funext i
  fin_cases i <;> rfl
theorem parser14 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell14)=
    ok (some ⟨⟨1670636405#u32,2127376760#u32⟩,⟨325283687#u32,1381290638#u32⟩⟩) :=
  JFr_EncodedCell.parser cell14 limbs14 encoded14
#print axioms encoded14
#print axioms parser14
def cell15 : Array U8 16#usize := ⟨[77#u8,19#u8,94#u8,41#u8,122#u8,54#u8,53#u8,35#u8,179#u8,16#u8,77#u8,107#u8,109#u8,229#u8,124#u8,61#u8],by rfl⟩
def limbs15 : QM31Limbs := ![⟨694031181,by change 694031181<2147483647;omega⟩,⟨590689914,by change 590689914<2147483647;omega⟩,⟨1800212659,by change 1800212659<2147483647;omega⟩,⟨1031595373,by change 1031595373<2147483647;omega⟩]
theorem rawCell15 : (raw.drop 240).take 16=cell15.val := by
  simp only [raw,JFz_Scan55.data,JFz_Scan55.j00,JFz_Scan55.j01,JFz_Scan55.j02,JFz_Scan55.j03,JFz_Scan55.j04,JFz_Scan55.j05,JFz_Scan55.j06,JFz_Scan55.j07,JFz_Scan55.j08,JFz_Scan55.j09,JFz_Scan55.j10,JFz_Scan55.j11,JFz_Scan55.j12,JFz_Scan55.b00_length,JFz_Scan55.b01_length,JFz_Scan55.b02_length,JFz_Scan55.b03_length,JFz_Scan55.b04_length,JFz_Scan55.b05_length,JFz_Scan55.b06_length,JFz_Scan55.b07_length,JFz_Scan55.b08_length,JFz_Scan55.b09_length,JFz_Scan55.b10_length,JFz_Scan55.b11_length,JFz_Scan55.b12_length,JFz_Scan55.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell15
theorem encoded15 : CandidateParserByteOrder.arrayBytes16 cell15=encodeQM31LE limbs15 := by
  funext i
  fin_cases i <;> rfl
theorem parser15 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell15)=
    ok (some ⟨⟨694031181#u32,590689914#u32⟩,⟨1800212659#u32,1031595373#u32⟩⟩) :=
  JFr_EncodedCell.parser cell15 limbs15 encoded15
#print axioms encoded15
#print axioms parser15
def cell16 : Array U8 16#usize := ⟨[142#u8,227#u8,76#u8,121#u8,248#u8,141#u8,66#u8,13#u8,195#u8,187#u8,142#u8,23#u8,227#u8,237#u8,194#u8,42#u8],by rfl⟩
def limbs16 : QM31Limbs := ![⟨2035082126,by change 2035082126<2147483647;omega⟩,⟨222465528,by change 222465528<2147483647;omega⟩,⟨395230147,by change 395230147<2147483647;omega⟩,⟨717417955,by change 717417955<2147483647;omega⟩]
theorem rawCell16 : (raw.drop 256).take 16=cell16.val := by
  simp only [raw,JFz_Scan55.data,JFz_Scan55.j00,JFz_Scan55.j01,JFz_Scan55.j02,JFz_Scan55.j03,JFz_Scan55.j04,JFz_Scan55.j05,JFz_Scan55.j06,JFz_Scan55.j07,JFz_Scan55.j08,JFz_Scan55.j09,JFz_Scan55.j10,JFz_Scan55.j11,JFz_Scan55.j12,JFz_Scan55.b00_length,JFz_Scan55.b01_length,JFz_Scan55.b02_length,JFz_Scan55.b03_length,JFz_Scan55.b04_length,JFz_Scan55.b05_length,JFz_Scan55.b06_length,JFz_Scan55.b07_length,JFz_Scan55.b08_length,JFz_Scan55.b09_length,JFz_Scan55.b10_length,JFz_Scan55.b11_length,JFz_Scan55.b12_length,JFz_Scan55.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell16
theorem encoded16 : CandidateParserByteOrder.arrayBytes16 cell16=encodeQM31LE limbs16 := by
  funext i
  fin_cases i <;> rfl
theorem parser16 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell16)=
    ok (some ⟨⟨2035082126#u32,222465528#u32⟩,⟨395230147#u32,717417955#u32⟩⟩) :=
  JFr_EncodedCell.parser cell16 limbs16 encoded16
#print axioms encoded16
#print axioms parser16
def cell17 : Array U8 16#usize := ⟨[217#u8,23#u8,84#u8,17#u8,160#u8,181#u8,120#u8,87#u8,26#u8,56#u8,249#u8,6#u8,183#u8,88#u8,91#u8,87#u8],by rfl⟩
def limbs17 : QM31Limbs := ![⟨290723801,by change 290723801<2147483647;omega⟩,⟨1467528608,by change 1467528608<2147483647;omega⟩,⟨116996122,by change 116996122<2147483647;omega⟩,⟨1465604279,by change 1465604279<2147483647;omega⟩]
theorem rawCell17 : (raw.drop 272).take 16=cell17.val := by
  simp only [raw,JFz_Scan55.data,JFz_Scan55.j00,JFz_Scan55.j01,JFz_Scan55.j02,JFz_Scan55.j03,JFz_Scan55.j04,JFz_Scan55.j05,JFz_Scan55.j06,JFz_Scan55.j07,JFz_Scan55.j08,JFz_Scan55.j09,JFz_Scan55.j10,JFz_Scan55.j11,JFz_Scan55.j12,JFz_Scan55.b00_length,JFz_Scan55.b01_length,JFz_Scan55.b02_length,JFz_Scan55.b03_length,JFz_Scan55.b04_length,JFz_Scan55.b05_length,JFz_Scan55.b06_length,JFz_Scan55.b07_length,JFz_Scan55.b08_length,JFz_Scan55.b09_length,JFz_Scan55.b10_length,JFz_Scan55.b11_length,JFz_Scan55.b12_length,JFz_Scan55.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell17
theorem encoded17 : CandidateParserByteOrder.arrayBytes16 cell17=encodeQM31LE limbs17 := by
  funext i
  fin_cases i <;> rfl
theorem parser17 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell17)=
    ok (some ⟨⟨290723801#u32,1467528608#u32⟩,⟨116996122#u32,1465604279#u32⟩⟩) :=
  JFr_EncodedCell.parser cell17 limbs17 encoded17
#print axioms encoded17
#print axioms parser17
def cell18 : Array U8 16#usize := ⟨[190#u8,194#u8,29#u8,92#u8,98#u8,69#u8,42#u8,83#u8,129#u8,178#u8,39#u8,114#u8,60#u8,23#u8,225#u8,82#u8],by rfl⟩
def limbs18 : QM31Limbs := ![⟨1545454270,by change 1545454270<2147483647;omega⟩,⟨1395279202,by change 1395279202<2147483647;omega⟩,⟨1915204225,by change 1915204225<2147483647;omega⟩,⟨1390483260,by change 1390483260<2147483647;omega⟩]
theorem rawCell18 : (raw.drop 288).take 16=cell18.val := by
  simp only [raw,JFz_Scan55.data,JFz_Scan55.j00,JFz_Scan55.j01,JFz_Scan55.j02,JFz_Scan55.j03,JFz_Scan55.j04,JFz_Scan55.j05,JFz_Scan55.j06,JFz_Scan55.j07,JFz_Scan55.j08,JFz_Scan55.j09,JFz_Scan55.j10,JFz_Scan55.j11,JFz_Scan55.j12,JFz_Scan55.b00_length,JFz_Scan55.b01_length,JFz_Scan55.b02_length,JFz_Scan55.b03_length,JFz_Scan55.b04_length,JFz_Scan55.b05_length,JFz_Scan55.b06_length,JFz_Scan55.b07_length,JFz_Scan55.b08_length,JFz_Scan55.b09_length,JFz_Scan55.b10_length,JFz_Scan55.b11_length,JFz_Scan55.b12_length,JFz_Scan55.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell18
theorem encoded18 : CandidateParserByteOrder.arrayBytes16 cell18=encodeQM31LE limbs18 := by
  funext i
  fin_cases i <;> rfl
theorem parser18 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell18)=
    ok (some ⟨⟨1545454270#u32,1395279202#u32⟩,⟨1915204225#u32,1390483260#u32⟩⟩) :=
  JFr_EncodedCell.parser cell18 limbs18 encoded18
#print axioms encoded18
#print axioms parser18
def cell19 : Array U8 16#usize := ⟨[27#u8,141#u8,170#u8,5#u8,73#u8,60#u8,232#u8,107#u8,44#u8,222#u8,206#u8,47#u8,95#u8,10#u8,12#u8,111#u8],by rfl⟩
def limbs19 : QM31Limbs := ![⟨95063323,by change 95063323<2147483647;omega⟩,⟨1810381897,by change 1810381897<2147483647;omega⟩,⟨802086444,by change 802086444<2147483647;omega⟩,⟨1863060063,by change 1863060063<2147483647;omega⟩]
theorem rawCell19 : (raw.drop 304).take 16=cell19.val := by
  simp only [raw,JFz_Scan55.data,JFz_Scan55.j00,JFz_Scan55.j01,JFz_Scan55.j02,JFz_Scan55.j03,JFz_Scan55.j04,JFz_Scan55.j05,JFz_Scan55.j06,JFz_Scan55.j07,JFz_Scan55.j08,JFz_Scan55.j09,JFz_Scan55.j10,JFz_Scan55.j11,JFz_Scan55.j12,JFz_Scan55.b00_length,JFz_Scan55.b01_length,JFz_Scan55.b02_length,JFz_Scan55.b03_length,JFz_Scan55.b04_length,JFz_Scan55.b05_length,JFz_Scan55.b06_length,JFz_Scan55.b07_length,JFz_Scan55.b08_length,JFz_Scan55.b09_length,JFz_Scan55.b10_length,JFz_Scan55.b11_length,JFz_Scan55.b12_length,JFz_Scan55.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell19
theorem encoded19 : CandidateParserByteOrder.arrayBytes16 cell19=encodeQM31LE limbs19 := by
  funext i
  fin_cases i <;> rfl
theorem parser19 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell19)=
    ok (some ⟨⟨95063323#u32,1810381897#u32⟩,⟨802086444#u32,1863060063#u32⟩⟩) :=
  JFr_EncodedCell.parser cell19 limbs19 encoded19
#print axioms encoded19
#print axioms parser19
def cell20 : Array U8 16#usize := ⟨[42#u8,103#u8,191#u8,51#u8,181#u8,151#u8,81#u8,122#u8,247#u8,104#u8,133#u8,31#u8,253#u8,36#u8,185#u8,70#u8],by rfl⟩
def limbs20 : QM31Limbs := ![⟨868181802,by change 868181802<2147483647;omega⟩,⟨2052167605,by change 2052167605<2147483647;omega⟩,⟨528836855,by change 528836855<2147483647;omega⟩,⟨1186538749,by change 1186538749<2147483647;omega⟩]
theorem rawCell20 : (raw.drop 320).take 16=cell20.val := by
  simp only [raw,JFz_Scan55.data,JFz_Scan55.j00,JFz_Scan55.j01,JFz_Scan55.j02,JFz_Scan55.j03,JFz_Scan55.j04,JFz_Scan55.j05,JFz_Scan55.j06,JFz_Scan55.j07,JFz_Scan55.j08,JFz_Scan55.j09,JFz_Scan55.j10,JFz_Scan55.j11,JFz_Scan55.j12,JFz_Scan55.b00_length,JFz_Scan55.b01_length,JFz_Scan55.b02_length,JFz_Scan55.b03_length,JFz_Scan55.b04_length,JFz_Scan55.b05_length,JFz_Scan55.b06_length,JFz_Scan55.b07_length,JFz_Scan55.b08_length,JFz_Scan55.b09_length,JFz_Scan55.b10_length,JFz_Scan55.b11_length,JFz_Scan55.b12_length,JFz_Scan55.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell20
theorem encoded20 : CandidateParserByteOrder.arrayBytes16 cell20=encodeQM31LE limbs20 := by
  funext i
  fin_cases i <;> rfl
theorem parser20 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell20)=
    ok (some ⟨⟨868181802#u32,2052167605#u32⟩,⟨528836855#u32,1186538749#u32⟩⟩) :=
  JFr_EncodedCell.parser cell20 limbs20 encoded20
#print axioms encoded20
#print axioms parser20
def cell21 : Array U8 16#usize := ⟨[187#u8,107#u8,111#u8,89#u8,140#u8,78#u8,198#u8,103#u8,191#u8,28#u8,92#u8,68#u8,209#u8,69#u8,109#u8,103#u8],by rfl⟩
def limbs21 : QM31Limbs := ![⟨1500474299,by change 1500474299<2147483647;omega⟩,⟨1741049484,by change 1741049484<2147483647;omega⟩,⟨1146887359,by change 1146887359<2147483647;omega⟩,⟨1735214545,by change 1735214545<2147483647;omega⟩]
theorem rawCell21 : (raw.drop 336).take 16=cell21.val := by
  simp only [raw,JFz_Scan55.data,JFz_Scan55.j00,JFz_Scan55.j01,JFz_Scan55.j02,JFz_Scan55.j03,JFz_Scan55.j04,JFz_Scan55.j05,JFz_Scan55.j06,JFz_Scan55.j07,JFz_Scan55.j08,JFz_Scan55.j09,JFz_Scan55.j10,JFz_Scan55.j11,JFz_Scan55.j12,JFz_Scan55.b00_length,JFz_Scan55.b01_length,JFz_Scan55.b02_length,JFz_Scan55.b03_length,JFz_Scan55.b04_length,JFz_Scan55.b05_length,JFz_Scan55.b06_length,JFz_Scan55.b07_length,JFz_Scan55.b08_length,JFz_Scan55.b09_length,JFz_Scan55.b10_length,JFz_Scan55.b11_length,JFz_Scan55.b12_length,JFz_Scan55.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell21
theorem encoded21 : CandidateParserByteOrder.arrayBytes16 cell21=encodeQM31LE limbs21 := by
  funext i
  fin_cases i <;> rfl
theorem parser21 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell21)=
    ok (some ⟨⟨1500474299#u32,1741049484#u32⟩,⟨1146887359#u32,1735214545#u32⟩⟩) :=
  JFr_EncodedCell.parser cell21 limbs21 encoded21
#print axioms encoded21
#print axioms parser21
def cell22 : Array U8 16#usize := ⟨[214#u8,168#u8,138#u8,12#u8,174#u8,106#u8,36#u8,73#u8,62#u8,245#u8,162#u8,122#u8,214#u8,33#u8,181#u8,108#u8],by rfl⟩
def limbs22 : QM31Limbs := ![⟨210413782,by change 210413782<2147483647;omega⟩,⟨1227123374,by change 1227123374<2147483647;omega⟩,⟨2057499966,by change 2057499966<2147483647;omega⟩,⟨1823810006,by change 1823810006<2147483647;omega⟩]
theorem rawCell22 : (raw.drop 352).take 16=cell22.val := by
  simp only [raw,JFz_Scan55.data,JFz_Scan55.j00,JFz_Scan55.j01,JFz_Scan55.j02,JFz_Scan55.j03,JFz_Scan55.j04,JFz_Scan55.j05,JFz_Scan55.j06,JFz_Scan55.j07,JFz_Scan55.j08,JFz_Scan55.j09,JFz_Scan55.j10,JFz_Scan55.j11,JFz_Scan55.j12,JFz_Scan55.b00_length,JFz_Scan55.b01_length,JFz_Scan55.b02_length,JFz_Scan55.b03_length,JFz_Scan55.b04_length,JFz_Scan55.b05_length,JFz_Scan55.b06_length,JFz_Scan55.b07_length,JFz_Scan55.b08_length,JFz_Scan55.b09_length,JFz_Scan55.b10_length,JFz_Scan55.b11_length,JFz_Scan55.b12_length,JFz_Scan55.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell22
theorem encoded22 : CandidateParserByteOrder.arrayBytes16 cell22=encodeQM31LE limbs22 := by
  funext i
  fin_cases i <;> rfl
theorem parser22 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell22)=
    ok (some ⟨⟨210413782#u32,1227123374#u32⟩,⟨2057499966#u32,1823810006#u32⟩⟩) :=
  JFr_EncodedCell.parser cell22 limbs22 encoded22
#print axioms encoded22
#print axioms parser22
def cell23 : Array U8 16#usize := ⟨[249#u8,81#u8,67#u8,85#u8,159#u8,77#u8,73#u8,31#u8,227#u8,47#u8,142#u8,67#u8,187#u8,79#u8,166#u8,69#u8],by rfl⟩
def limbs23 : QM31Limbs := ![⟨1430475257,by change 1430475257<2147483647;omega⟩,⟨524897695,by change 524897695<2147483647;omega⟩,⟨1133391843,by change 1133391843<2147483647;omega⟩,⟨1168527291,by change 1168527291<2147483647;omega⟩]
theorem rawCell23 : (raw.drop 368).take 16=cell23.val := by
  simp only [raw,JFz_Scan55.data,JFz_Scan55.j00,JFz_Scan55.j01,JFz_Scan55.j02,JFz_Scan55.j03,JFz_Scan55.j04,JFz_Scan55.j05,JFz_Scan55.j06,JFz_Scan55.j07,JFz_Scan55.j08,JFz_Scan55.j09,JFz_Scan55.j10,JFz_Scan55.j11,JFz_Scan55.j12,JFz_Scan55.b00_length,JFz_Scan55.b01_length,JFz_Scan55.b02_length,JFz_Scan55.b03_length,JFz_Scan55.b04_length,JFz_Scan55.b05_length,JFz_Scan55.b06_length,JFz_Scan55.b07_length,JFz_Scan55.b08_length,JFz_Scan55.b09_length,JFz_Scan55.b10_length,JFz_Scan55.b11_length,JFz_Scan55.b12_length,JFz_Scan55.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell23
theorem encoded23 : CandidateParserByteOrder.arrayBytes16 cell23=encodeQM31LE limbs23 := by
  funext i
  fin_cases i <;> rfl
theorem parser23 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell23)=
    ok (some ⟨⟨1430475257#u32,524897695#u32⟩,⟨1133391843#u32,1168527291#u32⟩⟩) :=
  JFr_EncodedCell.parser cell23 limbs23 encoded23
#print axioms encoded23
#print axioms parser23
def cell24 : Array U8 16#usize := ⟨[55#u8,96#u8,174#u8,16#u8,108#u8,240#u8,146#u8,97#u8,103#u8,1#u8,177#u8,52#u8,2#u8,91#u8,40#u8,57#u8],by rfl⟩
def limbs24 : QM31Limbs := ![⟨279863351,by change 279863351<2147483647;omega⟩,⟨1637019756,by change 1637019756<2147483647;omega⟩,⟨884015463,by change 884015463<2147483647;omega⟩,⟨958946050,by change 958946050<2147483647;omega⟩]
theorem rawCell24 : (raw.drop 384).take 16=cell24.val := by
  simp only [raw,JFz_Scan55.data,JFz_Scan55.j00,JFz_Scan55.j01,JFz_Scan55.j02,JFz_Scan55.j03,JFz_Scan55.j04,JFz_Scan55.j05,JFz_Scan55.j06,JFz_Scan55.j07,JFz_Scan55.j08,JFz_Scan55.j09,JFz_Scan55.j10,JFz_Scan55.j11,JFz_Scan55.j12,JFz_Scan55.b00_length,JFz_Scan55.b01_length,JFz_Scan55.b02_length,JFz_Scan55.b03_length,JFz_Scan55.b04_length,JFz_Scan55.b05_length,JFz_Scan55.b06_length,JFz_Scan55.b07_length,JFz_Scan55.b08_length,JFz_Scan55.b09_length,JFz_Scan55.b10_length,JFz_Scan55.b11_length,JFz_Scan55.b12_length,JFz_Scan55.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell24
theorem encoded24 : CandidateParserByteOrder.arrayBytes16 cell24=encodeQM31LE limbs24 := by
  funext i
  fin_cases i <;> rfl
theorem parser24 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell24)=
    ok (some ⟨⟨279863351#u32,1637019756#u32⟩,⟨884015463#u32,958946050#u32⟩⟩) :=
  JFr_EncodedCell.parser cell24 limbs24 encoded24
#print axioms encoded24
#print axioms parser24
def cell25 : Array U8 16#usize := ⟨[251#u8,245#u8,240#u8,74#u8,94#u8,231#u8,251#u8,48#u8,114#u8,103#u8,227#u8,78#u8,242#u8,88#u8,2#u8,109#u8],by rfl⟩
def limbs25 : QM31Limbs := ![⟨1257305595,by change 1257305595<2147483647;omega⟩,⟨821815134,by change 821815134<2147483647;omega⟩,⟨1323526002,by change 1323526002<2147483647;omega⟩,⟨1828870386,by change 1828870386<2147483647;omega⟩]
theorem rawCell25 : (raw.drop 400).take 16=cell25.val := by
  simp only [raw,JFz_Scan55.data,JFz_Scan55.j00,JFz_Scan55.j01,JFz_Scan55.j02,JFz_Scan55.j03,JFz_Scan55.j04,JFz_Scan55.j05,JFz_Scan55.j06,JFz_Scan55.j07,JFz_Scan55.j08,JFz_Scan55.j09,JFz_Scan55.j10,JFz_Scan55.j11,JFz_Scan55.j12,JFz_Scan55.b00_length,JFz_Scan55.b01_length,JFz_Scan55.b02_length,JFz_Scan55.b03_length,JFz_Scan55.b04_length,JFz_Scan55.b05_length,JFz_Scan55.b06_length,JFz_Scan55.b07_length,JFz_Scan55.b08_length,JFz_Scan55.b09_length,JFz_Scan55.b10_length,JFz_Scan55.b11_length,JFz_Scan55.b12_length,JFz_Scan55.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell25
theorem encoded25 : CandidateParserByteOrder.arrayBytes16 cell25=encodeQM31LE limbs25 := by
  funext i
  fin_cases i <;> rfl
theorem parser25 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell25)=
    ok (some ⟨⟨1257305595#u32,821815134#u32⟩,⟨1323526002#u32,1828870386#u32⟩⟩) :=
  JFr_EncodedCell.parser cell25 limbs25 encoded25
#print axioms encoded25
#print axioms parser25
def cell26 : Array U8 16#usize := ⟨[218#u8,77#u8,52#u8,46#u8,147#u8,111#u8,189#u8,27#u8,57#u8,45#u8,163#u8,110#u8,235#u8,216#u8,53#u8,108#u8],by rfl⟩
def limbs26 : QM31Limbs := ![⟨775179738,by change 775179738<2147483647;omega⟩,⟨465399699,by change 465399699<2147483647;omega⟩,⟨1856187705,by change 1856187705<2147483647;omega⟩,⟨1815468267,by change 1815468267<2147483647;omega⟩]
theorem rawCell26 : (raw.drop 416).take 16=cell26.val := by
  simp only [raw,JFz_Scan55.data,JFz_Scan55.j00,JFz_Scan55.j01,JFz_Scan55.j02,JFz_Scan55.j03,JFz_Scan55.j04,JFz_Scan55.j05,JFz_Scan55.j06,JFz_Scan55.j07,JFz_Scan55.j08,JFz_Scan55.j09,JFz_Scan55.j10,JFz_Scan55.j11,JFz_Scan55.j12,JFz_Scan55.b00_length,JFz_Scan55.b01_length,JFz_Scan55.b02_length,JFz_Scan55.b03_length,JFz_Scan55.b04_length,JFz_Scan55.b05_length,JFz_Scan55.b06_length,JFz_Scan55.b07_length,JFz_Scan55.b08_length,JFz_Scan55.b09_length,JFz_Scan55.b10_length,JFz_Scan55.b11_length,JFz_Scan55.b12_length,JFz_Scan55.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell26
theorem encoded26 : CandidateParserByteOrder.arrayBytes16 cell26=encodeQM31LE limbs26 := by
  funext i
  fin_cases i <;> rfl
theorem parser26 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell26)=
    ok (some ⟨⟨775179738#u32,465399699#u32⟩,⟨1856187705#u32,1815468267#u32⟩⟩) :=
  JFr_EncodedCell.parser cell26 limbs26 encoded26
#print axioms encoded26
#print axioms parser26
def cell27 : Array U8 16#usize := ⟨[233#u8,111#u8,149#u8,88#u8,195#u8,85#u8,116#u8,72#u8,53#u8,192#u8,154#u8,8#u8,24#u8,164#u8,157#u8,72#u8],by rfl⟩
def limbs27 : QM31Limbs := ![⟨1486188521,by change 1486188521<2147483647;omega⟩,⟨1215583683,by change 1215583683<2147483647;omega⟩,⟨144359477,by change 144359477<2147483647;omega⟩,⟨1218290712,by change 1218290712<2147483647;omega⟩]
theorem rawCell27 : (raw.drop 432).take 16=cell27.val := by
  simp only [raw,JFz_Scan55.data,JFz_Scan55.j00,JFz_Scan55.j01,JFz_Scan55.j02,JFz_Scan55.j03,JFz_Scan55.j04,JFz_Scan55.j05,JFz_Scan55.j06,JFz_Scan55.j07,JFz_Scan55.j08,JFz_Scan55.j09,JFz_Scan55.j10,JFz_Scan55.j11,JFz_Scan55.j12,JFz_Scan55.b00_length,JFz_Scan55.b01_length,JFz_Scan55.b02_length,JFz_Scan55.b03_length,JFz_Scan55.b04_length,JFz_Scan55.b05_length,JFz_Scan55.b06_length,JFz_Scan55.b07_length,JFz_Scan55.b08_length,JFz_Scan55.b09_length,JFz_Scan55.b10_length,JFz_Scan55.b11_length,JFz_Scan55.b12_length,JFz_Scan55.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell27
theorem encoded27 : CandidateParserByteOrder.arrayBytes16 cell27=encodeQM31LE limbs27 := by
  funext i
  fin_cases i <;> rfl
theorem parser27 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell27)=
    ok (some ⟨⟨1486188521#u32,1215583683#u32⟩,⟨144359477#u32,1218290712#u32⟩⟩) :=
  JFr_EncodedCell.parser cell27 limbs27 encoded27
#print axioms encoded27
#print axioms parser27
end AspisR1.JFr_Bytes07
