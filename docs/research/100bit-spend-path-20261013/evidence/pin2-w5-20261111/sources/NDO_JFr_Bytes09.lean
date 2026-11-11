import NDO_JFr_Data09
import NDO_JFr_EncodedCell
import NDO_JFz_Scan57
set_option autoImplicit false
namespace AspisR1.JFr_Bytes09
open Aeneas Aeneas.Std Result RetainedFieldByteCodec
open AspisR1PublicPreparation
open AspisS1ExtractedRoundChildren
def raw : List U8 := JFz_Scan57.data
theorem rawLength : raw.length=448 := JFz_Scan57.length
#print axioms rawLength
theorem selected : (JFx_NativeBytes.proof.val.drop 4253).take 448=raw := JFz_Scan57.selected
#print axioms selected
def cell00 : Array U8 16#usize := ⟨[61#u8,80#u8,137#u8,68#u8,63#u8,143#u8,143#u8,113#u8,211#u8,98#u8,160#u8,127#u8,234#u8,184#u8,29#u8,116#u8],by rfl⟩
def limbs00 : QM31Limbs := ![⟨1149849661,by change 1149849661<2147483647;omega⟩,⟨1905233727,by change 1905233727<2147483647;omega⟩,⟨2141217491,by change 2141217491<2147483647;omega⟩,⟨1948104938,by change 1948104938<2147483647;omega⟩]
theorem rawCell00 : (raw.drop 0).take 16=cell00.val := by
  simp only [raw,JFz_Scan57.data,JFz_Scan57.j00,JFz_Scan57.j01,JFz_Scan57.j02,JFz_Scan57.j03,JFz_Scan57.j04,JFz_Scan57.j05,JFz_Scan57.j06,JFz_Scan57.j07,JFz_Scan57.j08,JFz_Scan57.j09,JFz_Scan57.j10,JFz_Scan57.j11,JFz_Scan57.j12,JFz_Scan57.b00_length,JFz_Scan57.b01_length,JFz_Scan57.b02_length,JFz_Scan57.b03_length,JFz_Scan57.b04_length,JFz_Scan57.b05_length,JFz_Scan57.b06_length,JFz_Scan57.b07_length,JFz_Scan57.b08_length,JFz_Scan57.b09_length,JFz_Scan57.b10_length,JFz_Scan57.b11_length,JFz_Scan57.b12_length,JFz_Scan57.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell00
theorem encoded00 : CandidateParserByteOrder.arrayBytes16 cell00=encodeQM31LE limbs00 := by
  funext i
  fin_cases i <;> rfl
theorem parser00 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell00)=
    ok (some ⟨⟨1149849661#u32,1905233727#u32⟩,⟨2141217491#u32,1948104938#u32⟩⟩) :=
  JFr_EncodedCell.parser cell00 limbs00 encoded00
#print axioms encoded00
#print axioms parser00
def cell01 : Array U8 16#usize := ⟨[171#u8,172#u8,203#u8,42#u8,185#u8,237#u8,95#u8,95#u8,160#u8,75#u8,140#u8,9#u8,95#u8,5#u8,99#u8,118#u8],by rfl⟩
def limbs01 : QM31Limbs := ![⟨717991083,by change 717991083<2147483647;omega⟩,⟨1600122297,by change 1600122297<2147483647;omega⟩,⟨160189344,by change 160189344<2147483647;omega⟩,⟨1986200927,by change 1986200927<2147483647;omega⟩]
theorem rawCell01 : (raw.drop 16).take 16=cell01.val := by
  simp only [raw,JFz_Scan57.data,JFz_Scan57.j00,JFz_Scan57.j01,JFz_Scan57.j02,JFz_Scan57.j03,JFz_Scan57.j04,JFz_Scan57.j05,JFz_Scan57.j06,JFz_Scan57.j07,JFz_Scan57.j08,JFz_Scan57.j09,JFz_Scan57.j10,JFz_Scan57.j11,JFz_Scan57.j12,JFz_Scan57.b00_length,JFz_Scan57.b01_length,JFz_Scan57.b02_length,JFz_Scan57.b03_length,JFz_Scan57.b04_length,JFz_Scan57.b05_length,JFz_Scan57.b06_length,JFz_Scan57.b07_length,JFz_Scan57.b08_length,JFz_Scan57.b09_length,JFz_Scan57.b10_length,JFz_Scan57.b11_length,JFz_Scan57.b12_length,JFz_Scan57.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell01
theorem encoded01 : CandidateParserByteOrder.arrayBytes16 cell01=encodeQM31LE limbs01 := by
  funext i
  fin_cases i <;> rfl
theorem parser01 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell01)=
    ok (some ⟨⟨717991083#u32,1600122297#u32⟩,⟨160189344#u32,1986200927#u32⟩⟩) :=
  JFr_EncodedCell.parser cell01 limbs01 encoded01
#print axioms encoded01
#print axioms parser01
def cell02 : Array U8 16#usize := ⟨[119#u8,110#u8,175#u8,49#u8,15#u8,250#u8,115#u8,13#u8,229#u8,144#u8,49#u8,112#u8,0#u8,178#u8,241#u8,56#u8],by rfl⟩
def limbs02 : QM31Limbs := ![⟨833580663,by change 833580663<2147483647;omega⟩,⟨225704463,by change 225704463<2147483647;omega⟩,⟨1882296549,by change 1882296549<2147483647;omega⟩,⟨955363840,by change 955363840<2147483647;omega⟩]
theorem rawCell02 : (raw.drop 32).take 16=cell02.val := by
  simp only [raw,JFz_Scan57.data,JFz_Scan57.j00,JFz_Scan57.j01,JFz_Scan57.j02,JFz_Scan57.j03,JFz_Scan57.j04,JFz_Scan57.j05,JFz_Scan57.j06,JFz_Scan57.j07,JFz_Scan57.j08,JFz_Scan57.j09,JFz_Scan57.j10,JFz_Scan57.j11,JFz_Scan57.j12,JFz_Scan57.b00_length,JFz_Scan57.b01_length,JFz_Scan57.b02_length,JFz_Scan57.b03_length,JFz_Scan57.b04_length,JFz_Scan57.b05_length,JFz_Scan57.b06_length,JFz_Scan57.b07_length,JFz_Scan57.b08_length,JFz_Scan57.b09_length,JFz_Scan57.b10_length,JFz_Scan57.b11_length,JFz_Scan57.b12_length,JFz_Scan57.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell02
theorem encoded02 : CandidateParserByteOrder.arrayBytes16 cell02=encodeQM31LE limbs02 := by
  funext i
  fin_cases i <;> rfl
theorem parser02 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell02)=
    ok (some ⟨⟨833580663#u32,225704463#u32⟩,⟨1882296549#u32,955363840#u32⟩⟩) :=
  JFr_EncodedCell.parser cell02 limbs02 encoded02
#print axioms encoded02
#print axioms parser02
def cell03 : Array U8 16#usize := ⟨[143#u8,31#u8,214#u8,118#u8,206#u8,53#u8,160#u8,47#u8,237#u8,195#u8,3#u8,40#u8,151#u8,212#u8,207#u8,1#u8],by rfl⟩
def limbs03 : QM31Limbs := ![⟨1993744271,by change 1993744271<2147483647;omega⟩,⟨799028686,by change 799028686<2147483647;omega⟩,⟨671335405,by change 671335405<2147483647;omega⟩,⟨30397591,by change 30397591<2147483647;omega⟩]
theorem rawCell03 : (raw.drop 48).take 16=cell03.val := by
  simp only [raw,JFz_Scan57.data,JFz_Scan57.j00,JFz_Scan57.j01,JFz_Scan57.j02,JFz_Scan57.j03,JFz_Scan57.j04,JFz_Scan57.j05,JFz_Scan57.j06,JFz_Scan57.j07,JFz_Scan57.j08,JFz_Scan57.j09,JFz_Scan57.j10,JFz_Scan57.j11,JFz_Scan57.j12,JFz_Scan57.b00_length,JFz_Scan57.b01_length,JFz_Scan57.b02_length,JFz_Scan57.b03_length,JFz_Scan57.b04_length,JFz_Scan57.b05_length,JFz_Scan57.b06_length,JFz_Scan57.b07_length,JFz_Scan57.b08_length,JFz_Scan57.b09_length,JFz_Scan57.b10_length,JFz_Scan57.b11_length,JFz_Scan57.b12_length,JFz_Scan57.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell03
theorem encoded03 : CandidateParserByteOrder.arrayBytes16 cell03=encodeQM31LE limbs03 := by
  funext i
  fin_cases i <;> rfl
theorem parser03 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell03)=
    ok (some ⟨⟨1993744271#u32,799028686#u32⟩,⟨671335405#u32,30397591#u32⟩⟩) :=
  JFr_EncodedCell.parser cell03 limbs03 encoded03
#print axioms encoded03
#print axioms parser03
def cell04 : Array U8 16#usize := ⟨[200#u8,189#u8,1#u8,88#u8,36#u8,116#u8,34#u8,22#u8,189#u8,156#u8,222#u8,72#u8,216#u8,12#u8,3#u8,87#u8],by rfl⟩
def limbs04 : QM31Limbs := ![⟨1476509128,by change 1476509128<2147483647;omega⟩,⟨371356708,by change 371356708<2147483647;omega⟩,⟨1222548669,by change 1222548669<2147483647;omega⟩,⟨1459817688,by change 1459817688<2147483647;omega⟩]
theorem rawCell04 : (raw.drop 64).take 16=cell04.val := by
  simp only [raw,JFz_Scan57.data,JFz_Scan57.j00,JFz_Scan57.j01,JFz_Scan57.j02,JFz_Scan57.j03,JFz_Scan57.j04,JFz_Scan57.j05,JFz_Scan57.j06,JFz_Scan57.j07,JFz_Scan57.j08,JFz_Scan57.j09,JFz_Scan57.j10,JFz_Scan57.j11,JFz_Scan57.j12,JFz_Scan57.b00_length,JFz_Scan57.b01_length,JFz_Scan57.b02_length,JFz_Scan57.b03_length,JFz_Scan57.b04_length,JFz_Scan57.b05_length,JFz_Scan57.b06_length,JFz_Scan57.b07_length,JFz_Scan57.b08_length,JFz_Scan57.b09_length,JFz_Scan57.b10_length,JFz_Scan57.b11_length,JFz_Scan57.b12_length,JFz_Scan57.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell04
theorem encoded04 : CandidateParserByteOrder.arrayBytes16 cell04=encodeQM31LE limbs04 := by
  funext i
  fin_cases i <;> rfl
theorem parser04 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell04)=
    ok (some ⟨⟨1476509128#u32,371356708#u32⟩,⟨1222548669#u32,1459817688#u32⟩⟩) :=
  JFr_EncodedCell.parser cell04 limbs04 encoded04
#print axioms encoded04
#print axioms parser04
def cell05 : Array U8 16#usize := ⟨[134#u8,22#u8,114#u8,111#u8,63#u8,143#u8,85#u8,99#u8,61#u8,19#u8,107#u8,91#u8,66#u8,114#u8,87#u8,26#u8],by rfl⟩
def limbs05 : QM31Limbs := ![⟨1869747846,by change 1869747846<2147483647;omega⟩,⟨1666551615,by change 1666551615<2147483647;omega⟩,⟨1533743933,by change 1533743933<2147483647;omega⟩,⟨441938498,by change 441938498<2147483647;omega⟩]
theorem rawCell05 : (raw.drop 80).take 16=cell05.val := by
  simp only [raw,JFz_Scan57.data,JFz_Scan57.j00,JFz_Scan57.j01,JFz_Scan57.j02,JFz_Scan57.j03,JFz_Scan57.j04,JFz_Scan57.j05,JFz_Scan57.j06,JFz_Scan57.j07,JFz_Scan57.j08,JFz_Scan57.j09,JFz_Scan57.j10,JFz_Scan57.j11,JFz_Scan57.j12,JFz_Scan57.b00_length,JFz_Scan57.b01_length,JFz_Scan57.b02_length,JFz_Scan57.b03_length,JFz_Scan57.b04_length,JFz_Scan57.b05_length,JFz_Scan57.b06_length,JFz_Scan57.b07_length,JFz_Scan57.b08_length,JFz_Scan57.b09_length,JFz_Scan57.b10_length,JFz_Scan57.b11_length,JFz_Scan57.b12_length,JFz_Scan57.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell05
theorem encoded05 : CandidateParserByteOrder.arrayBytes16 cell05=encodeQM31LE limbs05 := by
  funext i
  fin_cases i <;> rfl
theorem parser05 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell05)=
    ok (some ⟨⟨1869747846#u32,1666551615#u32⟩,⟨1533743933#u32,441938498#u32⟩⟩) :=
  JFr_EncodedCell.parser cell05 limbs05 encoded05
#print axioms encoded05
#print axioms parser05
def cell06 : Array U8 16#usize := ⟨[80#u8,93#u8,52#u8,59#u8,29#u8,166#u8,124#u8,13#u8,203#u8,170#u8,32#u8,2#u8,51#u8,61#u8,15#u8,14#u8],by rfl⟩
def limbs06 : QM31Limbs := ![⟨993287504,by change 993287504<2147483647;omega⟩,⟨226272797,by change 226272797<2147483647;omega⟩,⟨35695307,by change 35695307<2147483647;omega⟩,⟨235879731,by change 235879731<2147483647;omega⟩]
theorem rawCell06 : (raw.drop 96).take 16=cell06.val := by
  simp only [raw,JFz_Scan57.data,JFz_Scan57.j00,JFz_Scan57.j01,JFz_Scan57.j02,JFz_Scan57.j03,JFz_Scan57.j04,JFz_Scan57.j05,JFz_Scan57.j06,JFz_Scan57.j07,JFz_Scan57.j08,JFz_Scan57.j09,JFz_Scan57.j10,JFz_Scan57.j11,JFz_Scan57.j12,JFz_Scan57.b00_length,JFz_Scan57.b01_length,JFz_Scan57.b02_length,JFz_Scan57.b03_length,JFz_Scan57.b04_length,JFz_Scan57.b05_length,JFz_Scan57.b06_length,JFz_Scan57.b07_length,JFz_Scan57.b08_length,JFz_Scan57.b09_length,JFz_Scan57.b10_length,JFz_Scan57.b11_length,JFz_Scan57.b12_length,JFz_Scan57.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell06
theorem encoded06 : CandidateParserByteOrder.arrayBytes16 cell06=encodeQM31LE limbs06 := by
  funext i
  fin_cases i <;> rfl
theorem parser06 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell06)=
    ok (some ⟨⟨993287504#u32,226272797#u32⟩,⟨35695307#u32,235879731#u32⟩⟩) :=
  JFr_EncodedCell.parser cell06 limbs06 encoded06
#print axioms encoded06
#print axioms parser06
def cell07 : Array U8 16#usize := ⟨[240#u8,245#u8,142#u8,87#u8,237#u8,57#u8,127#u8,50#u8,142#u8,112#u8,53#u8,117#u8,133#u8,141#u8,32#u8,33#u8],by rfl⟩
def limbs07 : QM31Limbs := ![⟨1468986864,by change 1468986864<2147483647;omega⟩,⟨847198701,by change 847198701<2147483647;omega⟩,⟨1966436494,by change 1966436494<2147483647;omega⟩,⟨555781509,by change 555781509<2147483647;omega⟩]
theorem rawCell07 : (raw.drop 112).take 16=cell07.val := by
  simp only [raw,JFz_Scan57.data,JFz_Scan57.j00,JFz_Scan57.j01,JFz_Scan57.j02,JFz_Scan57.j03,JFz_Scan57.j04,JFz_Scan57.j05,JFz_Scan57.j06,JFz_Scan57.j07,JFz_Scan57.j08,JFz_Scan57.j09,JFz_Scan57.j10,JFz_Scan57.j11,JFz_Scan57.j12,JFz_Scan57.b00_length,JFz_Scan57.b01_length,JFz_Scan57.b02_length,JFz_Scan57.b03_length,JFz_Scan57.b04_length,JFz_Scan57.b05_length,JFz_Scan57.b06_length,JFz_Scan57.b07_length,JFz_Scan57.b08_length,JFz_Scan57.b09_length,JFz_Scan57.b10_length,JFz_Scan57.b11_length,JFz_Scan57.b12_length,JFz_Scan57.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell07
theorem encoded07 : CandidateParserByteOrder.arrayBytes16 cell07=encodeQM31LE limbs07 := by
  funext i
  fin_cases i <;> rfl
theorem parser07 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell07)=
    ok (some ⟨⟨1468986864#u32,847198701#u32⟩,⟨1966436494#u32,555781509#u32⟩⟩) :=
  JFr_EncodedCell.parser cell07 limbs07 encoded07
#print axioms encoded07
#print axioms parser07
def cell08 : Array U8 16#usize := ⟨[175#u8,139#u8,85#u8,112#u8,225#u8,165#u8,73#u8,104#u8,255#u8,201#u8,238#u8,17#u8,217#u8,193#u8,134#u8,83#u8],by rfl⟩
def limbs08 : QM31Limbs := ![⟨1884654511,by change 1884654511<2147483647;omega⟩,⟨1749657057,by change 1749657057<2147483647;omega⟩,⟨300861951,by change 300861951<2147483647;omega⟩,⟨1401340377,by change 1401340377<2147483647;omega⟩]
theorem rawCell08 : (raw.drop 128).take 16=cell08.val := by
  simp only [raw,JFz_Scan57.data,JFz_Scan57.j00,JFz_Scan57.j01,JFz_Scan57.j02,JFz_Scan57.j03,JFz_Scan57.j04,JFz_Scan57.j05,JFz_Scan57.j06,JFz_Scan57.j07,JFz_Scan57.j08,JFz_Scan57.j09,JFz_Scan57.j10,JFz_Scan57.j11,JFz_Scan57.j12,JFz_Scan57.b00_length,JFz_Scan57.b01_length,JFz_Scan57.b02_length,JFz_Scan57.b03_length,JFz_Scan57.b04_length,JFz_Scan57.b05_length,JFz_Scan57.b06_length,JFz_Scan57.b07_length,JFz_Scan57.b08_length,JFz_Scan57.b09_length,JFz_Scan57.b10_length,JFz_Scan57.b11_length,JFz_Scan57.b12_length,JFz_Scan57.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell08
theorem encoded08 : CandidateParserByteOrder.arrayBytes16 cell08=encodeQM31LE limbs08 := by
  funext i
  fin_cases i <;> rfl
theorem parser08 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell08)=
    ok (some ⟨⟨1884654511#u32,1749657057#u32⟩,⟨300861951#u32,1401340377#u32⟩⟩) :=
  JFr_EncodedCell.parser cell08 limbs08 encoded08
#print axioms encoded08
#print axioms parser08
def cell09 : Array U8 16#usize := ⟨[129#u8,89#u8,122#u8,32#u8,233#u8,130#u8,2#u8,79#u8,206#u8,235#u8,150#u8,19#u8,70#u8,171#u8,154#u8,72#u8],by rfl⟩
def limbs09 : QM31Limbs := ![⟨544889217,by change 544889217<2147483647;omega⟩,⟨1325564649,by change 1325564649<2147483647;omega⟩,⟨328657870,by change 328657870<2147483647;omega⟩,⟨1218095942,by change 1218095942<2147483647;omega⟩]
theorem rawCell09 : (raw.drop 144).take 16=cell09.val := by
  simp only [raw,JFz_Scan57.data,JFz_Scan57.j00,JFz_Scan57.j01,JFz_Scan57.j02,JFz_Scan57.j03,JFz_Scan57.j04,JFz_Scan57.j05,JFz_Scan57.j06,JFz_Scan57.j07,JFz_Scan57.j08,JFz_Scan57.j09,JFz_Scan57.j10,JFz_Scan57.j11,JFz_Scan57.j12,JFz_Scan57.b00_length,JFz_Scan57.b01_length,JFz_Scan57.b02_length,JFz_Scan57.b03_length,JFz_Scan57.b04_length,JFz_Scan57.b05_length,JFz_Scan57.b06_length,JFz_Scan57.b07_length,JFz_Scan57.b08_length,JFz_Scan57.b09_length,JFz_Scan57.b10_length,JFz_Scan57.b11_length,JFz_Scan57.b12_length,JFz_Scan57.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell09
theorem encoded09 : CandidateParserByteOrder.arrayBytes16 cell09=encodeQM31LE limbs09 := by
  funext i
  fin_cases i <;> rfl
theorem parser09 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell09)=
    ok (some ⟨⟨544889217#u32,1325564649#u32⟩,⟨328657870#u32,1218095942#u32⟩⟩) :=
  JFr_EncodedCell.parser cell09 limbs09 encoded09
#print axioms encoded09
#print axioms parser09
def cell10 : Array U8 16#usize := ⟨[250#u8,121#u8,21#u8,42#u8,160#u8,176#u8,91#u8,7#u8,99#u8,0#u8,208#u8,117#u8,210#u8,201#u8,203#u8,1#u8],by rfl⟩
def limbs10 : QM31Limbs := ![⟨706050554,by change 706050554<2147483647;omega⟩,⟨123449504,by change 123449504<2147483647;omega⟩,⟨1976565859,by change 1976565859<2147483647;omega⟩,⟨30132690,by change 30132690<2147483647;omega⟩]
theorem rawCell10 : (raw.drop 160).take 16=cell10.val := by
  simp only [raw,JFz_Scan57.data,JFz_Scan57.j00,JFz_Scan57.j01,JFz_Scan57.j02,JFz_Scan57.j03,JFz_Scan57.j04,JFz_Scan57.j05,JFz_Scan57.j06,JFz_Scan57.j07,JFz_Scan57.j08,JFz_Scan57.j09,JFz_Scan57.j10,JFz_Scan57.j11,JFz_Scan57.j12,JFz_Scan57.b00_length,JFz_Scan57.b01_length,JFz_Scan57.b02_length,JFz_Scan57.b03_length,JFz_Scan57.b04_length,JFz_Scan57.b05_length,JFz_Scan57.b06_length,JFz_Scan57.b07_length,JFz_Scan57.b08_length,JFz_Scan57.b09_length,JFz_Scan57.b10_length,JFz_Scan57.b11_length,JFz_Scan57.b12_length,JFz_Scan57.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell10
theorem encoded10 : CandidateParserByteOrder.arrayBytes16 cell10=encodeQM31LE limbs10 := by
  funext i
  fin_cases i <;> rfl
theorem parser10 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell10)=
    ok (some ⟨⟨706050554#u32,123449504#u32⟩,⟨1976565859#u32,30132690#u32⟩⟩) :=
  JFr_EncodedCell.parser cell10 limbs10 encoded10
#print axioms encoded10
#print axioms parser10
def cell11 : Array U8 16#usize := ⟨[167#u8,84#u8,86#u8,41#u8,28#u8,45#u8,31#u8,34#u8,230#u8,254#u8,216#u8,73#u8,124#u8,204#u8,17#u8,39#u8],by rfl⟩
def limbs11 : QM31Limbs := ![⟨693523623,by change 693523623<2147483647;omega⟩,⟨572468508,by change 572468508<2147483647;omega⟩,⟨1238957798,by change 1238957798<2147483647;omega⟩,⟨655477884,by change 655477884<2147483647;omega⟩]
theorem rawCell11 : (raw.drop 176).take 16=cell11.val := by
  simp only [raw,JFz_Scan57.data,JFz_Scan57.j00,JFz_Scan57.j01,JFz_Scan57.j02,JFz_Scan57.j03,JFz_Scan57.j04,JFz_Scan57.j05,JFz_Scan57.j06,JFz_Scan57.j07,JFz_Scan57.j08,JFz_Scan57.j09,JFz_Scan57.j10,JFz_Scan57.j11,JFz_Scan57.j12,JFz_Scan57.b00_length,JFz_Scan57.b01_length,JFz_Scan57.b02_length,JFz_Scan57.b03_length,JFz_Scan57.b04_length,JFz_Scan57.b05_length,JFz_Scan57.b06_length,JFz_Scan57.b07_length,JFz_Scan57.b08_length,JFz_Scan57.b09_length,JFz_Scan57.b10_length,JFz_Scan57.b11_length,JFz_Scan57.b12_length,JFz_Scan57.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell11
theorem encoded11 : CandidateParserByteOrder.arrayBytes16 cell11=encodeQM31LE limbs11 := by
  funext i
  fin_cases i <;> rfl
theorem parser11 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell11)=
    ok (some ⟨⟨693523623#u32,572468508#u32⟩,⟨1238957798#u32,655477884#u32⟩⟩) :=
  JFr_EncodedCell.parser cell11 limbs11 encoded11
#print axioms encoded11
#print axioms parser11
def cell12 : Array U8 16#usize := ⟨[152#u8,134#u8,214#u8,3#u8,51#u8,162#u8,70#u8,14#u8,213#u8,187#u8,106#u8,46#u8,211#u8,63#u8,101#u8,7#u8],by rfl⟩
def limbs12 : QM31Limbs := ![⟨64390808,by change 64390808<2147483647;omega⟩,⟨239510067,by change 239510067<2147483647;omega⟩,⟨778746837,by change 778746837<2147483647;omega⟩,⟨124075987,by change 124075987<2147483647;omega⟩]
theorem rawCell12 : (raw.drop 192).take 16=cell12.val := by
  simp only [raw,JFz_Scan57.data,JFz_Scan57.j00,JFz_Scan57.j01,JFz_Scan57.j02,JFz_Scan57.j03,JFz_Scan57.j04,JFz_Scan57.j05,JFz_Scan57.j06,JFz_Scan57.j07,JFz_Scan57.j08,JFz_Scan57.j09,JFz_Scan57.j10,JFz_Scan57.j11,JFz_Scan57.j12,JFz_Scan57.b00_length,JFz_Scan57.b01_length,JFz_Scan57.b02_length,JFz_Scan57.b03_length,JFz_Scan57.b04_length,JFz_Scan57.b05_length,JFz_Scan57.b06_length,JFz_Scan57.b07_length,JFz_Scan57.b08_length,JFz_Scan57.b09_length,JFz_Scan57.b10_length,JFz_Scan57.b11_length,JFz_Scan57.b12_length,JFz_Scan57.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell12
theorem encoded12 : CandidateParserByteOrder.arrayBytes16 cell12=encodeQM31LE limbs12 := by
  funext i
  fin_cases i <;> rfl
theorem parser12 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell12)=
    ok (some ⟨⟨64390808#u32,239510067#u32⟩,⟨778746837#u32,124075987#u32⟩⟩) :=
  JFr_EncodedCell.parser cell12 limbs12 encoded12
#print axioms encoded12
#print axioms parser12
def cell13 : Array U8 16#usize := ⟨[51#u8,236#u8,200#u8,62#u8,115#u8,4#u8,104#u8,104#u8,222#u8,111#u8,191#u8,87#u8,92#u8,51#u8,197#u8,55#u8],by rfl⟩
def limbs13 : QM31Limbs := ![⟨1053355059,by change 1053355059<2147483647;omega⟩,⟨1751647347,by change 1751647347<2147483647;omega⟩,⟨1472163806,by change 1472163806<2147483647;omega⟩,⟨935670620,by change 935670620<2147483647;omega⟩]
theorem rawCell13 : (raw.drop 208).take 16=cell13.val := by
  simp only [raw,JFz_Scan57.data,JFz_Scan57.j00,JFz_Scan57.j01,JFz_Scan57.j02,JFz_Scan57.j03,JFz_Scan57.j04,JFz_Scan57.j05,JFz_Scan57.j06,JFz_Scan57.j07,JFz_Scan57.j08,JFz_Scan57.j09,JFz_Scan57.j10,JFz_Scan57.j11,JFz_Scan57.j12,JFz_Scan57.b00_length,JFz_Scan57.b01_length,JFz_Scan57.b02_length,JFz_Scan57.b03_length,JFz_Scan57.b04_length,JFz_Scan57.b05_length,JFz_Scan57.b06_length,JFz_Scan57.b07_length,JFz_Scan57.b08_length,JFz_Scan57.b09_length,JFz_Scan57.b10_length,JFz_Scan57.b11_length,JFz_Scan57.b12_length,JFz_Scan57.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell13
theorem encoded13 : CandidateParserByteOrder.arrayBytes16 cell13=encodeQM31LE limbs13 := by
  funext i
  fin_cases i <;> rfl
theorem parser13 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell13)=
    ok (some ⟨⟨1053355059#u32,1751647347#u32⟩,⟨1472163806#u32,935670620#u32⟩⟩) :=
  JFr_EncodedCell.parser cell13 limbs13 encoded13
#print axioms encoded13
#print axioms parser13
def cell14 : Array U8 16#usize := ⟨[80#u8,131#u8,190#u8,66#u8,217#u8,74#u8,174#u8,47#u8,163#u8,0#u8,26#u8,111#u8,38#u8,153#u8,72#u8,26#u8],by rfl⟩
def limbs14 : QM31Limbs := ![⟨1119781712,by change 1119781712<2147483647;omega⟩,⟨799951577,by change 799951577<2147483647;omega⟩,⟨1863975075,by change 1863975075<2147483647;omega⟩,⟨440965414,by change 440965414<2147483647;omega⟩]
theorem rawCell14 : (raw.drop 224).take 16=cell14.val := by
  simp only [raw,JFz_Scan57.data,JFz_Scan57.j00,JFz_Scan57.j01,JFz_Scan57.j02,JFz_Scan57.j03,JFz_Scan57.j04,JFz_Scan57.j05,JFz_Scan57.j06,JFz_Scan57.j07,JFz_Scan57.j08,JFz_Scan57.j09,JFz_Scan57.j10,JFz_Scan57.j11,JFz_Scan57.j12,JFz_Scan57.b00_length,JFz_Scan57.b01_length,JFz_Scan57.b02_length,JFz_Scan57.b03_length,JFz_Scan57.b04_length,JFz_Scan57.b05_length,JFz_Scan57.b06_length,JFz_Scan57.b07_length,JFz_Scan57.b08_length,JFz_Scan57.b09_length,JFz_Scan57.b10_length,JFz_Scan57.b11_length,JFz_Scan57.b12_length,JFz_Scan57.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell14
theorem encoded14 : CandidateParserByteOrder.arrayBytes16 cell14=encodeQM31LE limbs14 := by
  funext i
  fin_cases i <;> rfl
theorem parser14 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell14)=
    ok (some ⟨⟨1119781712#u32,799951577#u32⟩,⟨1863975075#u32,440965414#u32⟩⟩) :=
  JFr_EncodedCell.parser cell14 limbs14 encoded14
#print axioms encoded14
#print axioms parser14
def cell15 : Array U8 16#usize := ⟨[243#u8,76#u8,222#u8,38#u8,136#u8,135#u8,74#u8,11#u8,189#u8,223#u8,234#u8,27#u8,47#u8,37#u8,144#u8,16#u8],by rfl⟩
def limbs15 : QM31Limbs := ![⟨652102899,by change 652102899<2147483647;omega⟩,⟨189433736,by change 189433736<2147483647;omega⟩,⟨468377533,by change 468377533<2147483647;omega⟩,⟨277882159,by change 277882159<2147483647;omega⟩]
theorem rawCell15 : (raw.drop 240).take 16=cell15.val := by
  simp only [raw,JFz_Scan57.data,JFz_Scan57.j00,JFz_Scan57.j01,JFz_Scan57.j02,JFz_Scan57.j03,JFz_Scan57.j04,JFz_Scan57.j05,JFz_Scan57.j06,JFz_Scan57.j07,JFz_Scan57.j08,JFz_Scan57.j09,JFz_Scan57.j10,JFz_Scan57.j11,JFz_Scan57.j12,JFz_Scan57.b00_length,JFz_Scan57.b01_length,JFz_Scan57.b02_length,JFz_Scan57.b03_length,JFz_Scan57.b04_length,JFz_Scan57.b05_length,JFz_Scan57.b06_length,JFz_Scan57.b07_length,JFz_Scan57.b08_length,JFz_Scan57.b09_length,JFz_Scan57.b10_length,JFz_Scan57.b11_length,JFz_Scan57.b12_length,JFz_Scan57.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell15
theorem encoded15 : CandidateParserByteOrder.arrayBytes16 cell15=encodeQM31LE limbs15 := by
  funext i
  fin_cases i <;> rfl
theorem parser15 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell15)=
    ok (some ⟨⟨652102899#u32,189433736#u32⟩,⟨468377533#u32,277882159#u32⟩⟩) :=
  JFr_EncodedCell.parser cell15 limbs15 encoded15
#print axioms encoded15
#print axioms parser15
def cell16 : Array U8 16#usize := ⟨[66#u8,2#u8,9#u8,116#u8,226#u8,254#u8,119#u8,88#u8,44#u8,108#u8,217#u8,64#u8,43#u8,186#u8,189#u8,111#u8],by rfl⟩
def limbs16 : QM31Limbs := ![⟨1946747458,by change 1946747458<2147483647;omega⟩,⟨1484259042,by change 1484259042<2147483647;omega⟩,⟨1087990828,by change 1087990828<2147483647;omega⟩,⟨1874704939,by change 1874704939<2147483647;omega⟩]
theorem rawCell16 : (raw.drop 256).take 16=cell16.val := by
  simp only [raw,JFz_Scan57.data,JFz_Scan57.j00,JFz_Scan57.j01,JFz_Scan57.j02,JFz_Scan57.j03,JFz_Scan57.j04,JFz_Scan57.j05,JFz_Scan57.j06,JFz_Scan57.j07,JFz_Scan57.j08,JFz_Scan57.j09,JFz_Scan57.j10,JFz_Scan57.j11,JFz_Scan57.j12,JFz_Scan57.b00_length,JFz_Scan57.b01_length,JFz_Scan57.b02_length,JFz_Scan57.b03_length,JFz_Scan57.b04_length,JFz_Scan57.b05_length,JFz_Scan57.b06_length,JFz_Scan57.b07_length,JFz_Scan57.b08_length,JFz_Scan57.b09_length,JFz_Scan57.b10_length,JFz_Scan57.b11_length,JFz_Scan57.b12_length,JFz_Scan57.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell16
theorem encoded16 : CandidateParserByteOrder.arrayBytes16 cell16=encodeQM31LE limbs16 := by
  funext i
  fin_cases i <;> rfl
theorem parser16 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell16)=
    ok (some ⟨⟨1946747458#u32,1484259042#u32⟩,⟨1087990828#u32,1874704939#u32⟩⟩) :=
  JFr_EncodedCell.parser cell16 limbs16 encoded16
#print axioms encoded16
#print axioms parser16
def cell17 : Array U8 16#usize := ⟨[53#u8,213#u8,113#u8,107#u8,140#u8,241#u8,11#u8,98#u8,220#u8,16#u8,97#u8,58#u8,46#u8,111#u8,226#u8,30#u8],by rfl⟩
def limbs17 : QM31Limbs := ![⟨1802622261,by change 1802622261<2147483647;omega⟩,⟨1644949900,by change 1644949900<2147483647;omega⟩,⟨979439836,by change 979439836<2147483647;omega⟩,⟨518156078,by change 518156078<2147483647;omega⟩]
theorem rawCell17 : (raw.drop 272).take 16=cell17.val := by
  simp only [raw,JFz_Scan57.data,JFz_Scan57.j00,JFz_Scan57.j01,JFz_Scan57.j02,JFz_Scan57.j03,JFz_Scan57.j04,JFz_Scan57.j05,JFz_Scan57.j06,JFz_Scan57.j07,JFz_Scan57.j08,JFz_Scan57.j09,JFz_Scan57.j10,JFz_Scan57.j11,JFz_Scan57.j12,JFz_Scan57.b00_length,JFz_Scan57.b01_length,JFz_Scan57.b02_length,JFz_Scan57.b03_length,JFz_Scan57.b04_length,JFz_Scan57.b05_length,JFz_Scan57.b06_length,JFz_Scan57.b07_length,JFz_Scan57.b08_length,JFz_Scan57.b09_length,JFz_Scan57.b10_length,JFz_Scan57.b11_length,JFz_Scan57.b12_length,JFz_Scan57.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell17
theorem encoded17 : CandidateParserByteOrder.arrayBytes16 cell17=encodeQM31LE limbs17 := by
  funext i
  fin_cases i <;> rfl
theorem parser17 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell17)=
    ok (some ⟨⟨1802622261#u32,1644949900#u32⟩,⟨979439836#u32,518156078#u32⟩⟩) :=
  JFr_EncodedCell.parser cell17 limbs17 encoded17
#print axioms encoded17
#print axioms parser17
def cell18 : Array U8 16#usize := ⟨[126#u8,28#u8,192#u8,3#u8,53#u8,5#u8,202#u8,14#u8,98#u8,25#u8,104#u8,86#u8,39#u8,251#u8,242#u8,75#u8],by rfl⟩
def limbs18 : QM31Limbs := ![⟨62921854,by change 62921854<2147483647;omega⟩,⟨248120629,by change 248120629<2147483647;omega⟩,⟨1449662818,by change 1449662818<2147483647;omega⟩,⟨1274215207,by change 1274215207<2147483647;omega⟩]
theorem rawCell18 : (raw.drop 288).take 16=cell18.val := by
  simp only [raw,JFz_Scan57.data,JFz_Scan57.j00,JFz_Scan57.j01,JFz_Scan57.j02,JFz_Scan57.j03,JFz_Scan57.j04,JFz_Scan57.j05,JFz_Scan57.j06,JFz_Scan57.j07,JFz_Scan57.j08,JFz_Scan57.j09,JFz_Scan57.j10,JFz_Scan57.j11,JFz_Scan57.j12,JFz_Scan57.b00_length,JFz_Scan57.b01_length,JFz_Scan57.b02_length,JFz_Scan57.b03_length,JFz_Scan57.b04_length,JFz_Scan57.b05_length,JFz_Scan57.b06_length,JFz_Scan57.b07_length,JFz_Scan57.b08_length,JFz_Scan57.b09_length,JFz_Scan57.b10_length,JFz_Scan57.b11_length,JFz_Scan57.b12_length,JFz_Scan57.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell18
theorem encoded18 : CandidateParserByteOrder.arrayBytes16 cell18=encodeQM31LE limbs18 := by
  funext i
  fin_cases i <;> rfl
theorem parser18 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell18)=
    ok (some ⟨⟨62921854#u32,248120629#u32⟩,⟨1449662818#u32,1274215207#u32⟩⟩) :=
  JFr_EncodedCell.parser cell18 limbs18 encoded18
#print axioms encoded18
#print axioms parser18
def cell19 : Array U8 16#usize := ⟨[35#u8,163#u8,172#u8,11#u8,46#u8,115#u8,180#u8,26#u8,191#u8,189#u8,128#u8,68#u8,55#u8,173#u8,167#u8,69#u8],by rfl⟩
def limbs19 : QM31Limbs := ![⟨195863331,by change 195863331<2147483647;omega⟩,⟨448033582,by change 448033582<2147483647;omega⟩,⟨1149287871,by change 1149287871<2147483647;omega⟩,⟨1168616759,by change 1168616759<2147483647;omega⟩]
theorem rawCell19 : (raw.drop 304).take 16=cell19.val := by
  simp only [raw,JFz_Scan57.data,JFz_Scan57.j00,JFz_Scan57.j01,JFz_Scan57.j02,JFz_Scan57.j03,JFz_Scan57.j04,JFz_Scan57.j05,JFz_Scan57.j06,JFz_Scan57.j07,JFz_Scan57.j08,JFz_Scan57.j09,JFz_Scan57.j10,JFz_Scan57.j11,JFz_Scan57.j12,JFz_Scan57.b00_length,JFz_Scan57.b01_length,JFz_Scan57.b02_length,JFz_Scan57.b03_length,JFz_Scan57.b04_length,JFz_Scan57.b05_length,JFz_Scan57.b06_length,JFz_Scan57.b07_length,JFz_Scan57.b08_length,JFz_Scan57.b09_length,JFz_Scan57.b10_length,JFz_Scan57.b11_length,JFz_Scan57.b12_length,JFz_Scan57.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell19
theorem encoded19 : CandidateParserByteOrder.arrayBytes16 cell19=encodeQM31LE limbs19 := by
  funext i
  fin_cases i <;> rfl
theorem parser19 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell19)=
    ok (some ⟨⟨195863331#u32,448033582#u32⟩,⟨1149287871#u32,1168616759#u32⟩⟩) :=
  JFr_EncodedCell.parser cell19 limbs19 encoded19
#print axioms encoded19
#print axioms parser19
def cell20 : Array U8 16#usize := ⟨[230#u8,90#u8,15#u8,66#u8,10#u8,138#u8,141#u8,5#u8,171#u8,215#u8,235#u8,76#u8,199#u8,92#u8,20#u8,126#u8],by rfl⟩
def limbs20 : QM31Limbs := ![⟨1108302566,by change 1108302566<2147483647;omega⟩,⟨93161994,by change 93161994<2147483647;omega⟩,⟨1290524587,by change 1290524587<2147483647;omega⟩,⟨2115263687,by change 2115263687<2147483647;omega⟩]
theorem rawCell20 : (raw.drop 320).take 16=cell20.val := by
  simp only [raw,JFz_Scan57.data,JFz_Scan57.j00,JFz_Scan57.j01,JFz_Scan57.j02,JFz_Scan57.j03,JFz_Scan57.j04,JFz_Scan57.j05,JFz_Scan57.j06,JFz_Scan57.j07,JFz_Scan57.j08,JFz_Scan57.j09,JFz_Scan57.j10,JFz_Scan57.j11,JFz_Scan57.j12,JFz_Scan57.b00_length,JFz_Scan57.b01_length,JFz_Scan57.b02_length,JFz_Scan57.b03_length,JFz_Scan57.b04_length,JFz_Scan57.b05_length,JFz_Scan57.b06_length,JFz_Scan57.b07_length,JFz_Scan57.b08_length,JFz_Scan57.b09_length,JFz_Scan57.b10_length,JFz_Scan57.b11_length,JFz_Scan57.b12_length,JFz_Scan57.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell20
theorem encoded20 : CandidateParserByteOrder.arrayBytes16 cell20=encodeQM31LE limbs20 := by
  funext i
  fin_cases i <;> rfl
theorem parser20 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell20)=
    ok (some ⟨⟨1108302566#u32,93161994#u32⟩,⟨1290524587#u32,2115263687#u32⟩⟩) :=
  JFr_EncodedCell.parser cell20 limbs20 encoded20
#print axioms encoded20
#print axioms parser20
def cell21 : Array U8 16#usize := ⟨[154#u8,133#u8,148#u8,49#u8,127#u8,152#u8,234#u8,28#u8,191#u8,114#u8,146#u8,17#u8,178#u8,90#u8,118#u8,105#u8],by rfl⟩
def limbs21 : QM31Limbs := ![⟨831817114,by change 831817114<2147483647;omega⟩,⟨485136511,by change 485136511<2147483647;omega⟩,⟨294810303,by change 294810303<2147483647;omega⟩,⟨1769364146,by change 1769364146<2147483647;omega⟩]
theorem rawCell21 : (raw.drop 336).take 16=cell21.val := by
  simp only [raw,JFz_Scan57.data,JFz_Scan57.j00,JFz_Scan57.j01,JFz_Scan57.j02,JFz_Scan57.j03,JFz_Scan57.j04,JFz_Scan57.j05,JFz_Scan57.j06,JFz_Scan57.j07,JFz_Scan57.j08,JFz_Scan57.j09,JFz_Scan57.j10,JFz_Scan57.j11,JFz_Scan57.j12,JFz_Scan57.b00_length,JFz_Scan57.b01_length,JFz_Scan57.b02_length,JFz_Scan57.b03_length,JFz_Scan57.b04_length,JFz_Scan57.b05_length,JFz_Scan57.b06_length,JFz_Scan57.b07_length,JFz_Scan57.b08_length,JFz_Scan57.b09_length,JFz_Scan57.b10_length,JFz_Scan57.b11_length,JFz_Scan57.b12_length,JFz_Scan57.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell21
theorem encoded21 : CandidateParserByteOrder.arrayBytes16 cell21=encodeQM31LE limbs21 := by
  funext i
  fin_cases i <;> rfl
theorem parser21 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell21)=
    ok (some ⟨⟨831817114#u32,485136511#u32⟩,⟨294810303#u32,1769364146#u32⟩⟩) :=
  JFr_EncodedCell.parser cell21 limbs21 encoded21
#print axioms encoded21
#print axioms parser21
def cell22 : Array U8 16#usize := ⟨[87#u8,145#u8,254#u8,114#u8,62#u8,190#u8,116#u8,41#u8,219#u8,145#u8,39#u8,32#u8,124#u8,197#u8,4#u8,48#u8],by rfl⟩
def limbs22 : QM31Limbs := ![⟨1929285975,by change 1929285975<2147483647;omega⟩,⟨695516734,by change 695516734<2147483647;omega⟩,⟨539464155,by change 539464155<2147483647;omega⟩,⟨805619068,by change 805619068<2147483647;omega⟩]
theorem rawCell22 : (raw.drop 352).take 16=cell22.val := by
  simp only [raw,JFz_Scan57.data,JFz_Scan57.j00,JFz_Scan57.j01,JFz_Scan57.j02,JFz_Scan57.j03,JFz_Scan57.j04,JFz_Scan57.j05,JFz_Scan57.j06,JFz_Scan57.j07,JFz_Scan57.j08,JFz_Scan57.j09,JFz_Scan57.j10,JFz_Scan57.j11,JFz_Scan57.j12,JFz_Scan57.b00_length,JFz_Scan57.b01_length,JFz_Scan57.b02_length,JFz_Scan57.b03_length,JFz_Scan57.b04_length,JFz_Scan57.b05_length,JFz_Scan57.b06_length,JFz_Scan57.b07_length,JFz_Scan57.b08_length,JFz_Scan57.b09_length,JFz_Scan57.b10_length,JFz_Scan57.b11_length,JFz_Scan57.b12_length,JFz_Scan57.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell22
theorem encoded22 : CandidateParserByteOrder.arrayBytes16 cell22=encodeQM31LE limbs22 := by
  funext i
  fin_cases i <;> rfl
theorem parser22 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell22)=
    ok (some ⟨⟨1929285975#u32,695516734#u32⟩,⟨539464155#u32,805619068#u32⟩⟩) :=
  JFr_EncodedCell.parser cell22 limbs22 encoded22
#print axioms encoded22
#print axioms parser22
def cell23 : Array U8 16#usize := ⟨[66#u8,148#u8,72#u8,17#u8,88#u8,105#u8,70#u8,108#u8,110#u8,52#u8,150#u8,12#u8,163#u8,160#u8,180#u8,123#u8],by rfl⟩
def limbs23 : QM31Limbs := ![⟨289969218,by change 289969218<2147483647;omega⟩,⟨1816553816,by change 1816553816<2147483647;omega⟩,⟨211170414,by change 211170414<2147483647;omega⟩,⟨2075435171,by change 2075435171<2147483647;omega⟩]
theorem rawCell23 : (raw.drop 368).take 16=cell23.val := by
  simp only [raw,JFz_Scan57.data,JFz_Scan57.j00,JFz_Scan57.j01,JFz_Scan57.j02,JFz_Scan57.j03,JFz_Scan57.j04,JFz_Scan57.j05,JFz_Scan57.j06,JFz_Scan57.j07,JFz_Scan57.j08,JFz_Scan57.j09,JFz_Scan57.j10,JFz_Scan57.j11,JFz_Scan57.j12,JFz_Scan57.b00_length,JFz_Scan57.b01_length,JFz_Scan57.b02_length,JFz_Scan57.b03_length,JFz_Scan57.b04_length,JFz_Scan57.b05_length,JFz_Scan57.b06_length,JFz_Scan57.b07_length,JFz_Scan57.b08_length,JFz_Scan57.b09_length,JFz_Scan57.b10_length,JFz_Scan57.b11_length,JFz_Scan57.b12_length,JFz_Scan57.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell23
theorem encoded23 : CandidateParserByteOrder.arrayBytes16 cell23=encodeQM31LE limbs23 := by
  funext i
  fin_cases i <;> rfl
theorem parser23 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell23)=
    ok (some ⟨⟨289969218#u32,1816553816#u32⟩,⟨211170414#u32,2075435171#u32⟩⟩) :=
  JFr_EncodedCell.parser cell23 limbs23 encoded23
#print axioms encoded23
#print axioms parser23
def cell24 : Array U8 16#usize := ⟨[131#u8,78#u8,254#u8,66#u8,159#u8,28#u8,142#u8,36#u8,86#u8,33#u8,167#u8,42#u8,232#u8,16#u8,136#u8,29#u8],by rfl⟩
def limbs24 : QM31Limbs := ![⟨1123962499,by change 1123962499<2147483647;omega⟩,⟨613293215,by change 613293215<2147483647;omega⟩,⟨715596118,by change 715596118<2147483647;omega⟩,⟨495456488,by change 495456488<2147483647;omega⟩]
theorem rawCell24 : (raw.drop 384).take 16=cell24.val := by
  simp only [raw,JFz_Scan57.data,JFz_Scan57.j00,JFz_Scan57.j01,JFz_Scan57.j02,JFz_Scan57.j03,JFz_Scan57.j04,JFz_Scan57.j05,JFz_Scan57.j06,JFz_Scan57.j07,JFz_Scan57.j08,JFz_Scan57.j09,JFz_Scan57.j10,JFz_Scan57.j11,JFz_Scan57.j12,JFz_Scan57.b00_length,JFz_Scan57.b01_length,JFz_Scan57.b02_length,JFz_Scan57.b03_length,JFz_Scan57.b04_length,JFz_Scan57.b05_length,JFz_Scan57.b06_length,JFz_Scan57.b07_length,JFz_Scan57.b08_length,JFz_Scan57.b09_length,JFz_Scan57.b10_length,JFz_Scan57.b11_length,JFz_Scan57.b12_length,JFz_Scan57.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell24
theorem encoded24 : CandidateParserByteOrder.arrayBytes16 cell24=encodeQM31LE limbs24 := by
  funext i
  fin_cases i <;> rfl
theorem parser24 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell24)=
    ok (some ⟨⟨1123962499#u32,613293215#u32⟩,⟨715596118#u32,495456488#u32⟩⟩) :=
  JFr_EncodedCell.parser cell24 limbs24 encoded24
#print axioms encoded24
#print axioms parser24
def cell25 : Array U8 16#usize := ⟨[8#u8,11#u8,65#u8,113#u8,136#u8,184#u8,126#u8,44#u8,221#u8,79#u8,16#u8,50#u8,6#u8,133#u8,142#u8,123#u8],by rfl⟩
def limbs25 : QM31Limbs := ![⟨1900088072,by change 1900088072<2147483647;omega⟩,⟨746502280,by change 746502280<2147483647;omega⟩,⟨839929821,by change 839929821<2147483647;omega⟩,⟨2072937734,by change 2072937734<2147483647;omega⟩]
theorem rawCell25 : (raw.drop 400).take 16=cell25.val := by
  simp only [raw,JFz_Scan57.data,JFz_Scan57.j00,JFz_Scan57.j01,JFz_Scan57.j02,JFz_Scan57.j03,JFz_Scan57.j04,JFz_Scan57.j05,JFz_Scan57.j06,JFz_Scan57.j07,JFz_Scan57.j08,JFz_Scan57.j09,JFz_Scan57.j10,JFz_Scan57.j11,JFz_Scan57.j12,JFz_Scan57.b00_length,JFz_Scan57.b01_length,JFz_Scan57.b02_length,JFz_Scan57.b03_length,JFz_Scan57.b04_length,JFz_Scan57.b05_length,JFz_Scan57.b06_length,JFz_Scan57.b07_length,JFz_Scan57.b08_length,JFz_Scan57.b09_length,JFz_Scan57.b10_length,JFz_Scan57.b11_length,JFz_Scan57.b12_length,JFz_Scan57.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell25
theorem encoded25 : CandidateParserByteOrder.arrayBytes16 cell25=encodeQM31LE limbs25 := by
  funext i
  fin_cases i <;> rfl
theorem parser25 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell25)=
    ok (some ⟨⟨1900088072#u32,746502280#u32⟩,⟨839929821#u32,2072937734#u32⟩⟩) :=
  JFr_EncodedCell.parser cell25 limbs25 encoded25
#print axioms encoded25
#print axioms parser25
def cell26 : Array U8 16#usize := ⟨[205#u8,77#u8,200#u8,9#u8,113#u8,192#u8,63#u8,66#u8,219#u8,9#u8,193#u8,126#u8,192#u8,89#u8,114#u8,82#u8],by rfl⟩
def limbs26 : QM31Limbs := ![⟨164122061,by change 164122061<2147483647;omega⟩,⟨1111474289,by change 1111474289<2147483647;omega⟩,⟨2126580187,by change 2126580187<2147483647;omega⟩,⟨1383225792,by change 1383225792<2147483647;omega⟩]
theorem rawCell26 : (raw.drop 416).take 16=cell26.val := by
  simp only [raw,JFz_Scan57.data,JFz_Scan57.j00,JFz_Scan57.j01,JFz_Scan57.j02,JFz_Scan57.j03,JFz_Scan57.j04,JFz_Scan57.j05,JFz_Scan57.j06,JFz_Scan57.j07,JFz_Scan57.j08,JFz_Scan57.j09,JFz_Scan57.j10,JFz_Scan57.j11,JFz_Scan57.j12,JFz_Scan57.b00_length,JFz_Scan57.b01_length,JFz_Scan57.b02_length,JFz_Scan57.b03_length,JFz_Scan57.b04_length,JFz_Scan57.b05_length,JFz_Scan57.b06_length,JFz_Scan57.b07_length,JFz_Scan57.b08_length,JFz_Scan57.b09_length,JFz_Scan57.b10_length,JFz_Scan57.b11_length,JFz_Scan57.b12_length,JFz_Scan57.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell26
theorem encoded26 : CandidateParserByteOrder.arrayBytes16 cell26=encodeQM31LE limbs26 := by
  funext i
  fin_cases i <;> rfl
theorem parser26 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell26)=
    ok (some ⟨⟨164122061#u32,1111474289#u32⟩,⟨2126580187#u32,1383225792#u32⟩⟩) :=
  JFr_EncodedCell.parser cell26 limbs26 encoded26
#print axioms encoded26
#print axioms parser26
def cell27 : Array U8 16#usize := ⟨[182#u8,199#u8,173#u8,87#u8,92#u8,228#u8,71#u8,112#u8,212#u8,101#u8,7#u8,102#u8,82#u8,77#u8,26#u8,64#u8],by rfl⟩
def limbs27 : QM31Limbs := ![⟨1471006646,by change 1471006646<2147483647;omega⟩,⟨1883759708,by change 1883759708<2147483647;omega⟩,⟨1711760852,by change 1711760852<2147483647;omega⟩,⟨1075465554,by change 1075465554<2147483647;omega⟩]
theorem rawCell27 : (raw.drop 432).take 16=cell27.val := by
  simp only [raw,JFz_Scan57.data,JFz_Scan57.j00,JFz_Scan57.j01,JFz_Scan57.j02,JFz_Scan57.j03,JFz_Scan57.j04,JFz_Scan57.j05,JFz_Scan57.j06,JFz_Scan57.j07,JFz_Scan57.j08,JFz_Scan57.j09,JFz_Scan57.j10,JFz_Scan57.j11,JFz_Scan57.j12,JFz_Scan57.b00_length,JFz_Scan57.b01_length,JFz_Scan57.b02_length,JFz_Scan57.b03_length,JFz_Scan57.b04_length,JFz_Scan57.b05_length,JFz_Scan57.b06_length,JFz_Scan57.b07_length,JFz_Scan57.b08_length,JFz_Scan57.b09_length,JFz_Scan57.b10_length,JFz_Scan57.b11_length,JFz_Scan57.b12_length,JFz_Scan57.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell27
theorem encoded27 : CandidateParserByteOrder.arrayBytes16 cell27=encodeQM31LE limbs27 := by
  funext i
  fin_cases i <;> rfl
theorem parser27 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell27)=
    ok (some ⟨⟨1471006646#u32,1883759708#u32⟩,⟨1711760852#u32,1075465554#u32⟩⟩) :=
  JFr_EncodedCell.parser cell27 limbs27 encoded27
#print axioms encoded27
#print axioms parser27
end AspisR1.JFr_Bytes09
