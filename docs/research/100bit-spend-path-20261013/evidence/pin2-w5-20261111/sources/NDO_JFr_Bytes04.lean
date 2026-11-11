import NDO_JFr_Data04
import NDO_JFr_EncodedCell
import NDO_JFz_Scan52
set_option autoImplicit false
namespace AspisR1.JFr_Bytes04
open Aeneas Aeneas.Std Result RetainedFieldByteCodec
open AspisR1PublicPreparation
open AspisS1ExtractedRoundChildren
def raw : List U8 := JFz_Scan52.data
theorem rawLength : raw.length=448 := JFz_Scan52.length
#print axioms rawLength
theorem selected : (JFx_NativeBytes.proof.val.drop 1988).take 448=raw := JFz_Scan52.selected
#print axioms selected
def cell00 : Array U8 16#usize := ⟨[167#u8,226#u8,97#u8,8#u8,156#u8,119#u8,189#u8,29#u8,189#u8,40#u8,190#u8,50#u8,12#u8,240#u8,137#u8,92#u8],by rfl⟩
def limbs00 : QM31Limbs := ![⟨140632743,by change 140632743<2147483647;omega⟩,⟨498956188,by change 498956188<2147483647;omega⟩,⟨851323069,by change 851323069<2147483647;omega⟩,⟨1552543756,by change 1552543756<2147483647;omega⟩]
theorem rawCell00 : (raw.drop 0).take 16=cell00.val := by
  simp only [raw,JFz_Scan52.data,JFz_Scan52.j00,JFz_Scan52.j01,JFz_Scan52.j02,JFz_Scan52.j03,JFz_Scan52.j04,JFz_Scan52.j05,JFz_Scan52.j06,JFz_Scan52.j07,JFz_Scan52.j08,JFz_Scan52.j09,JFz_Scan52.j10,JFz_Scan52.j11,JFz_Scan52.j12,JFz_Scan52.b00_length,JFz_Scan52.b01_length,JFz_Scan52.b02_length,JFz_Scan52.b03_length,JFz_Scan52.b04_length,JFz_Scan52.b05_length,JFz_Scan52.b06_length,JFz_Scan52.b07_length,JFz_Scan52.b08_length,JFz_Scan52.b09_length,JFz_Scan52.b10_length,JFz_Scan52.b11_length,JFz_Scan52.b12_length,JFz_Scan52.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell00
theorem encoded00 : CandidateParserByteOrder.arrayBytes16 cell00=encodeQM31LE limbs00 := by
  funext i
  fin_cases i <;> rfl
theorem parser00 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell00)=
    ok (some ⟨⟨140632743#u32,498956188#u32⟩,⟨851323069#u32,1552543756#u32⟩⟩) :=
  JFr_EncodedCell.parser cell00 limbs00 encoded00
#print axioms encoded00
#print axioms parser00
def cell01 : Array U8 16#usize := ⟨[131#u8,245#u8,108#u8,21#u8,171#u8,242#u8,255#u8,122#u8,56#u8,0#u8,27#u8,57#u8,231#u8,108#u8,73#u8,41#u8],by rfl⟩
def limbs01 : QM31Limbs := ![⟨359462275,by change 359462275<2147483647;omega⟩,⟨2063594155,by change 2063594155<2147483647;omega⟩,⟨958070840,by change 958070840<2147483647;omega⟩,⟨692677863,by change 692677863<2147483647;omega⟩]
theorem rawCell01 : (raw.drop 16).take 16=cell01.val := by
  simp only [raw,JFz_Scan52.data,JFz_Scan52.j00,JFz_Scan52.j01,JFz_Scan52.j02,JFz_Scan52.j03,JFz_Scan52.j04,JFz_Scan52.j05,JFz_Scan52.j06,JFz_Scan52.j07,JFz_Scan52.j08,JFz_Scan52.j09,JFz_Scan52.j10,JFz_Scan52.j11,JFz_Scan52.j12,JFz_Scan52.b00_length,JFz_Scan52.b01_length,JFz_Scan52.b02_length,JFz_Scan52.b03_length,JFz_Scan52.b04_length,JFz_Scan52.b05_length,JFz_Scan52.b06_length,JFz_Scan52.b07_length,JFz_Scan52.b08_length,JFz_Scan52.b09_length,JFz_Scan52.b10_length,JFz_Scan52.b11_length,JFz_Scan52.b12_length,JFz_Scan52.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell01
theorem encoded01 : CandidateParserByteOrder.arrayBytes16 cell01=encodeQM31LE limbs01 := by
  funext i
  fin_cases i <;> rfl
theorem parser01 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell01)=
    ok (some ⟨⟨359462275#u32,2063594155#u32⟩,⟨958070840#u32,692677863#u32⟩⟩) :=
  JFr_EncodedCell.parser cell01 limbs01 encoded01
#print axioms encoded01
#print axioms parser01
def cell02 : Array U8 16#usize := ⟨[99#u8,139#u8,244#u8,95#u8,237#u8,228#u8,165#u8,2#u8,1#u8,46#u8,20#u8,1#u8,104#u8,34#u8,234#u8,22#u8],by rfl⟩
def limbs02 : QM31Limbs := ![⟨1609861987,by change 1609861987<2147483647;omega⟩,⟨44426477,by change 44426477<2147483647;omega⟩,⟨18099713,by change 18099713<2147483647;omega⟩,⟨384442984,by change 384442984<2147483647;omega⟩]
theorem rawCell02 : (raw.drop 32).take 16=cell02.val := by
  simp only [raw,JFz_Scan52.data,JFz_Scan52.j00,JFz_Scan52.j01,JFz_Scan52.j02,JFz_Scan52.j03,JFz_Scan52.j04,JFz_Scan52.j05,JFz_Scan52.j06,JFz_Scan52.j07,JFz_Scan52.j08,JFz_Scan52.j09,JFz_Scan52.j10,JFz_Scan52.j11,JFz_Scan52.j12,JFz_Scan52.b00_length,JFz_Scan52.b01_length,JFz_Scan52.b02_length,JFz_Scan52.b03_length,JFz_Scan52.b04_length,JFz_Scan52.b05_length,JFz_Scan52.b06_length,JFz_Scan52.b07_length,JFz_Scan52.b08_length,JFz_Scan52.b09_length,JFz_Scan52.b10_length,JFz_Scan52.b11_length,JFz_Scan52.b12_length,JFz_Scan52.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell02
theorem encoded02 : CandidateParserByteOrder.arrayBytes16 cell02=encodeQM31LE limbs02 := by
  funext i
  fin_cases i <;> rfl
theorem parser02 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell02)=
    ok (some ⟨⟨1609861987#u32,44426477#u32⟩,⟨18099713#u32,384442984#u32⟩⟩) :=
  JFr_EncodedCell.parser cell02 limbs02 encoded02
#print axioms encoded02
#print axioms parser02
def cell03 : Array U8 16#usize := ⟨[141#u8,26#u8,60#u8,12#u8,120#u8,152#u8,68#u8,105#u8,173#u8,214#u8,21#u8,72#u8,167#u8,183#u8,133#u8,114#u8],by rfl⟩
def limbs03 : QM31Limbs := ![⟨205265549,by change 205265549<2147483647;omega⟩,⟨1766103160,by change 1766103160<2147483647;omega⟩,⟨1209390765,by change 1209390765<2147483647;omega⟩,⟨1921365927,by change 1921365927<2147483647;omega⟩]
theorem rawCell03 : (raw.drop 48).take 16=cell03.val := by
  simp only [raw,JFz_Scan52.data,JFz_Scan52.j00,JFz_Scan52.j01,JFz_Scan52.j02,JFz_Scan52.j03,JFz_Scan52.j04,JFz_Scan52.j05,JFz_Scan52.j06,JFz_Scan52.j07,JFz_Scan52.j08,JFz_Scan52.j09,JFz_Scan52.j10,JFz_Scan52.j11,JFz_Scan52.j12,JFz_Scan52.b00_length,JFz_Scan52.b01_length,JFz_Scan52.b02_length,JFz_Scan52.b03_length,JFz_Scan52.b04_length,JFz_Scan52.b05_length,JFz_Scan52.b06_length,JFz_Scan52.b07_length,JFz_Scan52.b08_length,JFz_Scan52.b09_length,JFz_Scan52.b10_length,JFz_Scan52.b11_length,JFz_Scan52.b12_length,JFz_Scan52.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell03
theorem encoded03 : CandidateParserByteOrder.arrayBytes16 cell03=encodeQM31LE limbs03 := by
  funext i
  fin_cases i <;> rfl
theorem parser03 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell03)=
    ok (some ⟨⟨205265549#u32,1766103160#u32⟩,⟨1209390765#u32,1921365927#u32⟩⟩) :=
  JFr_EncodedCell.parser cell03 limbs03 encoded03
#print axioms encoded03
#print axioms parser03
def cell04 : Array U8 16#usize := ⟨[181#u8,83#u8,160#u8,74#u8,48#u8,188#u8,8#u8,59#u8,72#u8,6#u8,48#u8,115#u8,16#u8,76#u8,130#u8,29#u8],by rfl⟩
def limbs04 : QM31Limbs := ![⟨1252021173,by change 1252021173<2147483647;omega⟩,⟨990428208,by change 990428208<2147483647;omega⟩,⟨1932527176,by change 1932527176<2147483647;omega⟩,⟨495078416,by change 495078416<2147483647;omega⟩]
theorem rawCell04 : (raw.drop 64).take 16=cell04.val := by
  simp only [raw,JFz_Scan52.data,JFz_Scan52.j00,JFz_Scan52.j01,JFz_Scan52.j02,JFz_Scan52.j03,JFz_Scan52.j04,JFz_Scan52.j05,JFz_Scan52.j06,JFz_Scan52.j07,JFz_Scan52.j08,JFz_Scan52.j09,JFz_Scan52.j10,JFz_Scan52.j11,JFz_Scan52.j12,JFz_Scan52.b00_length,JFz_Scan52.b01_length,JFz_Scan52.b02_length,JFz_Scan52.b03_length,JFz_Scan52.b04_length,JFz_Scan52.b05_length,JFz_Scan52.b06_length,JFz_Scan52.b07_length,JFz_Scan52.b08_length,JFz_Scan52.b09_length,JFz_Scan52.b10_length,JFz_Scan52.b11_length,JFz_Scan52.b12_length,JFz_Scan52.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell04
theorem encoded04 : CandidateParserByteOrder.arrayBytes16 cell04=encodeQM31LE limbs04 := by
  funext i
  fin_cases i <;> rfl
theorem parser04 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell04)=
    ok (some ⟨⟨1252021173#u32,990428208#u32⟩,⟨1932527176#u32,495078416#u32⟩⟩) :=
  JFr_EncodedCell.parser cell04 limbs04 encoded04
#print axioms encoded04
#print axioms parser04
def cell05 : Array U8 16#usize := ⟨[57#u8,80#u8,60#u8,56#u8,254#u8,204#u8,153#u8,8#u8,141#u8,2#u8,20#u8,34#u8,240#u8,253#u8,157#u8,96#u8],by rfl⟩
def limbs05 : QM31Limbs := ![⟨943476793,by change 943476793<2147483647;omega⟩,⟨144297214,by change 144297214<2147483647;omega⟩,⟨571736717,by change 571736717<2147483647;omega⟩,⟨1620966896,by change 1620966896<2147483647;omega⟩]
theorem rawCell05 : (raw.drop 80).take 16=cell05.val := by
  simp only [raw,JFz_Scan52.data,JFz_Scan52.j00,JFz_Scan52.j01,JFz_Scan52.j02,JFz_Scan52.j03,JFz_Scan52.j04,JFz_Scan52.j05,JFz_Scan52.j06,JFz_Scan52.j07,JFz_Scan52.j08,JFz_Scan52.j09,JFz_Scan52.j10,JFz_Scan52.j11,JFz_Scan52.j12,JFz_Scan52.b00_length,JFz_Scan52.b01_length,JFz_Scan52.b02_length,JFz_Scan52.b03_length,JFz_Scan52.b04_length,JFz_Scan52.b05_length,JFz_Scan52.b06_length,JFz_Scan52.b07_length,JFz_Scan52.b08_length,JFz_Scan52.b09_length,JFz_Scan52.b10_length,JFz_Scan52.b11_length,JFz_Scan52.b12_length,JFz_Scan52.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell05
theorem encoded05 : CandidateParserByteOrder.arrayBytes16 cell05=encodeQM31LE limbs05 := by
  funext i
  fin_cases i <;> rfl
theorem parser05 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell05)=
    ok (some ⟨⟨943476793#u32,144297214#u32⟩,⟨571736717#u32,1620966896#u32⟩⟩) :=
  JFr_EncodedCell.parser cell05 limbs05 encoded05
#print axioms encoded05
#print axioms parser05
def cell06 : Array U8 16#usize := ⟨[205#u8,5#u8,67#u8,82#u8,9#u8,107#u8,213#u8,21#u8,231#u8,139#u8,11#u8,107#u8,191#u8,49#u8,5#u8,99#u8],by rfl⟩
def limbs06 : QM31Limbs := ![⟨1380124109,by change 1380124109<2147483647;omega⟩,⟨366308105,by change 366308105<2147483647;omega⟩,⟨1795918823,by change 1795918823<2147483647;omega⟩,⟨1661284799,by change 1661284799<2147483647;omega⟩]
theorem rawCell06 : (raw.drop 96).take 16=cell06.val := by
  simp only [raw,JFz_Scan52.data,JFz_Scan52.j00,JFz_Scan52.j01,JFz_Scan52.j02,JFz_Scan52.j03,JFz_Scan52.j04,JFz_Scan52.j05,JFz_Scan52.j06,JFz_Scan52.j07,JFz_Scan52.j08,JFz_Scan52.j09,JFz_Scan52.j10,JFz_Scan52.j11,JFz_Scan52.j12,JFz_Scan52.b00_length,JFz_Scan52.b01_length,JFz_Scan52.b02_length,JFz_Scan52.b03_length,JFz_Scan52.b04_length,JFz_Scan52.b05_length,JFz_Scan52.b06_length,JFz_Scan52.b07_length,JFz_Scan52.b08_length,JFz_Scan52.b09_length,JFz_Scan52.b10_length,JFz_Scan52.b11_length,JFz_Scan52.b12_length,JFz_Scan52.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell06
theorem encoded06 : CandidateParserByteOrder.arrayBytes16 cell06=encodeQM31LE limbs06 := by
  funext i
  fin_cases i <;> rfl
theorem parser06 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell06)=
    ok (some ⟨⟨1380124109#u32,366308105#u32⟩,⟨1795918823#u32,1661284799#u32⟩⟩) :=
  JFr_EncodedCell.parser cell06 limbs06 encoded06
#print axioms encoded06
#print axioms parser06
def cell07 : Array U8 16#usize := ⟨[101#u8,26#u8,161#u8,8#u8,211#u8,174#u8,109#u8,17#u8,128#u8,32#u8,140#u8,103#u8,161#u8,11#u8,169#u8,49#u8],by rfl⟩
def limbs07 : QM31Limbs := ![⟨144775781,by change 144775781<2147483647;omega⟩,⟨292400851,by change 292400851<2147483647;omega⟩,⟨1737236608,by change 1737236608<2147483647;omega⟩,⟨833162145,by change 833162145<2147483647;omega⟩]
theorem rawCell07 : (raw.drop 112).take 16=cell07.val := by
  simp only [raw,JFz_Scan52.data,JFz_Scan52.j00,JFz_Scan52.j01,JFz_Scan52.j02,JFz_Scan52.j03,JFz_Scan52.j04,JFz_Scan52.j05,JFz_Scan52.j06,JFz_Scan52.j07,JFz_Scan52.j08,JFz_Scan52.j09,JFz_Scan52.j10,JFz_Scan52.j11,JFz_Scan52.j12,JFz_Scan52.b00_length,JFz_Scan52.b01_length,JFz_Scan52.b02_length,JFz_Scan52.b03_length,JFz_Scan52.b04_length,JFz_Scan52.b05_length,JFz_Scan52.b06_length,JFz_Scan52.b07_length,JFz_Scan52.b08_length,JFz_Scan52.b09_length,JFz_Scan52.b10_length,JFz_Scan52.b11_length,JFz_Scan52.b12_length,JFz_Scan52.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell07
theorem encoded07 : CandidateParserByteOrder.arrayBytes16 cell07=encodeQM31LE limbs07 := by
  funext i
  fin_cases i <;> rfl
theorem parser07 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell07)=
    ok (some ⟨⟨144775781#u32,292400851#u32⟩,⟨1737236608#u32,833162145#u32⟩⟩) :=
  JFr_EncodedCell.parser cell07 limbs07 encoded07
#print axioms encoded07
#print axioms parser07
def cell08 : Array U8 16#usize := ⟨[96#u8,121#u8,73#u8,53#u8,114#u8,174#u8,180#u8,100#u8,41#u8,210#u8,11#u8,61#u8,84#u8,180#u8,250#u8,0#u8],by rfl⟩
def limbs08 : QM31Limbs := ![⟨894007648,by change 894007648<2147483647;omega⟩,⟨1689562738,by change 1689562738<2147483647;omega⟩,⟨1024184873,by change 1024184873<2147483647;omega⟩,⟨16430164,by change 16430164<2147483647;omega⟩]
theorem rawCell08 : (raw.drop 128).take 16=cell08.val := by
  simp only [raw,JFz_Scan52.data,JFz_Scan52.j00,JFz_Scan52.j01,JFz_Scan52.j02,JFz_Scan52.j03,JFz_Scan52.j04,JFz_Scan52.j05,JFz_Scan52.j06,JFz_Scan52.j07,JFz_Scan52.j08,JFz_Scan52.j09,JFz_Scan52.j10,JFz_Scan52.j11,JFz_Scan52.j12,JFz_Scan52.b00_length,JFz_Scan52.b01_length,JFz_Scan52.b02_length,JFz_Scan52.b03_length,JFz_Scan52.b04_length,JFz_Scan52.b05_length,JFz_Scan52.b06_length,JFz_Scan52.b07_length,JFz_Scan52.b08_length,JFz_Scan52.b09_length,JFz_Scan52.b10_length,JFz_Scan52.b11_length,JFz_Scan52.b12_length,JFz_Scan52.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell08
theorem encoded08 : CandidateParserByteOrder.arrayBytes16 cell08=encodeQM31LE limbs08 := by
  funext i
  fin_cases i <;> rfl
theorem parser08 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell08)=
    ok (some ⟨⟨894007648#u32,1689562738#u32⟩,⟨1024184873#u32,16430164#u32⟩⟩) :=
  JFr_EncodedCell.parser cell08 limbs08 encoded08
#print axioms encoded08
#print axioms parser08
def cell09 : Array U8 16#usize := ⟨[187#u8,230#u8,55#u8,72#u8,34#u8,237#u8,140#u8,27#u8,97#u8,99#u8,49#u8,33#u8,223#u8,137#u8,226#u8,86#u8],by rfl⟩
def limbs09 : QM31Limbs := ![⟨1211623099,by change 1211623099<2147483647;omega⟩,⟨462220578,by change 462220578<2147483647;omega⟩,⟨556884833,by change 556884833<2147483647;omega⟩,⟨1457687007,by change 1457687007<2147483647;omega⟩]
theorem rawCell09 : (raw.drop 144).take 16=cell09.val := by
  simp only [raw,JFz_Scan52.data,JFz_Scan52.j00,JFz_Scan52.j01,JFz_Scan52.j02,JFz_Scan52.j03,JFz_Scan52.j04,JFz_Scan52.j05,JFz_Scan52.j06,JFz_Scan52.j07,JFz_Scan52.j08,JFz_Scan52.j09,JFz_Scan52.j10,JFz_Scan52.j11,JFz_Scan52.j12,JFz_Scan52.b00_length,JFz_Scan52.b01_length,JFz_Scan52.b02_length,JFz_Scan52.b03_length,JFz_Scan52.b04_length,JFz_Scan52.b05_length,JFz_Scan52.b06_length,JFz_Scan52.b07_length,JFz_Scan52.b08_length,JFz_Scan52.b09_length,JFz_Scan52.b10_length,JFz_Scan52.b11_length,JFz_Scan52.b12_length,JFz_Scan52.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell09
theorem encoded09 : CandidateParserByteOrder.arrayBytes16 cell09=encodeQM31LE limbs09 := by
  funext i
  fin_cases i <;> rfl
theorem parser09 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell09)=
    ok (some ⟨⟨1211623099#u32,462220578#u32⟩,⟨556884833#u32,1457687007#u32⟩⟩) :=
  JFr_EncodedCell.parser cell09 limbs09 encoded09
#print axioms encoded09
#print axioms parser09
def cell10 : Array U8 16#usize := ⟨[185#u8,128#u8,216#u8,56#u8,180#u8,89#u8,8#u8,109#u8,125#u8,89#u8,109#u8,34#u8,210#u8,182#u8,180#u8,92#u8],by rfl⟩
def limbs10 : QM31Limbs := ![⟨953712825,by change 953712825<2147483647;omega⟩,⟨1829263796,by change 1829263796<2147483647;omega⟩,⟨577591677,by change 577591677<2147483647;omega⟩,⟨1555347154,by change 1555347154<2147483647;omega⟩]
theorem rawCell10 : (raw.drop 160).take 16=cell10.val := by
  simp only [raw,JFz_Scan52.data,JFz_Scan52.j00,JFz_Scan52.j01,JFz_Scan52.j02,JFz_Scan52.j03,JFz_Scan52.j04,JFz_Scan52.j05,JFz_Scan52.j06,JFz_Scan52.j07,JFz_Scan52.j08,JFz_Scan52.j09,JFz_Scan52.j10,JFz_Scan52.j11,JFz_Scan52.j12,JFz_Scan52.b00_length,JFz_Scan52.b01_length,JFz_Scan52.b02_length,JFz_Scan52.b03_length,JFz_Scan52.b04_length,JFz_Scan52.b05_length,JFz_Scan52.b06_length,JFz_Scan52.b07_length,JFz_Scan52.b08_length,JFz_Scan52.b09_length,JFz_Scan52.b10_length,JFz_Scan52.b11_length,JFz_Scan52.b12_length,JFz_Scan52.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell10
theorem encoded10 : CandidateParserByteOrder.arrayBytes16 cell10=encodeQM31LE limbs10 := by
  funext i
  fin_cases i <;> rfl
theorem parser10 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell10)=
    ok (some ⟨⟨953712825#u32,1829263796#u32⟩,⟨577591677#u32,1555347154#u32⟩⟩) :=
  JFr_EncodedCell.parser cell10 limbs10 encoded10
#print axioms encoded10
#print axioms parser10
def cell11 : Array U8 16#usize := ⟨[120#u8,220#u8,144#u8,4#u8,100#u8,2#u8,63#u8,32#u8,199#u8,32#u8,162#u8,49#u8,75#u8,132#u8,121#u8,62#u8],by rfl⟩
def limbs11 : QM31Limbs := ![⟨76602488,by change 76602488<2147483647;omega⟩,⟨541000292,by change 541000292<2147483647;omega⟩,⟨832708807,by change 832708807<2147483647;omega⟩,⟨1048151115,by change 1048151115<2147483647;omega⟩]
theorem rawCell11 : (raw.drop 176).take 16=cell11.val := by
  simp only [raw,JFz_Scan52.data,JFz_Scan52.j00,JFz_Scan52.j01,JFz_Scan52.j02,JFz_Scan52.j03,JFz_Scan52.j04,JFz_Scan52.j05,JFz_Scan52.j06,JFz_Scan52.j07,JFz_Scan52.j08,JFz_Scan52.j09,JFz_Scan52.j10,JFz_Scan52.j11,JFz_Scan52.j12,JFz_Scan52.b00_length,JFz_Scan52.b01_length,JFz_Scan52.b02_length,JFz_Scan52.b03_length,JFz_Scan52.b04_length,JFz_Scan52.b05_length,JFz_Scan52.b06_length,JFz_Scan52.b07_length,JFz_Scan52.b08_length,JFz_Scan52.b09_length,JFz_Scan52.b10_length,JFz_Scan52.b11_length,JFz_Scan52.b12_length,JFz_Scan52.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell11
theorem encoded11 : CandidateParserByteOrder.arrayBytes16 cell11=encodeQM31LE limbs11 := by
  funext i
  fin_cases i <;> rfl
theorem parser11 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell11)=
    ok (some ⟨⟨76602488#u32,541000292#u32⟩,⟨832708807#u32,1048151115#u32⟩⟩) :=
  JFr_EncodedCell.parser cell11 limbs11 encoded11
#print axioms encoded11
#print axioms parser11
def cell12 : Array U8 16#usize := ⟨[125#u8,139#u8,71#u8,63#u8,96#u8,168#u8,127#u8,88#u8,106#u8,36#u8,163#u8,29#u8,55#u8,41#u8,98#u8,55#u8],by rfl⟩
def limbs12 : QM31Limbs := ![⟨1061653373,by change 1061653373<2147483647;omega⟩,⟨1484761184,by change 1484761184<2147483647;omega⟩,⟨497230954,by change 497230954<2147483647;omega⟩,⟨929179959,by change 929179959<2147483647;omega⟩]
theorem rawCell12 : (raw.drop 192).take 16=cell12.val := by
  simp only [raw,JFz_Scan52.data,JFz_Scan52.j00,JFz_Scan52.j01,JFz_Scan52.j02,JFz_Scan52.j03,JFz_Scan52.j04,JFz_Scan52.j05,JFz_Scan52.j06,JFz_Scan52.j07,JFz_Scan52.j08,JFz_Scan52.j09,JFz_Scan52.j10,JFz_Scan52.j11,JFz_Scan52.j12,JFz_Scan52.b00_length,JFz_Scan52.b01_length,JFz_Scan52.b02_length,JFz_Scan52.b03_length,JFz_Scan52.b04_length,JFz_Scan52.b05_length,JFz_Scan52.b06_length,JFz_Scan52.b07_length,JFz_Scan52.b08_length,JFz_Scan52.b09_length,JFz_Scan52.b10_length,JFz_Scan52.b11_length,JFz_Scan52.b12_length,JFz_Scan52.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell12
theorem encoded12 : CandidateParserByteOrder.arrayBytes16 cell12=encodeQM31LE limbs12 := by
  funext i
  fin_cases i <;> rfl
theorem parser12 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell12)=
    ok (some ⟨⟨1061653373#u32,1484761184#u32⟩,⟨497230954#u32,929179959#u32⟩⟩) :=
  JFr_EncodedCell.parser cell12 limbs12 encoded12
#print axioms encoded12
#print axioms parser12
def cell13 : Array U8 16#usize := ⟨[196#u8,74#u8,109#u8,127#u8,99#u8,42#u8,18#u8,43#u8,233#u8,71#u8,68#u8,25#u8,251#u8,34#u8,162#u8,107#u8],by rfl⟩
def limbs13 : QM31Limbs := ![⟨2137868996,by change 2137868996<2147483647;omega⟩,⟨722610787,by change 722610787<2147483647;omega⟩,⟨423905257,by change 423905257<2147483647;omega⟩,⟨1805787899,by change 1805787899<2147483647;omega⟩]
theorem rawCell13 : (raw.drop 208).take 16=cell13.val := by
  simp only [raw,JFz_Scan52.data,JFz_Scan52.j00,JFz_Scan52.j01,JFz_Scan52.j02,JFz_Scan52.j03,JFz_Scan52.j04,JFz_Scan52.j05,JFz_Scan52.j06,JFz_Scan52.j07,JFz_Scan52.j08,JFz_Scan52.j09,JFz_Scan52.j10,JFz_Scan52.j11,JFz_Scan52.j12,JFz_Scan52.b00_length,JFz_Scan52.b01_length,JFz_Scan52.b02_length,JFz_Scan52.b03_length,JFz_Scan52.b04_length,JFz_Scan52.b05_length,JFz_Scan52.b06_length,JFz_Scan52.b07_length,JFz_Scan52.b08_length,JFz_Scan52.b09_length,JFz_Scan52.b10_length,JFz_Scan52.b11_length,JFz_Scan52.b12_length,JFz_Scan52.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell13
theorem encoded13 : CandidateParserByteOrder.arrayBytes16 cell13=encodeQM31LE limbs13 := by
  funext i
  fin_cases i <;> rfl
theorem parser13 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell13)=
    ok (some ⟨⟨2137868996#u32,722610787#u32⟩,⟨423905257#u32,1805787899#u32⟩⟩) :=
  JFr_EncodedCell.parser cell13 limbs13 encoded13
#print axioms encoded13
#print axioms parser13
def cell14 : Array U8 16#usize := ⟨[53#u8,60#u8,59#u8,33#u8,71#u8,76#u8,29#u8,9#u8,13#u8,8#u8,157#u8,30#u8,143#u8,79#u8,102#u8,39#u8],by rfl⟩
def limbs14 : QM31Limbs := ![⟨557530165,by change 557530165<2147483647;omega⟩,⟨152915015,by change 152915015<2147483647;omega⟩,⟨513607693,by change 513607693<2147483647;omega⟩,⟨661016463,by change 661016463<2147483647;omega⟩]
theorem rawCell14 : (raw.drop 224).take 16=cell14.val := by
  simp only [raw,JFz_Scan52.data,JFz_Scan52.j00,JFz_Scan52.j01,JFz_Scan52.j02,JFz_Scan52.j03,JFz_Scan52.j04,JFz_Scan52.j05,JFz_Scan52.j06,JFz_Scan52.j07,JFz_Scan52.j08,JFz_Scan52.j09,JFz_Scan52.j10,JFz_Scan52.j11,JFz_Scan52.j12,JFz_Scan52.b00_length,JFz_Scan52.b01_length,JFz_Scan52.b02_length,JFz_Scan52.b03_length,JFz_Scan52.b04_length,JFz_Scan52.b05_length,JFz_Scan52.b06_length,JFz_Scan52.b07_length,JFz_Scan52.b08_length,JFz_Scan52.b09_length,JFz_Scan52.b10_length,JFz_Scan52.b11_length,JFz_Scan52.b12_length,JFz_Scan52.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell14
theorem encoded14 : CandidateParserByteOrder.arrayBytes16 cell14=encodeQM31LE limbs14 := by
  funext i
  fin_cases i <;> rfl
theorem parser14 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell14)=
    ok (some ⟨⟨557530165#u32,152915015#u32⟩,⟨513607693#u32,661016463#u32⟩⟩) :=
  JFr_EncodedCell.parser cell14 limbs14 encoded14
#print axioms encoded14
#print axioms parser14
def cell15 : Array U8 16#usize := ⟨[36#u8,80#u8,22#u8,26#u8,207#u8,151#u8,3#u8,45#u8,14#u8,250#u8,213#u8,81#u8,195#u8,90#u8,234#u8,25#u8],by rfl⟩
def limbs15 : QM31Limbs := ![⟨437669924,by change 437669924<2147483647;omega⟩,⟨755210191,by change 755210191<2147483647;omega⟩,⟨1372977678,by change 1372977678<2147483647;omega⟩,⟨434789059,by change 434789059<2147483647;omega⟩]
theorem rawCell15 : (raw.drop 240).take 16=cell15.val := by
  simp only [raw,JFz_Scan52.data,JFz_Scan52.j00,JFz_Scan52.j01,JFz_Scan52.j02,JFz_Scan52.j03,JFz_Scan52.j04,JFz_Scan52.j05,JFz_Scan52.j06,JFz_Scan52.j07,JFz_Scan52.j08,JFz_Scan52.j09,JFz_Scan52.j10,JFz_Scan52.j11,JFz_Scan52.j12,JFz_Scan52.b00_length,JFz_Scan52.b01_length,JFz_Scan52.b02_length,JFz_Scan52.b03_length,JFz_Scan52.b04_length,JFz_Scan52.b05_length,JFz_Scan52.b06_length,JFz_Scan52.b07_length,JFz_Scan52.b08_length,JFz_Scan52.b09_length,JFz_Scan52.b10_length,JFz_Scan52.b11_length,JFz_Scan52.b12_length,JFz_Scan52.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell15
theorem encoded15 : CandidateParserByteOrder.arrayBytes16 cell15=encodeQM31LE limbs15 := by
  funext i
  fin_cases i <;> rfl
theorem parser15 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell15)=
    ok (some ⟨⟨437669924#u32,755210191#u32⟩,⟨1372977678#u32,434789059#u32⟩⟩) :=
  JFr_EncodedCell.parser cell15 limbs15 encoded15
#print axioms encoded15
#print axioms parser15
def cell16 : Array U8 16#usize := ⟨[251#u8,147#u8,213#u8,56#u8,100#u8,161#u8,165#u8,66#u8,98#u8,117#u8,3#u8,87#u8,103#u8,201#u8,3#u8,70#u8],by rfl⟩
def limbs16 : QM31Limbs := ![⟨953521147,by change 953521147<2147483647;omega⟩,⟨1118151012,by change 1118151012<2147483647;omega⟩,⟨1459844450,by change 1459844450<2147483647;omega⟩,⟨1174653287,by change 1174653287<2147483647;omega⟩]
theorem rawCell16 : (raw.drop 256).take 16=cell16.val := by
  simp only [raw,JFz_Scan52.data,JFz_Scan52.j00,JFz_Scan52.j01,JFz_Scan52.j02,JFz_Scan52.j03,JFz_Scan52.j04,JFz_Scan52.j05,JFz_Scan52.j06,JFz_Scan52.j07,JFz_Scan52.j08,JFz_Scan52.j09,JFz_Scan52.j10,JFz_Scan52.j11,JFz_Scan52.j12,JFz_Scan52.b00_length,JFz_Scan52.b01_length,JFz_Scan52.b02_length,JFz_Scan52.b03_length,JFz_Scan52.b04_length,JFz_Scan52.b05_length,JFz_Scan52.b06_length,JFz_Scan52.b07_length,JFz_Scan52.b08_length,JFz_Scan52.b09_length,JFz_Scan52.b10_length,JFz_Scan52.b11_length,JFz_Scan52.b12_length,JFz_Scan52.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell16
theorem encoded16 : CandidateParserByteOrder.arrayBytes16 cell16=encodeQM31LE limbs16 := by
  funext i
  fin_cases i <;> rfl
theorem parser16 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell16)=
    ok (some ⟨⟨953521147#u32,1118151012#u32⟩,⟨1459844450#u32,1174653287#u32⟩⟩) :=
  JFr_EncodedCell.parser cell16 limbs16 encoded16
#print axioms encoded16
#print axioms parser16
def cell17 : Array U8 16#usize := ⟨[66#u8,12#u8,231#u8,84#u8,44#u8,49#u8,191#u8,20#u8,109#u8,104#u8,35#u8,92#u8,99#u8,67#u8,208#u8,64#u8],by rfl⟩
def limbs17 : QM31Limbs := ![⟨1424428098,by change 1424428098<2147483647;omega⟩,⟨348074284,by change 348074284<2147483647;omega⟩,⟨1545824365,by change 1545824365<2147483647;omega⟩,⟨1087390563,by change 1087390563<2147483647;omega⟩]
theorem rawCell17 : (raw.drop 272).take 16=cell17.val := by
  simp only [raw,JFz_Scan52.data,JFz_Scan52.j00,JFz_Scan52.j01,JFz_Scan52.j02,JFz_Scan52.j03,JFz_Scan52.j04,JFz_Scan52.j05,JFz_Scan52.j06,JFz_Scan52.j07,JFz_Scan52.j08,JFz_Scan52.j09,JFz_Scan52.j10,JFz_Scan52.j11,JFz_Scan52.j12,JFz_Scan52.b00_length,JFz_Scan52.b01_length,JFz_Scan52.b02_length,JFz_Scan52.b03_length,JFz_Scan52.b04_length,JFz_Scan52.b05_length,JFz_Scan52.b06_length,JFz_Scan52.b07_length,JFz_Scan52.b08_length,JFz_Scan52.b09_length,JFz_Scan52.b10_length,JFz_Scan52.b11_length,JFz_Scan52.b12_length,JFz_Scan52.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell17
theorem encoded17 : CandidateParserByteOrder.arrayBytes16 cell17=encodeQM31LE limbs17 := by
  funext i
  fin_cases i <;> rfl
theorem parser17 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell17)=
    ok (some ⟨⟨1424428098#u32,348074284#u32⟩,⟨1545824365#u32,1087390563#u32⟩⟩) :=
  JFr_EncodedCell.parser cell17 limbs17 encoded17
#print axioms encoded17
#print axioms parser17
def cell18 : Array U8 16#usize := ⟨[77#u8,50#u8,96#u8,94#u8,128#u8,212#u8,222#u8,18#u8,248#u8,198#u8,239#u8,107#u8,160#u8,171#u8,64#u8,108#u8],by rfl⟩
def limbs18 : QM31Limbs := ![⟨1583362637,by change 1583362637<2147483647;omega⟩,⟨316593280,by change 316593280<2147483647;omega⟩,⟨1810876152,by change 1810876152<2147483647;omega⟩,⟨1816177568,by change 1816177568<2147483647;omega⟩]
theorem rawCell18 : (raw.drop 288).take 16=cell18.val := by
  simp only [raw,JFz_Scan52.data,JFz_Scan52.j00,JFz_Scan52.j01,JFz_Scan52.j02,JFz_Scan52.j03,JFz_Scan52.j04,JFz_Scan52.j05,JFz_Scan52.j06,JFz_Scan52.j07,JFz_Scan52.j08,JFz_Scan52.j09,JFz_Scan52.j10,JFz_Scan52.j11,JFz_Scan52.j12,JFz_Scan52.b00_length,JFz_Scan52.b01_length,JFz_Scan52.b02_length,JFz_Scan52.b03_length,JFz_Scan52.b04_length,JFz_Scan52.b05_length,JFz_Scan52.b06_length,JFz_Scan52.b07_length,JFz_Scan52.b08_length,JFz_Scan52.b09_length,JFz_Scan52.b10_length,JFz_Scan52.b11_length,JFz_Scan52.b12_length,JFz_Scan52.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell18
theorem encoded18 : CandidateParserByteOrder.arrayBytes16 cell18=encodeQM31LE limbs18 := by
  funext i
  fin_cases i <;> rfl
theorem parser18 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell18)=
    ok (some ⟨⟨1583362637#u32,316593280#u32⟩,⟨1810876152#u32,1816177568#u32⟩⟩) :=
  JFr_EncodedCell.parser cell18 limbs18 encoded18
#print axioms encoded18
#print axioms parser18
def cell19 : Array U8 16#usize := ⟨[133#u8,252#u8,207#u8,103#u8,140#u8,179#u8,154#u8,40#u8,11#u8,112#u8,141#u8,82#u8,176#u8,103#u8,56#u8,67#u8],by rfl⟩
def limbs19 : QM31Limbs := ![⟨1741683845,by change 1741683845<2147483647;omega⟩,⟨681227148,by change 681227148<2147483647;omega⟩,⟨1385000971,by change 1385000971<2147483647;omega⟩,⟨1127770032,by change 1127770032<2147483647;omega⟩]
theorem rawCell19 : (raw.drop 304).take 16=cell19.val := by
  simp only [raw,JFz_Scan52.data,JFz_Scan52.j00,JFz_Scan52.j01,JFz_Scan52.j02,JFz_Scan52.j03,JFz_Scan52.j04,JFz_Scan52.j05,JFz_Scan52.j06,JFz_Scan52.j07,JFz_Scan52.j08,JFz_Scan52.j09,JFz_Scan52.j10,JFz_Scan52.j11,JFz_Scan52.j12,JFz_Scan52.b00_length,JFz_Scan52.b01_length,JFz_Scan52.b02_length,JFz_Scan52.b03_length,JFz_Scan52.b04_length,JFz_Scan52.b05_length,JFz_Scan52.b06_length,JFz_Scan52.b07_length,JFz_Scan52.b08_length,JFz_Scan52.b09_length,JFz_Scan52.b10_length,JFz_Scan52.b11_length,JFz_Scan52.b12_length,JFz_Scan52.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell19
theorem encoded19 : CandidateParserByteOrder.arrayBytes16 cell19=encodeQM31LE limbs19 := by
  funext i
  fin_cases i <;> rfl
theorem parser19 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell19)=
    ok (some ⟨⟨1741683845#u32,681227148#u32⟩,⟨1385000971#u32,1127770032#u32⟩⟩) :=
  JFr_EncodedCell.parser cell19 limbs19 encoded19
#print axioms encoded19
#print axioms parser19
def cell20 : Array U8 16#usize := ⟨[130#u8,57#u8,31#u8,11#u8,14#u8,132#u8,84#u8,20#u8,181#u8,153#u8,23#u8,99#u8,157#u8,0#u8,114#u8,39#u8],by rfl⟩
def limbs20 : QM31Limbs := ![⟨186595714,by change 186595714<2147483647;omega⟩,⟨341083150,by change 341083150<2147483647;omega⟩,⟨1662491061,by change 1662491061<2147483647;omega⟩,⟨661782685,by change 661782685<2147483647;omega⟩]
theorem rawCell20 : (raw.drop 320).take 16=cell20.val := by
  simp only [raw,JFz_Scan52.data,JFz_Scan52.j00,JFz_Scan52.j01,JFz_Scan52.j02,JFz_Scan52.j03,JFz_Scan52.j04,JFz_Scan52.j05,JFz_Scan52.j06,JFz_Scan52.j07,JFz_Scan52.j08,JFz_Scan52.j09,JFz_Scan52.j10,JFz_Scan52.j11,JFz_Scan52.j12,JFz_Scan52.b00_length,JFz_Scan52.b01_length,JFz_Scan52.b02_length,JFz_Scan52.b03_length,JFz_Scan52.b04_length,JFz_Scan52.b05_length,JFz_Scan52.b06_length,JFz_Scan52.b07_length,JFz_Scan52.b08_length,JFz_Scan52.b09_length,JFz_Scan52.b10_length,JFz_Scan52.b11_length,JFz_Scan52.b12_length,JFz_Scan52.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell20
theorem encoded20 : CandidateParserByteOrder.arrayBytes16 cell20=encodeQM31LE limbs20 := by
  funext i
  fin_cases i <;> rfl
theorem parser20 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell20)=
    ok (some ⟨⟨186595714#u32,341083150#u32⟩,⟨1662491061#u32,661782685#u32⟩⟩) :=
  JFr_EncodedCell.parser cell20 limbs20 encoded20
#print axioms encoded20
#print axioms parser20
def cell21 : Array U8 16#usize := ⟨[12#u8,65#u8,42#u8,119#u8,240#u8,119#u8,228#u8,1#u8,114#u8,51#u8,154#u8,21#u8,112#u8,154#u8,73#u8,46#u8],by rfl⟩
def limbs21 : QM31Limbs := ![⟨1999257868,by change 1999257868<2147483647;omega⟩,⟨31750128,by change 31750128<2147483647;omega⟩,⟨362427250,by change 362427250<2147483647;omega⟩,⟨776575600,by change 776575600<2147483647;omega⟩]
theorem rawCell21 : (raw.drop 336).take 16=cell21.val := by
  simp only [raw,JFz_Scan52.data,JFz_Scan52.j00,JFz_Scan52.j01,JFz_Scan52.j02,JFz_Scan52.j03,JFz_Scan52.j04,JFz_Scan52.j05,JFz_Scan52.j06,JFz_Scan52.j07,JFz_Scan52.j08,JFz_Scan52.j09,JFz_Scan52.j10,JFz_Scan52.j11,JFz_Scan52.j12,JFz_Scan52.b00_length,JFz_Scan52.b01_length,JFz_Scan52.b02_length,JFz_Scan52.b03_length,JFz_Scan52.b04_length,JFz_Scan52.b05_length,JFz_Scan52.b06_length,JFz_Scan52.b07_length,JFz_Scan52.b08_length,JFz_Scan52.b09_length,JFz_Scan52.b10_length,JFz_Scan52.b11_length,JFz_Scan52.b12_length,JFz_Scan52.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell21
theorem encoded21 : CandidateParserByteOrder.arrayBytes16 cell21=encodeQM31LE limbs21 := by
  funext i
  fin_cases i <;> rfl
theorem parser21 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell21)=
    ok (some ⟨⟨1999257868#u32,31750128#u32⟩,⟨362427250#u32,776575600#u32⟩⟩) :=
  JFr_EncodedCell.parser cell21 limbs21 encoded21
#print axioms encoded21
#print axioms parser21
def cell22 : Array U8 16#usize := ⟨[252#u8,198#u8,10#u8,39#u8,77#u8,35#u8,234#u8,22#u8,48#u8,22#u8,249#u8,24#u8,241#u8,200#u8,159#u8,124#u8],by rfl⟩
def limbs22 : QM31Limbs := ![⟨655017724,by change 655017724<2147483647;omega⟩,⟨384443213,by change 384443213<2147483647;omega⟩,⟨418977328,by change 418977328<2147483647;omega⟩,⟨2090846449,by change 2090846449<2147483647;omega⟩]
theorem rawCell22 : (raw.drop 352).take 16=cell22.val := by
  simp only [raw,JFz_Scan52.data,JFz_Scan52.j00,JFz_Scan52.j01,JFz_Scan52.j02,JFz_Scan52.j03,JFz_Scan52.j04,JFz_Scan52.j05,JFz_Scan52.j06,JFz_Scan52.j07,JFz_Scan52.j08,JFz_Scan52.j09,JFz_Scan52.j10,JFz_Scan52.j11,JFz_Scan52.j12,JFz_Scan52.b00_length,JFz_Scan52.b01_length,JFz_Scan52.b02_length,JFz_Scan52.b03_length,JFz_Scan52.b04_length,JFz_Scan52.b05_length,JFz_Scan52.b06_length,JFz_Scan52.b07_length,JFz_Scan52.b08_length,JFz_Scan52.b09_length,JFz_Scan52.b10_length,JFz_Scan52.b11_length,JFz_Scan52.b12_length,JFz_Scan52.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell22
theorem encoded22 : CandidateParserByteOrder.arrayBytes16 cell22=encodeQM31LE limbs22 := by
  funext i
  fin_cases i <;> rfl
theorem parser22 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell22)=
    ok (some ⟨⟨655017724#u32,384443213#u32⟩,⟨418977328#u32,2090846449#u32⟩⟩) :=
  JFr_EncodedCell.parser cell22 limbs22 encoded22
#print axioms encoded22
#print axioms parser22
def cell23 : Array U8 16#usize := ⟨[27#u8,22#u8,78#u8,55#u8,213#u8,80#u8,95#u8,64#u8,71#u8,172#u8,206#u8,0#u8,180#u8,110#u8,103#u8,49#u8],by rfl⟩
def limbs23 : QM31Limbs := ![⟨927864347,by change 927864347<2147483647;omega⟩,⟨1079988437,by change 1079988437<2147483647;omega⟩,⟨13544519,by change 13544519<2147483647;omega⟩,⟨828862132,by change 828862132<2147483647;omega⟩]
theorem rawCell23 : (raw.drop 368).take 16=cell23.val := by
  simp only [raw,JFz_Scan52.data,JFz_Scan52.j00,JFz_Scan52.j01,JFz_Scan52.j02,JFz_Scan52.j03,JFz_Scan52.j04,JFz_Scan52.j05,JFz_Scan52.j06,JFz_Scan52.j07,JFz_Scan52.j08,JFz_Scan52.j09,JFz_Scan52.j10,JFz_Scan52.j11,JFz_Scan52.j12,JFz_Scan52.b00_length,JFz_Scan52.b01_length,JFz_Scan52.b02_length,JFz_Scan52.b03_length,JFz_Scan52.b04_length,JFz_Scan52.b05_length,JFz_Scan52.b06_length,JFz_Scan52.b07_length,JFz_Scan52.b08_length,JFz_Scan52.b09_length,JFz_Scan52.b10_length,JFz_Scan52.b11_length,JFz_Scan52.b12_length,JFz_Scan52.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell23
theorem encoded23 : CandidateParserByteOrder.arrayBytes16 cell23=encodeQM31LE limbs23 := by
  funext i
  fin_cases i <;> rfl
theorem parser23 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell23)=
    ok (some ⟨⟨927864347#u32,1079988437#u32⟩,⟨13544519#u32,828862132#u32⟩⟩) :=
  JFr_EncodedCell.parser cell23 limbs23 encoded23
#print axioms encoded23
#print axioms parser23
def cell24 : Array U8 16#usize := ⟨[1#u8,77#u8,143#u8,39#u8,62#u8,137#u8,72#u8,127#u8,161#u8,24#u8,224#u8,39#u8,1#u8,230#u8,212#u8,115#u8],by rfl⟩
def limbs24 : QM31Limbs := ![⟨663702785,by change 663702785<2147483647;omega⟩,⟨2135460158,by change 2135460158<2147483647;omega⟩,⟨668997793,by change 668997793<2147483647;omega⟩,⟨1943332353,by change 1943332353<2147483647;omega⟩]
theorem rawCell24 : (raw.drop 384).take 16=cell24.val := by
  simp only [raw,JFz_Scan52.data,JFz_Scan52.j00,JFz_Scan52.j01,JFz_Scan52.j02,JFz_Scan52.j03,JFz_Scan52.j04,JFz_Scan52.j05,JFz_Scan52.j06,JFz_Scan52.j07,JFz_Scan52.j08,JFz_Scan52.j09,JFz_Scan52.j10,JFz_Scan52.j11,JFz_Scan52.j12,JFz_Scan52.b00_length,JFz_Scan52.b01_length,JFz_Scan52.b02_length,JFz_Scan52.b03_length,JFz_Scan52.b04_length,JFz_Scan52.b05_length,JFz_Scan52.b06_length,JFz_Scan52.b07_length,JFz_Scan52.b08_length,JFz_Scan52.b09_length,JFz_Scan52.b10_length,JFz_Scan52.b11_length,JFz_Scan52.b12_length,JFz_Scan52.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell24
theorem encoded24 : CandidateParserByteOrder.arrayBytes16 cell24=encodeQM31LE limbs24 := by
  funext i
  fin_cases i <;> rfl
theorem parser24 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell24)=
    ok (some ⟨⟨663702785#u32,2135460158#u32⟩,⟨668997793#u32,1943332353#u32⟩⟩) :=
  JFr_EncodedCell.parser cell24 limbs24 encoded24
#print axioms encoded24
#print axioms parser24
def cell25 : Array U8 16#usize := ⟨[185#u8,34#u8,16#u8,22#u8,149#u8,201#u8,108#u8,113#u8,60#u8,180#u8,63#u8,7#u8,117#u8,147#u8,160#u8,109#u8],by rfl⟩
def limbs25 : QM31Limbs := ![⟨370156217,by change 370156217<2147483647;omega⟩,⟨1902954901,by change 1902954901<2147483647;omega⟩,⟨121615420,by change 121615420<2147483647;omega⟩,⟨1839240053,by change 1839240053<2147483647;omega⟩]
theorem rawCell25 : (raw.drop 400).take 16=cell25.val := by
  simp only [raw,JFz_Scan52.data,JFz_Scan52.j00,JFz_Scan52.j01,JFz_Scan52.j02,JFz_Scan52.j03,JFz_Scan52.j04,JFz_Scan52.j05,JFz_Scan52.j06,JFz_Scan52.j07,JFz_Scan52.j08,JFz_Scan52.j09,JFz_Scan52.j10,JFz_Scan52.j11,JFz_Scan52.j12,JFz_Scan52.b00_length,JFz_Scan52.b01_length,JFz_Scan52.b02_length,JFz_Scan52.b03_length,JFz_Scan52.b04_length,JFz_Scan52.b05_length,JFz_Scan52.b06_length,JFz_Scan52.b07_length,JFz_Scan52.b08_length,JFz_Scan52.b09_length,JFz_Scan52.b10_length,JFz_Scan52.b11_length,JFz_Scan52.b12_length,JFz_Scan52.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell25
theorem encoded25 : CandidateParserByteOrder.arrayBytes16 cell25=encodeQM31LE limbs25 := by
  funext i
  fin_cases i <;> rfl
theorem parser25 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell25)=
    ok (some ⟨⟨370156217#u32,1902954901#u32⟩,⟨121615420#u32,1839240053#u32⟩⟩) :=
  JFr_EncodedCell.parser cell25 limbs25 encoded25
#print axioms encoded25
#print axioms parser25
def cell26 : Array U8 16#usize := ⟨[97#u8,124#u8,81#u8,24#u8,121#u8,209#u8,39#u8,58#u8,139#u8,117#u8,240#u8,118#u8,65#u8,159#u8,104#u8,10#u8],by rfl⟩
def limbs26 : QM31Limbs := ![⟨407993441,by change 407993441<2147483647;omega⟩,⟨975688057,by change 975688057<2147483647;omega⟩,⟨1995470219,by change 1995470219<2147483647;omega⟩,⟨174628673,by change 174628673<2147483647;omega⟩]
theorem rawCell26 : (raw.drop 416).take 16=cell26.val := by
  simp only [raw,JFz_Scan52.data,JFz_Scan52.j00,JFz_Scan52.j01,JFz_Scan52.j02,JFz_Scan52.j03,JFz_Scan52.j04,JFz_Scan52.j05,JFz_Scan52.j06,JFz_Scan52.j07,JFz_Scan52.j08,JFz_Scan52.j09,JFz_Scan52.j10,JFz_Scan52.j11,JFz_Scan52.j12,JFz_Scan52.b00_length,JFz_Scan52.b01_length,JFz_Scan52.b02_length,JFz_Scan52.b03_length,JFz_Scan52.b04_length,JFz_Scan52.b05_length,JFz_Scan52.b06_length,JFz_Scan52.b07_length,JFz_Scan52.b08_length,JFz_Scan52.b09_length,JFz_Scan52.b10_length,JFz_Scan52.b11_length,JFz_Scan52.b12_length,JFz_Scan52.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell26
theorem encoded26 : CandidateParserByteOrder.arrayBytes16 cell26=encodeQM31LE limbs26 := by
  funext i
  fin_cases i <;> rfl
theorem parser26 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell26)=
    ok (some ⟨⟨407993441#u32,975688057#u32⟩,⟨1995470219#u32,174628673#u32⟩⟩) :=
  JFr_EncodedCell.parser cell26 limbs26 encoded26
#print axioms encoded26
#print axioms parser26
def cell27 : Array U8 16#usize := ⟨[47#u8,248#u8,101#u8,97#u8,68#u8,187#u8,254#u8,27#u8,73#u8,192#u8,211#u8,97#u8,220#u8,152#u8,111#u8,18#u8],by rfl⟩
def limbs27 : QM31Limbs := ![⟨1634072623,by change 1634072623<2147483647;omega⟩,⟨469678916,by change 469678916<2147483647;omega⟩,⟨1641267273,by change 1641267273<2147483647;omega⟩,⟨309303516,by change 309303516<2147483647;omega⟩]
theorem rawCell27 : (raw.drop 432).take 16=cell27.val := by
  simp only [raw,JFz_Scan52.data,JFz_Scan52.j00,JFz_Scan52.j01,JFz_Scan52.j02,JFz_Scan52.j03,JFz_Scan52.j04,JFz_Scan52.j05,JFz_Scan52.j06,JFz_Scan52.j07,JFz_Scan52.j08,JFz_Scan52.j09,JFz_Scan52.j10,JFz_Scan52.j11,JFz_Scan52.j12,JFz_Scan52.b00_length,JFz_Scan52.b01_length,JFz_Scan52.b02_length,JFz_Scan52.b03_length,JFz_Scan52.b04_length,JFz_Scan52.b05_length,JFz_Scan52.b06_length,JFz_Scan52.b07_length,JFz_Scan52.b08_length,JFz_Scan52.b09_length,JFz_Scan52.b10_length,JFz_Scan52.b11_length,JFz_Scan52.b12_length,JFz_Scan52.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell27
theorem encoded27 : CandidateParserByteOrder.arrayBytes16 cell27=encodeQM31LE limbs27 := by
  funext i
  fin_cases i <;> rfl
theorem parser27 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell27)=
    ok (some ⟨⟨1634072623#u32,469678916#u32⟩,⟨1641267273#u32,309303516#u32⟩⟩) :=
  JFr_EncodedCell.parser cell27 limbs27 encoded27
#print axioms encoded27
#print axioms parser27
end AspisR1.JFr_Bytes04
