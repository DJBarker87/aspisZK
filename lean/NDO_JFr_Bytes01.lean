import NDO_JFr_Data01
import NDO_JFr_EncodedCell
import NDO_JFz_Scan49
set_option autoImplicit false
namespace AspisR1.JFr_Bytes01
open Aeneas Aeneas.Std Result RetainedFieldByteCodec
open AspisR1PublicPreparation
open AspisS1ExtractedRoundChildren
def raw : List U8 := JFz_Scan49.data
theorem rawLength : raw.length=448 := JFz_Scan49.length
#print axioms rawLength
theorem selected : (JFx_NativeBytes.proof.val.drop 629).take 448=raw := JFz_Scan49.selected
#print axioms selected
def cell00 : Array U8 16#usize := ⟨[243#u8,3#u8,34#u8,14#u8,109#u8,208#u8,140#u8,64#u8,80#u8,37#u8,231#u8,102#u8,207#u8,91#u8,0#u8,44#u8],by rfl⟩
def limbs00 : QM31Limbs := ![⟨237110259,by change 237110259<2147483647;omega⟩,⟨1082970221,by change 1082970221<2147483647;omega⟩,⟨1726424400,by change 1726424400<2147483647;omega⟩,⟨738221007,by change 738221007<2147483647;omega⟩]
theorem rawCell00 : (raw.drop 0).take 16=cell00.val := by
  simp only [raw,JFz_Scan49.data,JFz_Scan49.j00,JFz_Scan49.j01,JFz_Scan49.j02,JFz_Scan49.j03,JFz_Scan49.j04,JFz_Scan49.j05,JFz_Scan49.j06,JFz_Scan49.j07,JFz_Scan49.j08,JFz_Scan49.j09,JFz_Scan49.j10,JFz_Scan49.j11,JFz_Scan49.j12,JFz_Scan49.b00_length,JFz_Scan49.b01_length,JFz_Scan49.b02_length,JFz_Scan49.b03_length,JFz_Scan49.b04_length,JFz_Scan49.b05_length,JFz_Scan49.b06_length,JFz_Scan49.b07_length,JFz_Scan49.b08_length,JFz_Scan49.b09_length,JFz_Scan49.b10_length,JFz_Scan49.b11_length,JFz_Scan49.b12_length,JFz_Scan49.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell00
theorem encoded00 : CandidateParserByteOrder.arrayBytes16 cell00=encodeQM31LE limbs00 := by
  funext i
  fin_cases i <;> rfl
theorem parser00 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell00)=
    ok (some ⟨⟨237110259#u32,1082970221#u32⟩,⟨1726424400#u32,738221007#u32⟩⟩) :=
  JFr_EncodedCell.parser cell00 limbs00 encoded00
#print axioms encoded00
#print axioms parser00
def cell01 : Array U8 16#usize := ⟨[197#u8,71#u8,97#u8,91#u8,199#u8,104#u8,34#u8,60#u8,58#u8,212#u8,55#u8,127#u8,134#u8,6#u8,103#u8,9#u8],by rfl⟩
def limbs01 : QM31Limbs := ![⟨1533102021,by change 1533102021<2147483647;omega⟩,⟨1008888007,by change 1008888007<2147483647;omega⟩,⟨2134365242,by change 2134365242<2147483647;omega⟩,⟨157746822,by change 157746822<2147483647;omega⟩]
theorem rawCell01 : (raw.drop 16).take 16=cell01.val := by
  simp only [raw,JFz_Scan49.data,JFz_Scan49.j00,JFz_Scan49.j01,JFz_Scan49.j02,JFz_Scan49.j03,JFz_Scan49.j04,JFz_Scan49.j05,JFz_Scan49.j06,JFz_Scan49.j07,JFz_Scan49.j08,JFz_Scan49.j09,JFz_Scan49.j10,JFz_Scan49.j11,JFz_Scan49.j12,JFz_Scan49.b00_length,JFz_Scan49.b01_length,JFz_Scan49.b02_length,JFz_Scan49.b03_length,JFz_Scan49.b04_length,JFz_Scan49.b05_length,JFz_Scan49.b06_length,JFz_Scan49.b07_length,JFz_Scan49.b08_length,JFz_Scan49.b09_length,JFz_Scan49.b10_length,JFz_Scan49.b11_length,JFz_Scan49.b12_length,JFz_Scan49.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell01
theorem encoded01 : CandidateParserByteOrder.arrayBytes16 cell01=encodeQM31LE limbs01 := by
  funext i
  fin_cases i <;> rfl
theorem parser01 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell01)=
    ok (some ⟨⟨1533102021#u32,1008888007#u32⟩,⟨2134365242#u32,157746822#u32⟩⟩) :=
  JFr_EncodedCell.parser cell01 limbs01 encoded01
#print axioms encoded01
#print axioms parser01
def cell02 : Array U8 16#usize := ⟨[26#u8,69#u8,147#u8,28#u8,51#u8,151#u8,200#u8,39#u8,112#u8,247#u8,219#u8,110#u8,193#u8,209#u8,18#u8,66#u8],by rfl⟩
def limbs02 : QM31Limbs := ![⟨479413530,by change 479413530<2147483647;omega⟩,⟨667457331,by change 667457331<2147483647;omega⟩,⟨1859909488,by change 1859909488<2147483647;omega⟩,⟨1108529601,by change 1108529601<2147483647;omega⟩]
theorem rawCell02 : (raw.drop 32).take 16=cell02.val := by
  simp only [raw,JFz_Scan49.data,JFz_Scan49.j00,JFz_Scan49.j01,JFz_Scan49.j02,JFz_Scan49.j03,JFz_Scan49.j04,JFz_Scan49.j05,JFz_Scan49.j06,JFz_Scan49.j07,JFz_Scan49.j08,JFz_Scan49.j09,JFz_Scan49.j10,JFz_Scan49.j11,JFz_Scan49.j12,JFz_Scan49.b00_length,JFz_Scan49.b01_length,JFz_Scan49.b02_length,JFz_Scan49.b03_length,JFz_Scan49.b04_length,JFz_Scan49.b05_length,JFz_Scan49.b06_length,JFz_Scan49.b07_length,JFz_Scan49.b08_length,JFz_Scan49.b09_length,JFz_Scan49.b10_length,JFz_Scan49.b11_length,JFz_Scan49.b12_length,JFz_Scan49.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell02
theorem encoded02 : CandidateParserByteOrder.arrayBytes16 cell02=encodeQM31LE limbs02 := by
  funext i
  fin_cases i <;> rfl
theorem parser02 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell02)=
    ok (some ⟨⟨479413530#u32,667457331#u32⟩,⟨1859909488#u32,1108529601#u32⟩⟩) :=
  JFr_EncodedCell.parser cell02 limbs02 encoded02
#print axioms encoded02
#print axioms parser02
def cell03 : Array U8 16#usize := ⟨[183#u8,184#u8,76#u8,67#u8,34#u8,13#u8,108#u8,47#u8,248#u8,81#u8,52#u8,70#u8,74#u8,126#u8,244#u8,68#u8],by rfl⟩
def limbs03 : QM31Limbs := ![⟨1129101495,by change 1129101495<2147483647;omega⟩,⟨795610402,by change 795610402<2147483647;omega⟩,⟨1177833976,by change 1177833976<2147483647;omega⟩,⟨1156873802,by change 1156873802<2147483647;omega⟩]
theorem rawCell03 : (raw.drop 48).take 16=cell03.val := by
  simp only [raw,JFz_Scan49.data,JFz_Scan49.j00,JFz_Scan49.j01,JFz_Scan49.j02,JFz_Scan49.j03,JFz_Scan49.j04,JFz_Scan49.j05,JFz_Scan49.j06,JFz_Scan49.j07,JFz_Scan49.j08,JFz_Scan49.j09,JFz_Scan49.j10,JFz_Scan49.j11,JFz_Scan49.j12,JFz_Scan49.b00_length,JFz_Scan49.b01_length,JFz_Scan49.b02_length,JFz_Scan49.b03_length,JFz_Scan49.b04_length,JFz_Scan49.b05_length,JFz_Scan49.b06_length,JFz_Scan49.b07_length,JFz_Scan49.b08_length,JFz_Scan49.b09_length,JFz_Scan49.b10_length,JFz_Scan49.b11_length,JFz_Scan49.b12_length,JFz_Scan49.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell03
theorem encoded03 : CandidateParserByteOrder.arrayBytes16 cell03=encodeQM31LE limbs03 := by
  funext i
  fin_cases i <;> rfl
theorem parser03 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell03)=
    ok (some ⟨⟨1129101495#u32,795610402#u32⟩,⟨1177833976#u32,1156873802#u32⟩⟩) :=
  JFr_EncodedCell.parser cell03 limbs03 encoded03
#print axioms encoded03
#print axioms parser03
def cell04 : Array U8 16#usize := ⟨[140#u8,2#u8,140#u8,107#u8,62#u8,187#u8,165#u8,19#u8,87#u8,35#u8,69#u8,107#u8,237#u8,39#u8,39#u8,87#u8],by rfl⟩
def limbs04 : QM31Limbs := ![⟨1804337804,by change 1804337804<2147483647;omega⟩,⟨329628478,by change 329628478<2147483647;omega⟩,⟨1799693143,by change 1799693143<2147483647;omega⟩,⟨1462183917,by change 1462183917<2147483647;omega⟩]
theorem rawCell04 : (raw.drop 64).take 16=cell04.val := by
  simp only [raw,JFz_Scan49.data,JFz_Scan49.j00,JFz_Scan49.j01,JFz_Scan49.j02,JFz_Scan49.j03,JFz_Scan49.j04,JFz_Scan49.j05,JFz_Scan49.j06,JFz_Scan49.j07,JFz_Scan49.j08,JFz_Scan49.j09,JFz_Scan49.j10,JFz_Scan49.j11,JFz_Scan49.j12,JFz_Scan49.b00_length,JFz_Scan49.b01_length,JFz_Scan49.b02_length,JFz_Scan49.b03_length,JFz_Scan49.b04_length,JFz_Scan49.b05_length,JFz_Scan49.b06_length,JFz_Scan49.b07_length,JFz_Scan49.b08_length,JFz_Scan49.b09_length,JFz_Scan49.b10_length,JFz_Scan49.b11_length,JFz_Scan49.b12_length,JFz_Scan49.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell04
theorem encoded04 : CandidateParserByteOrder.arrayBytes16 cell04=encodeQM31LE limbs04 := by
  funext i
  fin_cases i <;> rfl
theorem parser04 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell04)=
    ok (some ⟨⟨1804337804#u32,329628478#u32⟩,⟨1799693143#u32,1462183917#u32⟩⟩) :=
  JFr_EncodedCell.parser cell04 limbs04 encoded04
#print axioms encoded04
#print axioms parser04
def cell05 : Array U8 16#usize := ⟨[232#u8,147#u8,250#u8,0#u8,96#u8,7#u8,132#u8,86#u8,14#u8,2#u8,96#u8,126#u8,118#u8,216#u8,201#u8,80#u8],by rfl⟩
def limbs05 : QM31Limbs := ![⟨16421864,by change 16421864<2147483647;omega⟩,⟨1451493216,by change 1451493216<2147483647;omega⟩,⟨2120221198,by change 2120221198<2147483647;omega⟩,⟨1355405430,by change 1355405430<2147483647;omega⟩]
theorem rawCell05 : (raw.drop 80).take 16=cell05.val := by
  simp only [raw,JFz_Scan49.data,JFz_Scan49.j00,JFz_Scan49.j01,JFz_Scan49.j02,JFz_Scan49.j03,JFz_Scan49.j04,JFz_Scan49.j05,JFz_Scan49.j06,JFz_Scan49.j07,JFz_Scan49.j08,JFz_Scan49.j09,JFz_Scan49.j10,JFz_Scan49.j11,JFz_Scan49.j12,JFz_Scan49.b00_length,JFz_Scan49.b01_length,JFz_Scan49.b02_length,JFz_Scan49.b03_length,JFz_Scan49.b04_length,JFz_Scan49.b05_length,JFz_Scan49.b06_length,JFz_Scan49.b07_length,JFz_Scan49.b08_length,JFz_Scan49.b09_length,JFz_Scan49.b10_length,JFz_Scan49.b11_length,JFz_Scan49.b12_length,JFz_Scan49.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell05
theorem encoded05 : CandidateParserByteOrder.arrayBytes16 cell05=encodeQM31LE limbs05 := by
  funext i
  fin_cases i <;> rfl
theorem parser05 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell05)=
    ok (some ⟨⟨16421864#u32,1451493216#u32⟩,⟨2120221198#u32,1355405430#u32⟩⟩) :=
  JFr_EncodedCell.parser cell05 limbs05 encoded05
#print axioms encoded05
#print axioms parser05
def cell06 : Array U8 16#usize := ⟨[131#u8,9#u8,94#u8,113#u8,87#u8,3#u8,90#u8,114#u8,109#u8,148#u8,216#u8,68#u8,202#u8,91#u8,16#u8,107#u8],by rfl⟩
def limbs06 : QM31Limbs := ![⟨1901988227,by change 1901988227<2147483647;omega⟩,⟨1918501719,by change 1918501719<2147483647;omega⟩,⟨1155044461,by change 1155044461<2147483647;omega⟩,⟨1796234186,by change 1796234186<2147483647;omega⟩]
theorem rawCell06 : (raw.drop 96).take 16=cell06.val := by
  simp only [raw,JFz_Scan49.data,JFz_Scan49.j00,JFz_Scan49.j01,JFz_Scan49.j02,JFz_Scan49.j03,JFz_Scan49.j04,JFz_Scan49.j05,JFz_Scan49.j06,JFz_Scan49.j07,JFz_Scan49.j08,JFz_Scan49.j09,JFz_Scan49.j10,JFz_Scan49.j11,JFz_Scan49.j12,JFz_Scan49.b00_length,JFz_Scan49.b01_length,JFz_Scan49.b02_length,JFz_Scan49.b03_length,JFz_Scan49.b04_length,JFz_Scan49.b05_length,JFz_Scan49.b06_length,JFz_Scan49.b07_length,JFz_Scan49.b08_length,JFz_Scan49.b09_length,JFz_Scan49.b10_length,JFz_Scan49.b11_length,JFz_Scan49.b12_length,JFz_Scan49.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell06
theorem encoded06 : CandidateParserByteOrder.arrayBytes16 cell06=encodeQM31LE limbs06 := by
  funext i
  fin_cases i <;> rfl
theorem parser06 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell06)=
    ok (some ⟨⟨1901988227#u32,1918501719#u32⟩,⟨1155044461#u32,1796234186#u32⟩⟩) :=
  JFr_EncodedCell.parser cell06 limbs06 encoded06
#print axioms encoded06
#print axioms parser06
def cell07 : Array U8 16#usize := ⟨[39#u8,135#u8,159#u8,98#u8,254#u8,53#u8,167#u8,117#u8,129#u8,192#u8,190#u8,1#u8,99#u8,142#u8,215#u8,92#u8],by rfl⟩
def limbs07 : QM31Limbs := ![⟨1654621991,by change 1654621991<2147483647;omega⟩,⟨1973892606,by change 1973892606<2147483647;omega⟩,⟨29278337,by change 29278337<2147483647;omega⟩,⟨1557630563,by change 1557630563<2147483647;omega⟩]
theorem rawCell07 : (raw.drop 112).take 16=cell07.val := by
  simp only [raw,JFz_Scan49.data,JFz_Scan49.j00,JFz_Scan49.j01,JFz_Scan49.j02,JFz_Scan49.j03,JFz_Scan49.j04,JFz_Scan49.j05,JFz_Scan49.j06,JFz_Scan49.j07,JFz_Scan49.j08,JFz_Scan49.j09,JFz_Scan49.j10,JFz_Scan49.j11,JFz_Scan49.j12,JFz_Scan49.b00_length,JFz_Scan49.b01_length,JFz_Scan49.b02_length,JFz_Scan49.b03_length,JFz_Scan49.b04_length,JFz_Scan49.b05_length,JFz_Scan49.b06_length,JFz_Scan49.b07_length,JFz_Scan49.b08_length,JFz_Scan49.b09_length,JFz_Scan49.b10_length,JFz_Scan49.b11_length,JFz_Scan49.b12_length,JFz_Scan49.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell07
theorem encoded07 : CandidateParserByteOrder.arrayBytes16 cell07=encodeQM31LE limbs07 := by
  funext i
  fin_cases i <;> rfl
theorem parser07 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell07)=
    ok (some ⟨⟨1654621991#u32,1973892606#u32⟩,⟨29278337#u32,1557630563#u32⟩⟩) :=
  JFr_EncodedCell.parser cell07 limbs07 encoded07
#print axioms encoded07
#print axioms parser07
def cell08 : Array U8 16#usize := ⟨[234#u8,126#u8,195#u8,95#u8,110#u8,52#u8,27#u8,87#u8,154#u8,37#u8,22#u8,25#u8,193#u8,65#u8,40#u8,106#u8],by rfl⟩
def limbs08 : QM31Limbs := ![⟨1606647530,by change 1606647530<2147483647;omega⟩,⟨1461400686,by change 1461400686<2147483647;omega⟩,⟨420881818,by change 420881818<2147483647;omega⟩,⟨1781023169,by change 1781023169<2147483647;omega⟩]
theorem rawCell08 : (raw.drop 128).take 16=cell08.val := by
  simp only [raw,JFz_Scan49.data,JFz_Scan49.j00,JFz_Scan49.j01,JFz_Scan49.j02,JFz_Scan49.j03,JFz_Scan49.j04,JFz_Scan49.j05,JFz_Scan49.j06,JFz_Scan49.j07,JFz_Scan49.j08,JFz_Scan49.j09,JFz_Scan49.j10,JFz_Scan49.j11,JFz_Scan49.j12,JFz_Scan49.b00_length,JFz_Scan49.b01_length,JFz_Scan49.b02_length,JFz_Scan49.b03_length,JFz_Scan49.b04_length,JFz_Scan49.b05_length,JFz_Scan49.b06_length,JFz_Scan49.b07_length,JFz_Scan49.b08_length,JFz_Scan49.b09_length,JFz_Scan49.b10_length,JFz_Scan49.b11_length,JFz_Scan49.b12_length,JFz_Scan49.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell08
theorem encoded08 : CandidateParserByteOrder.arrayBytes16 cell08=encodeQM31LE limbs08 := by
  funext i
  fin_cases i <;> rfl
theorem parser08 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell08)=
    ok (some ⟨⟨1606647530#u32,1461400686#u32⟩,⟨420881818#u32,1781023169#u32⟩⟩) :=
  JFr_EncodedCell.parser cell08 limbs08 encoded08
#print axioms encoded08
#print axioms parser08
def cell09 : Array U8 16#usize := ⟨[252#u8,219#u8,178#u8,127#u8,207#u8,219#u8,147#u8,12#u8,184#u8,56#u8,85#u8,63#u8,14#u8,194#u8,101#u8,74#u8],by rfl⟩
def limbs09 : QM31Limbs := ![⟨2142428156,by change 2142428156<2147483647;omega⟩,⟨211016655,by change 211016655<2147483647;omega⟩,⟨1062549688,by change 1062549688<2147483647;omega⟩,⟨1248182798,by change 1248182798<2147483647;omega⟩]
theorem rawCell09 : (raw.drop 144).take 16=cell09.val := by
  simp only [raw,JFz_Scan49.data,JFz_Scan49.j00,JFz_Scan49.j01,JFz_Scan49.j02,JFz_Scan49.j03,JFz_Scan49.j04,JFz_Scan49.j05,JFz_Scan49.j06,JFz_Scan49.j07,JFz_Scan49.j08,JFz_Scan49.j09,JFz_Scan49.j10,JFz_Scan49.j11,JFz_Scan49.j12,JFz_Scan49.b00_length,JFz_Scan49.b01_length,JFz_Scan49.b02_length,JFz_Scan49.b03_length,JFz_Scan49.b04_length,JFz_Scan49.b05_length,JFz_Scan49.b06_length,JFz_Scan49.b07_length,JFz_Scan49.b08_length,JFz_Scan49.b09_length,JFz_Scan49.b10_length,JFz_Scan49.b11_length,JFz_Scan49.b12_length,JFz_Scan49.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell09
theorem encoded09 : CandidateParserByteOrder.arrayBytes16 cell09=encodeQM31LE limbs09 := by
  funext i
  fin_cases i <;> rfl
theorem parser09 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell09)=
    ok (some ⟨⟨2142428156#u32,211016655#u32⟩,⟨1062549688#u32,1248182798#u32⟩⟩) :=
  JFr_EncodedCell.parser cell09 limbs09 encoded09
#print axioms encoded09
#print axioms parser09
def cell10 : Array U8 16#usize := ⟨[96#u8,168#u8,29#u8,63#u8,172#u8,238#u8,91#u8,32#u8,3#u8,141#u8,133#u8,104#u8,61#u8,122#u8,174#u8,110#u8],by rfl⟩
def limbs10 : QM31Limbs := ![⟨1058908256,by change 1058908256<2147483647;omega⟩,⟨542895788,by change 542895788<2147483647;omega⟩,⟨1753582851,by change 1753582851<2147483647;omega⟩,⟨1856928317,by change 1856928317<2147483647;omega⟩]
theorem rawCell10 : (raw.drop 160).take 16=cell10.val := by
  simp only [raw,JFz_Scan49.data,JFz_Scan49.j00,JFz_Scan49.j01,JFz_Scan49.j02,JFz_Scan49.j03,JFz_Scan49.j04,JFz_Scan49.j05,JFz_Scan49.j06,JFz_Scan49.j07,JFz_Scan49.j08,JFz_Scan49.j09,JFz_Scan49.j10,JFz_Scan49.j11,JFz_Scan49.j12,JFz_Scan49.b00_length,JFz_Scan49.b01_length,JFz_Scan49.b02_length,JFz_Scan49.b03_length,JFz_Scan49.b04_length,JFz_Scan49.b05_length,JFz_Scan49.b06_length,JFz_Scan49.b07_length,JFz_Scan49.b08_length,JFz_Scan49.b09_length,JFz_Scan49.b10_length,JFz_Scan49.b11_length,JFz_Scan49.b12_length,JFz_Scan49.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell10
theorem encoded10 : CandidateParserByteOrder.arrayBytes16 cell10=encodeQM31LE limbs10 := by
  funext i
  fin_cases i <;> rfl
theorem parser10 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell10)=
    ok (some ⟨⟨1058908256#u32,542895788#u32⟩,⟨1753582851#u32,1856928317#u32⟩⟩) :=
  JFr_EncodedCell.parser cell10 limbs10 encoded10
#print axioms encoded10
#print axioms parser10
def cell11 : Array U8 16#usize := ⟨[244#u8,42#u8,44#u8,81#u8,14#u8,136#u8,145#u8,5#u8,157#u8,43#u8,24#u8,61#u8,6#u8,38#u8,254#u8,21#u8],by rfl⟩
def limbs11 : QM31Limbs := ![⟨1361849076,by change 1361849076<2147483647;omega⟩,⟨93423630,by change 93423630<2147483647;omega⟩,⟨1024994205,by change 1024994205<2147483647;omega⟩,⟨368977414,by change 368977414<2147483647;omega⟩]
theorem rawCell11 : (raw.drop 176).take 16=cell11.val := by
  simp only [raw,JFz_Scan49.data,JFz_Scan49.j00,JFz_Scan49.j01,JFz_Scan49.j02,JFz_Scan49.j03,JFz_Scan49.j04,JFz_Scan49.j05,JFz_Scan49.j06,JFz_Scan49.j07,JFz_Scan49.j08,JFz_Scan49.j09,JFz_Scan49.j10,JFz_Scan49.j11,JFz_Scan49.j12,JFz_Scan49.b00_length,JFz_Scan49.b01_length,JFz_Scan49.b02_length,JFz_Scan49.b03_length,JFz_Scan49.b04_length,JFz_Scan49.b05_length,JFz_Scan49.b06_length,JFz_Scan49.b07_length,JFz_Scan49.b08_length,JFz_Scan49.b09_length,JFz_Scan49.b10_length,JFz_Scan49.b11_length,JFz_Scan49.b12_length,JFz_Scan49.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell11
theorem encoded11 : CandidateParserByteOrder.arrayBytes16 cell11=encodeQM31LE limbs11 := by
  funext i
  fin_cases i <;> rfl
theorem parser11 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell11)=
    ok (some ⟨⟨1361849076#u32,93423630#u32⟩,⟨1024994205#u32,368977414#u32⟩⟩) :=
  JFr_EncodedCell.parser cell11 limbs11 encoded11
#print axioms encoded11
#print axioms parser11
def cell12 : Array U8 16#usize := ⟨[150#u8,196#u8,143#u8,70#u8,62#u8,238#u8,181#u8,80#u8,42#u8,40#u8,4#u8,73#u8,30#u8,184#u8,98#u8,32#u8],by rfl⟩
def limbs12 : QM31Limbs := ![⟨1183827094,by change 1183827094<2147483647;omega⟩,⟨1354100286,by change 1354100286<2147483647;omega⟩,⟨1225009194,by change 1225009194<2147483647;omega⟩,⟨543340574,by change 543340574<2147483647;omega⟩]
theorem rawCell12 : (raw.drop 192).take 16=cell12.val := by
  simp only [raw,JFz_Scan49.data,JFz_Scan49.j00,JFz_Scan49.j01,JFz_Scan49.j02,JFz_Scan49.j03,JFz_Scan49.j04,JFz_Scan49.j05,JFz_Scan49.j06,JFz_Scan49.j07,JFz_Scan49.j08,JFz_Scan49.j09,JFz_Scan49.j10,JFz_Scan49.j11,JFz_Scan49.j12,JFz_Scan49.b00_length,JFz_Scan49.b01_length,JFz_Scan49.b02_length,JFz_Scan49.b03_length,JFz_Scan49.b04_length,JFz_Scan49.b05_length,JFz_Scan49.b06_length,JFz_Scan49.b07_length,JFz_Scan49.b08_length,JFz_Scan49.b09_length,JFz_Scan49.b10_length,JFz_Scan49.b11_length,JFz_Scan49.b12_length,JFz_Scan49.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell12
theorem encoded12 : CandidateParserByteOrder.arrayBytes16 cell12=encodeQM31LE limbs12 := by
  funext i
  fin_cases i <;> rfl
theorem parser12 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell12)=
    ok (some ⟨⟨1183827094#u32,1354100286#u32⟩,⟨1225009194#u32,543340574#u32⟩⟩) :=
  JFr_EncodedCell.parser cell12 limbs12 encoded12
#print axioms encoded12
#print axioms parser12
def cell13 : Array U8 16#usize := ⟨[23#u8,123#u8,166#u8,70#u8,117#u8,244#u8,56#u8,10#u8,203#u8,128#u8,77#u8,107#u8,176#u8,143#u8,179#u8,121#u8],by rfl⟩
def limbs13 : QM31Limbs := ![⟨1185315607,by change 1185315607<2147483647;omega⟩,⟨171504757,by change 171504757<2147483647;omega⟩,⟨1800241355,by change 1800241355<2147483647;omega⟩,⟨2041810864,by change 2041810864<2147483647;omega⟩]
theorem rawCell13 : (raw.drop 208).take 16=cell13.val := by
  simp only [raw,JFz_Scan49.data,JFz_Scan49.j00,JFz_Scan49.j01,JFz_Scan49.j02,JFz_Scan49.j03,JFz_Scan49.j04,JFz_Scan49.j05,JFz_Scan49.j06,JFz_Scan49.j07,JFz_Scan49.j08,JFz_Scan49.j09,JFz_Scan49.j10,JFz_Scan49.j11,JFz_Scan49.j12,JFz_Scan49.b00_length,JFz_Scan49.b01_length,JFz_Scan49.b02_length,JFz_Scan49.b03_length,JFz_Scan49.b04_length,JFz_Scan49.b05_length,JFz_Scan49.b06_length,JFz_Scan49.b07_length,JFz_Scan49.b08_length,JFz_Scan49.b09_length,JFz_Scan49.b10_length,JFz_Scan49.b11_length,JFz_Scan49.b12_length,JFz_Scan49.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell13
theorem encoded13 : CandidateParserByteOrder.arrayBytes16 cell13=encodeQM31LE limbs13 := by
  funext i
  fin_cases i <;> rfl
theorem parser13 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell13)=
    ok (some ⟨⟨1185315607#u32,171504757#u32⟩,⟨1800241355#u32,2041810864#u32⟩⟩) :=
  JFr_EncodedCell.parser cell13 limbs13 encoded13
#print axioms encoded13
#print axioms parser13
def cell14 : Array U8 16#usize := ⟨[234#u8,88#u8,89#u8,32#u8,219#u8,108#u8,237#u8,102#u8,232#u8,108#u8,106#u8,15#u8,202#u8,224#u8,92#u8,18#u8],by rfl⟩
def limbs14 : QM31Limbs := ![⟨542726378,by change 542726378<2147483647;omega⟩,⟨1726835931,by change 1726835931<2147483647;omega⟩,⟨258632936,by change 258632936<2147483647;omega⟩,⟨308076746,by change 308076746<2147483647;omega⟩]
theorem rawCell14 : (raw.drop 224).take 16=cell14.val := by
  simp only [raw,JFz_Scan49.data,JFz_Scan49.j00,JFz_Scan49.j01,JFz_Scan49.j02,JFz_Scan49.j03,JFz_Scan49.j04,JFz_Scan49.j05,JFz_Scan49.j06,JFz_Scan49.j07,JFz_Scan49.j08,JFz_Scan49.j09,JFz_Scan49.j10,JFz_Scan49.j11,JFz_Scan49.j12,JFz_Scan49.b00_length,JFz_Scan49.b01_length,JFz_Scan49.b02_length,JFz_Scan49.b03_length,JFz_Scan49.b04_length,JFz_Scan49.b05_length,JFz_Scan49.b06_length,JFz_Scan49.b07_length,JFz_Scan49.b08_length,JFz_Scan49.b09_length,JFz_Scan49.b10_length,JFz_Scan49.b11_length,JFz_Scan49.b12_length,JFz_Scan49.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell14
theorem encoded14 : CandidateParserByteOrder.arrayBytes16 cell14=encodeQM31LE limbs14 := by
  funext i
  fin_cases i <;> rfl
theorem parser14 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell14)=
    ok (some ⟨⟨542726378#u32,1726835931#u32⟩,⟨258632936#u32,308076746#u32⟩⟩) :=
  JFr_EncodedCell.parser cell14 limbs14 encoded14
#print axioms encoded14
#print axioms parser14
def cell15 : Array U8 16#usize := ⟨[30#u8,91#u8,105#u8,26#u8,58#u8,176#u8,254#u8,64#u8,223#u8,165#u8,146#u8,29#u8,33#u8,202#u8,50#u8,69#u8],by rfl⟩
def limbs15 : QM31Limbs := ![⟨443112222,by change 443112222<2147483647;omega⟩,⟨1090433082,by change 1090433082<2147483647;omega⟩,⟨496149983,by change 496149983<2147483647;omega⟩,⟨1160956449,by change 1160956449<2147483647;omega⟩]
theorem rawCell15 : (raw.drop 240).take 16=cell15.val := by
  simp only [raw,JFz_Scan49.data,JFz_Scan49.j00,JFz_Scan49.j01,JFz_Scan49.j02,JFz_Scan49.j03,JFz_Scan49.j04,JFz_Scan49.j05,JFz_Scan49.j06,JFz_Scan49.j07,JFz_Scan49.j08,JFz_Scan49.j09,JFz_Scan49.j10,JFz_Scan49.j11,JFz_Scan49.j12,JFz_Scan49.b00_length,JFz_Scan49.b01_length,JFz_Scan49.b02_length,JFz_Scan49.b03_length,JFz_Scan49.b04_length,JFz_Scan49.b05_length,JFz_Scan49.b06_length,JFz_Scan49.b07_length,JFz_Scan49.b08_length,JFz_Scan49.b09_length,JFz_Scan49.b10_length,JFz_Scan49.b11_length,JFz_Scan49.b12_length,JFz_Scan49.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell15
theorem encoded15 : CandidateParserByteOrder.arrayBytes16 cell15=encodeQM31LE limbs15 := by
  funext i
  fin_cases i <;> rfl
theorem parser15 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell15)=
    ok (some ⟨⟨443112222#u32,1090433082#u32⟩,⟨496149983#u32,1160956449#u32⟩⟩) :=
  JFr_EncodedCell.parser cell15 limbs15 encoded15
#print axioms encoded15
#print axioms parser15
def cell16 : Array U8 16#usize := ⟨[227#u8,32#u8,255#u8,125#u8,70#u8,177#u8,173#u8,86#u8,204#u8,44#u8,173#u8,126#u8,88#u8,22#u8,179#u8,94#u8],by rfl⟩
def limbs16 : QM31Limbs := ![⟨2113872099,by change 2113872099<2147483647;omega⟩,⟨1454223686,by change 1454223686<2147483647;omega⟩,⟨2125278412,by change 2125278412<2147483647;omega⟩,⟨1588794968,by change 1588794968<2147483647;omega⟩]
theorem rawCell16 : (raw.drop 256).take 16=cell16.val := by
  simp only [raw,JFz_Scan49.data,JFz_Scan49.j00,JFz_Scan49.j01,JFz_Scan49.j02,JFz_Scan49.j03,JFz_Scan49.j04,JFz_Scan49.j05,JFz_Scan49.j06,JFz_Scan49.j07,JFz_Scan49.j08,JFz_Scan49.j09,JFz_Scan49.j10,JFz_Scan49.j11,JFz_Scan49.j12,JFz_Scan49.b00_length,JFz_Scan49.b01_length,JFz_Scan49.b02_length,JFz_Scan49.b03_length,JFz_Scan49.b04_length,JFz_Scan49.b05_length,JFz_Scan49.b06_length,JFz_Scan49.b07_length,JFz_Scan49.b08_length,JFz_Scan49.b09_length,JFz_Scan49.b10_length,JFz_Scan49.b11_length,JFz_Scan49.b12_length,JFz_Scan49.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell16
theorem encoded16 : CandidateParserByteOrder.arrayBytes16 cell16=encodeQM31LE limbs16 := by
  funext i
  fin_cases i <;> rfl
theorem parser16 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell16)=
    ok (some ⟨⟨2113872099#u32,1454223686#u32⟩,⟨2125278412#u32,1588794968#u32⟩⟩) :=
  JFr_EncodedCell.parser cell16 limbs16 encoded16
#print axioms encoded16
#print axioms parser16
def cell17 : Array U8 16#usize := ⟨[176#u8,54#u8,133#u8,67#u8,59#u8,24#u8,166#u8,58#u8,27#u8,166#u8,131#u8,26#u8,168#u8,75#u8,192#u8,89#u8],by rfl⟩
def limbs17 : QM31Limbs := ![⟨1132803760,by change 1132803760<2147483647;omega⟩,⟨983963707,by change 983963707<2147483647;omega⟩,⟨444835355,by change 444835355<2147483647;omega⟩,⟨1505774504,by change 1505774504<2147483647;omega⟩]
theorem rawCell17 : (raw.drop 272).take 16=cell17.val := by
  simp only [raw,JFz_Scan49.data,JFz_Scan49.j00,JFz_Scan49.j01,JFz_Scan49.j02,JFz_Scan49.j03,JFz_Scan49.j04,JFz_Scan49.j05,JFz_Scan49.j06,JFz_Scan49.j07,JFz_Scan49.j08,JFz_Scan49.j09,JFz_Scan49.j10,JFz_Scan49.j11,JFz_Scan49.j12,JFz_Scan49.b00_length,JFz_Scan49.b01_length,JFz_Scan49.b02_length,JFz_Scan49.b03_length,JFz_Scan49.b04_length,JFz_Scan49.b05_length,JFz_Scan49.b06_length,JFz_Scan49.b07_length,JFz_Scan49.b08_length,JFz_Scan49.b09_length,JFz_Scan49.b10_length,JFz_Scan49.b11_length,JFz_Scan49.b12_length,JFz_Scan49.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell17
theorem encoded17 : CandidateParserByteOrder.arrayBytes16 cell17=encodeQM31LE limbs17 := by
  funext i
  fin_cases i <;> rfl
theorem parser17 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell17)=
    ok (some ⟨⟨1132803760#u32,983963707#u32⟩,⟨444835355#u32,1505774504#u32⟩⟩) :=
  JFr_EncodedCell.parser cell17 limbs17 encoded17
#print axioms encoded17
#print axioms parser17
def cell18 : Array U8 16#usize := ⟨[245#u8,167#u8,157#u8,75#u8,22#u8,129#u8,2#u8,94#u8,84#u8,0#u8,167#u8,53#u8,232#u8,243#u8,99#u8,34#u8],by rfl⟩
def limbs18 : QM31Limbs := ![⟨1268623349,by change 1268623349<2147483647;omega⟩,⟨1577222422,by change 1577222422<2147483647;omega⟩,⟨900137044,by change 900137044<2147483647;omega⟩,⟨576975848,by change 576975848<2147483647;omega⟩]
theorem rawCell18 : (raw.drop 288).take 16=cell18.val := by
  simp only [raw,JFz_Scan49.data,JFz_Scan49.j00,JFz_Scan49.j01,JFz_Scan49.j02,JFz_Scan49.j03,JFz_Scan49.j04,JFz_Scan49.j05,JFz_Scan49.j06,JFz_Scan49.j07,JFz_Scan49.j08,JFz_Scan49.j09,JFz_Scan49.j10,JFz_Scan49.j11,JFz_Scan49.j12,JFz_Scan49.b00_length,JFz_Scan49.b01_length,JFz_Scan49.b02_length,JFz_Scan49.b03_length,JFz_Scan49.b04_length,JFz_Scan49.b05_length,JFz_Scan49.b06_length,JFz_Scan49.b07_length,JFz_Scan49.b08_length,JFz_Scan49.b09_length,JFz_Scan49.b10_length,JFz_Scan49.b11_length,JFz_Scan49.b12_length,JFz_Scan49.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell18
theorem encoded18 : CandidateParserByteOrder.arrayBytes16 cell18=encodeQM31LE limbs18 := by
  funext i
  fin_cases i <;> rfl
theorem parser18 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell18)=
    ok (some ⟨⟨1268623349#u32,1577222422#u32⟩,⟨900137044#u32,576975848#u32⟩⟩) :=
  JFr_EncodedCell.parser cell18 limbs18 encoded18
#print axioms encoded18
#print axioms parser18
def cell19 : Array U8 16#usize := ⟨[42#u8,11#u8,207#u8,12#u8,223#u8,92#u8,28#u8,93#u8,51#u8,38#u8,231#u8,35#u8,199#u8,14#u8,10#u8,41#u8],by rfl⟩
def limbs19 : QM31Limbs := ![⟨214895402,by change 214895402<2147483647;omega⟩,⟨1562139871,by change 1562139871<2147483647;omega⟩,⟨602351155,by change 602351155<2147483647;omega⟩,⟨688524999,by change 688524999<2147483647;omega⟩]
theorem rawCell19 : (raw.drop 304).take 16=cell19.val := by
  simp only [raw,JFz_Scan49.data,JFz_Scan49.j00,JFz_Scan49.j01,JFz_Scan49.j02,JFz_Scan49.j03,JFz_Scan49.j04,JFz_Scan49.j05,JFz_Scan49.j06,JFz_Scan49.j07,JFz_Scan49.j08,JFz_Scan49.j09,JFz_Scan49.j10,JFz_Scan49.j11,JFz_Scan49.j12,JFz_Scan49.b00_length,JFz_Scan49.b01_length,JFz_Scan49.b02_length,JFz_Scan49.b03_length,JFz_Scan49.b04_length,JFz_Scan49.b05_length,JFz_Scan49.b06_length,JFz_Scan49.b07_length,JFz_Scan49.b08_length,JFz_Scan49.b09_length,JFz_Scan49.b10_length,JFz_Scan49.b11_length,JFz_Scan49.b12_length,JFz_Scan49.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell19
theorem encoded19 : CandidateParserByteOrder.arrayBytes16 cell19=encodeQM31LE limbs19 := by
  funext i
  fin_cases i <;> rfl
theorem parser19 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell19)=
    ok (some ⟨⟨214895402#u32,1562139871#u32⟩,⟨602351155#u32,688524999#u32⟩⟩) :=
  JFr_EncodedCell.parser cell19 limbs19 encoded19
#print axioms encoded19
#print axioms parser19
def cell20 : Array U8 16#usize := ⟨[124#u8,174#u8,106#u8,11#u8,178#u8,30#u8,11#u8,2#u8,52#u8,207#u8,175#u8,56#u8,10#u8,110#u8,239#u8,114#u8],by rfl⟩
def limbs20 : QM31Limbs := ![⟨191540860,by change 191540860<2147483647;omega⟩,⟨34283186,by change 34283186<2147483647;omega⟩,⟨951045940,by change 951045940<2147483647;omega⟩,⟨1928293898,by change 1928293898<2147483647;omega⟩]
theorem rawCell20 : (raw.drop 320).take 16=cell20.val := by
  simp only [raw,JFz_Scan49.data,JFz_Scan49.j00,JFz_Scan49.j01,JFz_Scan49.j02,JFz_Scan49.j03,JFz_Scan49.j04,JFz_Scan49.j05,JFz_Scan49.j06,JFz_Scan49.j07,JFz_Scan49.j08,JFz_Scan49.j09,JFz_Scan49.j10,JFz_Scan49.j11,JFz_Scan49.j12,JFz_Scan49.b00_length,JFz_Scan49.b01_length,JFz_Scan49.b02_length,JFz_Scan49.b03_length,JFz_Scan49.b04_length,JFz_Scan49.b05_length,JFz_Scan49.b06_length,JFz_Scan49.b07_length,JFz_Scan49.b08_length,JFz_Scan49.b09_length,JFz_Scan49.b10_length,JFz_Scan49.b11_length,JFz_Scan49.b12_length,JFz_Scan49.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell20
theorem encoded20 : CandidateParserByteOrder.arrayBytes16 cell20=encodeQM31LE limbs20 := by
  funext i
  fin_cases i <;> rfl
theorem parser20 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell20)=
    ok (some ⟨⟨191540860#u32,34283186#u32⟩,⟨951045940#u32,1928293898#u32⟩⟩) :=
  JFr_EncodedCell.parser cell20 limbs20 encoded20
#print axioms encoded20
#print axioms parser20
def cell21 : Array U8 16#usize := ⟨[219#u8,207#u8,49#u8,50#u8,68#u8,185#u8,188#u8,107#u8,167#u8,100#u8,142#u8,71#u8,241#u8,1#u8,107#u8,36#u8],by rfl⟩
def limbs21 : QM31Limbs := ![⟨842125275,by change 842125275<2147483647;omega⟩,⟨1807530308,by change 1807530308<2147483647;omega⟩,⟨1200514215,by change 1200514215<2147483647;omega⟩,⟨610992625,by change 610992625<2147483647;omega⟩]
theorem rawCell21 : (raw.drop 336).take 16=cell21.val := by
  simp only [raw,JFz_Scan49.data,JFz_Scan49.j00,JFz_Scan49.j01,JFz_Scan49.j02,JFz_Scan49.j03,JFz_Scan49.j04,JFz_Scan49.j05,JFz_Scan49.j06,JFz_Scan49.j07,JFz_Scan49.j08,JFz_Scan49.j09,JFz_Scan49.j10,JFz_Scan49.j11,JFz_Scan49.j12,JFz_Scan49.b00_length,JFz_Scan49.b01_length,JFz_Scan49.b02_length,JFz_Scan49.b03_length,JFz_Scan49.b04_length,JFz_Scan49.b05_length,JFz_Scan49.b06_length,JFz_Scan49.b07_length,JFz_Scan49.b08_length,JFz_Scan49.b09_length,JFz_Scan49.b10_length,JFz_Scan49.b11_length,JFz_Scan49.b12_length,JFz_Scan49.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell21
theorem encoded21 : CandidateParserByteOrder.arrayBytes16 cell21=encodeQM31LE limbs21 := by
  funext i
  fin_cases i <;> rfl
theorem parser21 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell21)=
    ok (some ⟨⟨842125275#u32,1807530308#u32⟩,⟨1200514215#u32,610992625#u32⟩⟩) :=
  JFr_EncodedCell.parser cell21 limbs21 encoded21
#print axioms encoded21
#print axioms parser21
def cell22 : Array U8 16#usize := ⟨[109#u8,113#u8,196#u8,90#u8,167#u8,18#u8,10#u8,59#u8,223#u8,150#u8,87#u8,122#u8,215#u8,76#u8,210#u8,25#u8],by rfl⟩
def limbs22 : QM31Limbs := ![⟨1522823533,by change 1522823533<2147483647;omega⟩,⟨990515879,by change 990515879<2147483647;omega⟩,⟨2052560607,by change 2052560607<2147483647;omega⟩,⟨433212631,by change 433212631<2147483647;omega⟩]
theorem rawCell22 : (raw.drop 352).take 16=cell22.val := by
  simp only [raw,JFz_Scan49.data,JFz_Scan49.j00,JFz_Scan49.j01,JFz_Scan49.j02,JFz_Scan49.j03,JFz_Scan49.j04,JFz_Scan49.j05,JFz_Scan49.j06,JFz_Scan49.j07,JFz_Scan49.j08,JFz_Scan49.j09,JFz_Scan49.j10,JFz_Scan49.j11,JFz_Scan49.j12,JFz_Scan49.b00_length,JFz_Scan49.b01_length,JFz_Scan49.b02_length,JFz_Scan49.b03_length,JFz_Scan49.b04_length,JFz_Scan49.b05_length,JFz_Scan49.b06_length,JFz_Scan49.b07_length,JFz_Scan49.b08_length,JFz_Scan49.b09_length,JFz_Scan49.b10_length,JFz_Scan49.b11_length,JFz_Scan49.b12_length,JFz_Scan49.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell22
theorem encoded22 : CandidateParserByteOrder.arrayBytes16 cell22=encodeQM31LE limbs22 := by
  funext i
  fin_cases i <;> rfl
theorem parser22 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell22)=
    ok (some ⟨⟨1522823533#u32,990515879#u32⟩,⟨2052560607#u32,433212631#u32⟩⟩) :=
  JFr_EncodedCell.parser cell22 limbs22 encoded22
#print axioms encoded22
#print axioms parser22
def cell23 : Array U8 16#usize := ⟨[183#u8,21#u8,188#u8,0#u8,215#u8,236#u8,36#u8,64#u8,122#u8,20#u8,167#u8,61#u8,237#u8,227#u8,187#u8,108#u8],by rfl⟩
def limbs23 : QM31Limbs := ![⟨12326327,by change 12326327<2147483647;omega⟩,⟨1076161751,by change 1076161751<2147483647;omega⟩,⟨1034359930,by change 1034359930<2147483647;omega⟩,⟨1824252909,by change 1824252909<2147483647;omega⟩]
theorem rawCell23 : (raw.drop 368).take 16=cell23.val := by
  simp only [raw,JFz_Scan49.data,JFz_Scan49.j00,JFz_Scan49.j01,JFz_Scan49.j02,JFz_Scan49.j03,JFz_Scan49.j04,JFz_Scan49.j05,JFz_Scan49.j06,JFz_Scan49.j07,JFz_Scan49.j08,JFz_Scan49.j09,JFz_Scan49.j10,JFz_Scan49.j11,JFz_Scan49.j12,JFz_Scan49.b00_length,JFz_Scan49.b01_length,JFz_Scan49.b02_length,JFz_Scan49.b03_length,JFz_Scan49.b04_length,JFz_Scan49.b05_length,JFz_Scan49.b06_length,JFz_Scan49.b07_length,JFz_Scan49.b08_length,JFz_Scan49.b09_length,JFz_Scan49.b10_length,JFz_Scan49.b11_length,JFz_Scan49.b12_length,JFz_Scan49.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell23
theorem encoded23 : CandidateParserByteOrder.arrayBytes16 cell23=encodeQM31LE limbs23 := by
  funext i
  fin_cases i <;> rfl
theorem parser23 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell23)=
    ok (some ⟨⟨12326327#u32,1076161751#u32⟩,⟨1034359930#u32,1824252909#u32⟩⟩) :=
  JFr_EncodedCell.parser cell23 limbs23 encoded23
#print axioms encoded23
#print axioms parser23
def cell24 : Array U8 16#usize := ⟨[152#u8,156#u8,139#u8,46#u8,184#u8,56#u8,228#u8,19#u8,141#u8,137#u8,15#u8,110#u8,203#u8,66#u8,203#u8,53#u8],by rfl⟩
def limbs24 : QM31Limbs := ![⟨780901528,by change 780901528<2147483647;omega⟩,⟨333723832,by change 333723832<2147483647;omega⟩,⟨1846512013,by change 1846512013<2147483647;omega⟩,⟨902513355,by change 902513355<2147483647;omega⟩]
theorem rawCell24 : (raw.drop 384).take 16=cell24.val := by
  simp only [raw,JFz_Scan49.data,JFz_Scan49.j00,JFz_Scan49.j01,JFz_Scan49.j02,JFz_Scan49.j03,JFz_Scan49.j04,JFz_Scan49.j05,JFz_Scan49.j06,JFz_Scan49.j07,JFz_Scan49.j08,JFz_Scan49.j09,JFz_Scan49.j10,JFz_Scan49.j11,JFz_Scan49.j12,JFz_Scan49.b00_length,JFz_Scan49.b01_length,JFz_Scan49.b02_length,JFz_Scan49.b03_length,JFz_Scan49.b04_length,JFz_Scan49.b05_length,JFz_Scan49.b06_length,JFz_Scan49.b07_length,JFz_Scan49.b08_length,JFz_Scan49.b09_length,JFz_Scan49.b10_length,JFz_Scan49.b11_length,JFz_Scan49.b12_length,JFz_Scan49.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell24
theorem encoded24 : CandidateParserByteOrder.arrayBytes16 cell24=encodeQM31LE limbs24 := by
  funext i
  fin_cases i <;> rfl
theorem parser24 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell24)=
    ok (some ⟨⟨780901528#u32,333723832#u32⟩,⟨1846512013#u32,902513355#u32⟩⟩) :=
  JFr_EncodedCell.parser cell24 limbs24 encoded24
#print axioms encoded24
#print axioms parser24
def cell25 : Array U8 16#usize := ⟨[165#u8,62#u8,34#u8,124#u8,159#u8,45#u8,160#u8,41#u8,38#u8,202#u8,211#u8,31#u8,139#u8,76#u8,196#u8,102#u8],by rfl⟩
def limbs25 : QM31Limbs := ![⟨2082619045,by change 2082619045<2147483647;omega⟩,⟨698363295,by change 698363295<2147483647;omega⟩,⟨533973542,by change 533973542<2147483647;omega⟩,⟨1724140683,by change 1724140683<2147483647;omega⟩]
theorem rawCell25 : (raw.drop 400).take 16=cell25.val := by
  simp only [raw,JFz_Scan49.data,JFz_Scan49.j00,JFz_Scan49.j01,JFz_Scan49.j02,JFz_Scan49.j03,JFz_Scan49.j04,JFz_Scan49.j05,JFz_Scan49.j06,JFz_Scan49.j07,JFz_Scan49.j08,JFz_Scan49.j09,JFz_Scan49.j10,JFz_Scan49.j11,JFz_Scan49.j12,JFz_Scan49.b00_length,JFz_Scan49.b01_length,JFz_Scan49.b02_length,JFz_Scan49.b03_length,JFz_Scan49.b04_length,JFz_Scan49.b05_length,JFz_Scan49.b06_length,JFz_Scan49.b07_length,JFz_Scan49.b08_length,JFz_Scan49.b09_length,JFz_Scan49.b10_length,JFz_Scan49.b11_length,JFz_Scan49.b12_length,JFz_Scan49.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell25
theorem encoded25 : CandidateParserByteOrder.arrayBytes16 cell25=encodeQM31LE limbs25 := by
  funext i
  fin_cases i <;> rfl
theorem parser25 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell25)=
    ok (some ⟨⟨2082619045#u32,698363295#u32⟩,⟨533973542#u32,1724140683#u32⟩⟩) :=
  JFr_EncodedCell.parser cell25 limbs25 encoded25
#print axioms encoded25
#print axioms parser25
def cell26 : Array U8 16#usize := ⟨[118#u8,253#u8,128#u8,91#u8,68#u8,116#u8,241#u8,80#u8,76#u8,244#u8,208#u8,5#u8,216#u8,81#u8,76#u8,122#u8],by rfl⟩
def limbs26 : QM31Limbs := ![⟨1535180150,by change 1535180150<2147483647;omega⟩,⟨1358001220,by change 1358001220<2147483647;omega⟩,⟨97580108,by change 97580108<2147483647;omega⟩,⟨2051822040,by change 2051822040<2147483647;omega⟩]
theorem rawCell26 : (raw.drop 416).take 16=cell26.val := by
  simp only [raw,JFz_Scan49.data,JFz_Scan49.j00,JFz_Scan49.j01,JFz_Scan49.j02,JFz_Scan49.j03,JFz_Scan49.j04,JFz_Scan49.j05,JFz_Scan49.j06,JFz_Scan49.j07,JFz_Scan49.j08,JFz_Scan49.j09,JFz_Scan49.j10,JFz_Scan49.j11,JFz_Scan49.j12,JFz_Scan49.b00_length,JFz_Scan49.b01_length,JFz_Scan49.b02_length,JFz_Scan49.b03_length,JFz_Scan49.b04_length,JFz_Scan49.b05_length,JFz_Scan49.b06_length,JFz_Scan49.b07_length,JFz_Scan49.b08_length,JFz_Scan49.b09_length,JFz_Scan49.b10_length,JFz_Scan49.b11_length,JFz_Scan49.b12_length,JFz_Scan49.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell26
theorem encoded26 : CandidateParserByteOrder.arrayBytes16 cell26=encodeQM31LE limbs26 := by
  funext i
  fin_cases i <;> rfl
theorem parser26 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell26)=
    ok (some ⟨⟨1535180150#u32,1358001220#u32⟩,⟨97580108#u32,2051822040#u32⟩⟩) :=
  JFr_EncodedCell.parser cell26 limbs26 encoded26
#print axioms encoded26
#print axioms parser26
def cell27 : Array U8 16#usize := ⟨[138#u8,68#u8,55#u8,53#u8,161#u8,147#u8,76#u8,14#u8,11#u8,142#u8,36#u8,44#u8,227#u8,8#u8,196#u8,0#u8],by rfl⟩
def limbs27 : QM31Limbs := ![⟨892814474,by change 892814474<2147483647;omega⟩,⟨239899553,by change 239899553<2147483647;omega⟩,⟨740593163,by change 740593163<2147483647;omega⟩,⟨12847331,by change 12847331<2147483647;omega⟩]
theorem rawCell27 : (raw.drop 432).take 16=cell27.val := by
  simp only [raw,JFz_Scan49.data,JFz_Scan49.j00,JFz_Scan49.j01,JFz_Scan49.j02,JFz_Scan49.j03,JFz_Scan49.j04,JFz_Scan49.j05,JFz_Scan49.j06,JFz_Scan49.j07,JFz_Scan49.j08,JFz_Scan49.j09,JFz_Scan49.j10,JFz_Scan49.j11,JFz_Scan49.j12,JFz_Scan49.b00_length,JFz_Scan49.b01_length,JFz_Scan49.b02_length,JFz_Scan49.b03_length,JFz_Scan49.b04_length,JFz_Scan49.b05_length,JFz_Scan49.b06_length,JFz_Scan49.b07_length,JFz_Scan49.b08_length,JFz_Scan49.b09_length,JFz_Scan49.b10_length,JFz_Scan49.b11_length,JFz_Scan49.b12_length,JFz_Scan49.b13_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms rawCell27
theorem encoded27 : CandidateParserByteOrder.arrayBytes16 cell27=encodeQM31LE limbs27 := by
  funext i
  fin_cases i <;> rfl
theorem parser27 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell27)=
    ok (some ⟨⟨892814474#u32,239899553#u32⟩,⟨740593163#u32,12847331#u32⟩⟩) :=
  JFr_EncodedCell.parser cell27 limbs27 encoded27
#print axioms encoded27
#print axioms parser27
end AspisR1.JFr_Bytes01
