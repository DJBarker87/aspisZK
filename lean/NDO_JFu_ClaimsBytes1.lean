import NDO_JFu_ClaimsData
set_option autoImplicit false
namespace AspisR1.JFu_ClaimsData
open Aeneas Aeneas.Std Result RetainedFieldByteCodec
open AspisR1PublicPreparation AspisS1ExtractedRoundChildren
open JFu_Q25Source.Input
def cell029 : Array U8 16#usize := ⟨[192#u8,139#u8,185#u8,40#u8,252#u8,253#u8,137#u8,66#u8,79#u8,83#u8,12#u8,34#u8,213#u8,1#u8,180#u8,1#u8],by rfl⟩
def limbs029 : QM31Limbs := ![⟨683248576,by change 683248576<2147483647;omega⟩,⟨1116339708,by change 1116339708<2147483647;omega⟩,⟨571233103,by change 571233103<2147483647;omega⟩,⟨28574165,by change 28574165<2147483647;omega⟩]
theorem window029 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*29)).take 16=cell029.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*29)).take 16=cell029.val
  rw [JFu_FlatWindow.source chunks lengths 29 (by change 29<116;omega)]
  rfl
#print axioms window029
theorem encoded029 : CandidateParserByteOrder.arrayBytes16 cell029=encodeQM31LE limbs029 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded029
theorem parser029 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell029)=
    ok (some ⟨⟨683248576#u32,1116339708#u32⟩,⟨571233103#u32,28574165#u32⟩⟩) := JFr_EncodedCell.parser cell029 limbs029 encoded029
#print axioms parser029
def cell030 : Array U8 16#usize := ⟨[179#u8,52#u8,236#u8,38#u8,120#u8,117#u8,229#u8,120#u8,109#u8,134#u8,196#u8,5#u8,246#u8,184#u8,68#u8,37#u8],by rfl⟩
def limbs030 : QM31Limbs := ![⟨653014195,by change 653014195<2147483647;omega⟩,⟨2028303736,by change 2028303736<2147483647;omega⟩,⟨96765549,by change 96765549<2147483647;omega⟩,⟨625260790,by change 625260790<2147483647;omega⟩]
theorem window030 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*30)).take 16=cell030.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*30)).take 16=cell030.val
  rw [JFu_FlatWindow.source chunks lengths 30 (by change 30<116;omega)]
  rfl
#print axioms window030
theorem encoded030 : CandidateParserByteOrder.arrayBytes16 cell030=encodeQM31LE limbs030 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded030
theorem parser030 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell030)=
    ok (some ⟨⟨653014195#u32,2028303736#u32⟩,⟨96765549#u32,625260790#u32⟩⟩) := JFr_EncodedCell.parser cell030 limbs030 encoded030
#print axioms parser030
def cell031 : Array U8 16#usize := ⟨[224#u8,233#u8,233#u8,117#u8,243#u8,129#u8,75#u8,22#u8,102#u8,67#u8,151#u8,61#u8,237#u8,150#u8,179#u8,72#u8],by rfl⟩
def limbs031 : QM31Limbs := ![⟨1978264032,by change 1978264032<2147483647;omega⟩,⟨374047219,by change 374047219<2147483647;omega⟩,⟨1033323366,by change 1033323366<2147483647;omega⟩,⟨1219729133,by change 1219729133<2147483647;omega⟩]
theorem window031 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*31)).take 16=cell031.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*31)).take 16=cell031.val
  rw [JFu_FlatWindow.source chunks lengths 31 (by change 31<116;omega)]
  rfl
#print axioms window031
theorem encoded031 : CandidateParserByteOrder.arrayBytes16 cell031=encodeQM31LE limbs031 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded031
theorem parser031 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell031)=
    ok (some ⟨⟨1978264032#u32,374047219#u32⟩,⟨1033323366#u32,1219729133#u32⟩⟩) := JFr_EncodedCell.parser cell031 limbs031 encoded031
#print axioms parser031
def cell032 : Array U8 16#usize := ⟨[229#u8,19#u8,227#u8,54#u8,115#u8,48#u8,133#u8,40#u8,146#u8,51#u8,159#u8,107#u8,140#u8,127#u8,199#u8,43#u8],by rfl⟩
def limbs032 : QM31Limbs := ![⟨920851429,by change 920851429<2147483647;omega⟩,⟨679817331,by change 679817331<2147483647;omega⟩,⟨1805595538,by change 1805595538<2147483647;omega⟩,⟨734494604,by change 734494604<2147483647;omega⟩]
theorem window032 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*32)).take 16=cell032.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*32)).take 16=cell032.val
  rw [JFu_FlatWindow.source chunks lengths 32 (by change 32<116;omega)]
  rfl
#print axioms window032
theorem encoded032 : CandidateParserByteOrder.arrayBytes16 cell032=encodeQM31LE limbs032 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded032
theorem parser032 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell032)=
    ok (some ⟨⟨920851429#u32,679817331#u32⟩,⟨1805595538#u32,734494604#u32⟩⟩) := JFr_EncodedCell.parser cell032 limbs032 encoded032
#print axioms parser032
def cell033 : Array U8 16#usize := ⟨[192#u8,136#u8,247#u8,125#u8,189#u8,158#u8,78#u8,2#u8,115#u8,98#u8,83#u8,10#u8,63#u8,214#u8,113#u8,93#u8],by rfl⟩
def limbs033 : QM31Limbs := ![⟨2113374400,by change 2113374400<2147483647;omega⟩,⟨38706877,by change 38706877<2147483647;omega⟩,⟨173236851,by change 173236851<2147483647;omega⟩,⟨1567741503,by change 1567741503<2147483647;omega⟩]
theorem window033 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*33)).take 16=cell033.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*33)).take 16=cell033.val
  rw [JFu_FlatWindow.source chunks lengths 33 (by change 33<116;omega)]
  rfl
#print axioms window033
theorem encoded033 : CandidateParserByteOrder.arrayBytes16 cell033=encodeQM31LE limbs033 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded033
theorem parser033 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell033)=
    ok (some ⟨⟨2113374400#u32,38706877#u32⟩,⟨173236851#u32,1567741503#u32⟩⟩) := JFr_EncodedCell.parser cell033 limbs033 encoded033
#print axioms parser033
def cell034 : Array U8 16#usize := ⟨[52#u8,162#u8,107#u8,86#u8,160#u8,251#u8,56#u8,122#u8,200#u8,151#u8,85#u8,88#u8,206#u8,97#u8,228#u8,16#u8],by rfl⟩
def limbs034 : QM31Limbs := ![⟨1449894452,by change 1449894452<2147483647;omega⟩,⟨2050554784,by change 2050554784<2147483647;omega⟩,⟨1482004424,by change 1482004424<2147483647;omega⟩,⟨283402702,by change 283402702<2147483647;omega⟩]
theorem window034 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*34)).take 16=cell034.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*34)).take 16=cell034.val
  rw [JFu_FlatWindow.source chunks lengths 34 (by change 34<116;omega)]
  rfl
#print axioms window034
theorem encoded034 : CandidateParserByteOrder.arrayBytes16 cell034=encodeQM31LE limbs034 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded034
theorem parser034 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell034)=
    ok (some ⟨⟨1449894452#u32,2050554784#u32⟩,⟨1482004424#u32,283402702#u32⟩⟩) := JFr_EncodedCell.parser cell034 limbs034 encoded034
#print axioms parser034
def cell035 : Array U8 16#usize := ⟨[71#u8,38#u8,211#u8,92#u8,241#u8,170#u8,21#u8,126#u8,247#u8,123#u8,94#u8,11#u8,103#u8,215#u8,48#u8,83#u8],by rfl⟩
def limbs035 : QM31Limbs := ![⟨1557341767,by change 1557341767<2147483647;omega⟩,⟨2115349233,by change 2115349233<2147483647;omega⟩,⟨190741495,by change 190741495<2147483647;omega⟩,⟨1395709799,by change 1395709799<2147483647;omega⟩]
theorem window035 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*35)).take 16=cell035.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*35)).take 16=cell035.val
  rw [JFu_FlatWindow.source chunks lengths 35 (by change 35<116;omega)]
  rfl
#print axioms window035
theorem encoded035 : CandidateParserByteOrder.arrayBytes16 cell035=encodeQM31LE limbs035 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded035
theorem parser035 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell035)=
    ok (some ⟨⟨1557341767#u32,2115349233#u32⟩,⟨190741495#u32,1395709799#u32⟩⟩) := JFr_EncodedCell.parser cell035 limbs035 encoded035
#print axioms parser035
def cell036 : Array U8 16#usize := ⟨[232#u8,55#u8,203#u8,58#u8,107#u8,55#u8,223#u8,82#u8,164#u8,46#u8,126#u8,13#u8,236#u8,48#u8,24#u8,118#u8],by rfl⟩
def limbs036 : QM31Limbs := ![⟨986396648,by change 986396648<2147483647;omega⟩,⟨1390360427,by change 1390360427<2147483647;omega⟩,⟨226373284,by change 226373284<2147483647;omega⟩,⟨1981296876,by change 1981296876<2147483647;omega⟩]
theorem window036 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*36)).take 16=cell036.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*36)).take 16=cell036.val
  rw [JFu_FlatWindow.source chunks lengths 36 (by change 36<116;omega)]
  rfl
#print axioms window036
theorem encoded036 : CandidateParserByteOrder.arrayBytes16 cell036=encodeQM31LE limbs036 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded036
theorem parser036 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell036)=
    ok (some ⟨⟨986396648#u32,1390360427#u32⟩,⟨226373284#u32,1981296876#u32⟩⟩) := JFr_EncodedCell.parser cell036 limbs036 encoded036
#print axioms parser036
def cell037 : Array U8 16#usize := ⟨[66#u8,254#u8,132#u8,28#u8,46#u8,22#u8,69#u8,5#u8,187#u8,173#u8,30#u8,60#u8,48#u8,224#u8,207#u8,114#u8],by rfl⟩
def limbs037 : QM31Limbs := ![⟨478477890,by change 478477890<2147483647;omega⟩,⟨88413742,by change 88413742<2147483647;omega⟩,⟨1008643515,by change 1008643515<2147483647;omega⟩,⟨1926225968,by change 1926225968<2147483647;omega⟩]
theorem window037 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*37)).take 16=cell037.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*37)).take 16=cell037.val
  rw [JFu_FlatWindow.source chunks lengths 37 (by change 37<116;omega)]
  rfl
#print axioms window037
theorem encoded037 : CandidateParserByteOrder.arrayBytes16 cell037=encodeQM31LE limbs037 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded037
theorem parser037 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell037)=
    ok (some ⟨⟨478477890#u32,88413742#u32⟩,⟨1008643515#u32,1926225968#u32⟩⟩) := JFr_EncodedCell.parser cell037 limbs037 encoded037
#print axioms parser037
def cell038 : Array U8 16#usize := ⟨[87#u8,66#u8,237#u8,89#u8,246#u8,215#u8,183#u8,31#u8,29#u8,213#u8,146#u8,29#u8,170#u8,223#u8,164#u8,63#u8],by rfl⟩
def limbs038 : QM31Limbs := ![⟨1508721239,by change 1508721239<2147483647;omega⟩,⟨532142070,by change 532142070<2147483647;omega⟩,⟨496162077,by change 496162077<2147483647;omega⟩,⟨1067769770,by change 1067769770<2147483647;omega⟩]
theorem window038 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*38)).take 16=cell038.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*38)).take 16=cell038.val
  rw [JFu_FlatWindow.source chunks lengths 38 (by change 38<116;omega)]
  rfl
#print axioms window038
theorem encoded038 : CandidateParserByteOrder.arrayBytes16 cell038=encodeQM31LE limbs038 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded038
theorem parser038 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell038)=
    ok (some ⟨⟨1508721239#u32,532142070#u32⟩,⟨496162077#u32,1067769770#u32⟩⟩) := JFr_EncodedCell.parser cell038 limbs038 encoded038
#print axioms parser038
def cell039 : Array U8 16#usize := ⟨[246#u8,167#u8,74#u8,73#u8,182#u8,250#u8,119#u8,25#u8,229#u8,31#u8,201#u8,27#u8,27#u8,199#u8,237#u8,89#u8],by rfl⟩
def limbs039 : QM31Limbs := ![⟨1229629430,by change 1229629430<2147483647;omega⟩,⟨427293366,by change 427293366<2147483647;omega⟩,⟨466165733,by change 466165733<2147483647;omega⟩,⟨1508755227,by change 1508755227<2147483647;omega⟩]
theorem window039 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*39)).take 16=cell039.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*39)).take 16=cell039.val
  rw [JFu_FlatWindow.source chunks lengths 39 (by change 39<116;omega)]
  rfl
#print axioms window039
theorem encoded039 : CandidateParserByteOrder.arrayBytes16 cell039=encodeQM31LE limbs039 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded039
theorem parser039 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell039)=
    ok (some ⟨⟨1229629430#u32,427293366#u32⟩,⟨466165733#u32,1508755227#u32⟩⟩) := JFr_EncodedCell.parser cell039 limbs039 encoded039
#print axioms parser039
def cell040 : Array U8 16#usize := ⟨[166#u8,144#u8,46#u8,74#u8,7#u8,198#u8,226#u8,120#u8,220#u8,152#u8,114#u8,87#u8,67#u8,17#u8,82#u8,16#u8],by rfl⟩
def limbs040 : QM31Limbs := ![⟨1244565670,by change 1244565670<2147483647;omega⟩,⟨2028127751,by change 2028127751<2147483647;omega⟩,⟨1467128028,by change 1467128028<2147483647;omega⟩,⟨273813827,by change 273813827<2147483647;omega⟩]
theorem window040 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*40)).take 16=cell040.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*40)).take 16=cell040.val
  rw [JFu_FlatWindow.source chunks lengths 40 (by change 40<116;omega)]
  rfl
#print axioms window040
theorem encoded040 : CandidateParserByteOrder.arrayBytes16 cell040=encodeQM31LE limbs040 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded040
theorem parser040 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell040)=
    ok (some ⟨⟨1244565670#u32,2028127751#u32⟩,⟨1467128028#u32,273813827#u32⟩⟩) := JFr_EncodedCell.parser cell040 limbs040 encoded040
#print axioms parser040
def cell041 : Array U8 16#usize := ⟨[35#u8,226#u8,232#u8,6#u8,225#u8,14#u8,39#u8,111#u8,31#u8,183#u8,122#u8,17#u8,124#u8,210#u8,82#u8,45#u8],by rfl⟩
def limbs041 : QM31Limbs := ![⟨115925539,by change 115925539<2147483647;omega⟩,⟨1864830689,by change 1864830689<2147483647;omega⟩,⟨293254943,by change 293254943<2147483647;omega⟩,⟨760402556,by change 760402556<2147483647;omega⟩]
theorem window041 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*41)).take 16=cell041.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*41)).take 16=cell041.val
  rw [JFu_FlatWindow.source chunks lengths 41 (by change 41<116;omega)]
  rfl
#print axioms window041
theorem encoded041 : CandidateParserByteOrder.arrayBytes16 cell041=encodeQM31LE limbs041 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded041
theorem parser041 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell041)=
    ok (some ⟨⟨115925539#u32,1864830689#u32⟩,⟨293254943#u32,760402556#u32⟩⟩) := JFr_EncodedCell.parser cell041 limbs041 encoded041
#print axioms parser041
def cell042 : Array U8 16#usize := ⟨[172#u8,30#u8,217#u8,18#u8,40#u8,103#u8,11#u8,5#u8,53#u8,72#u8,197#u8,78#u8,168#u8,158#u8,249#u8,70#u8],by rfl⟩
def limbs042 : QM31Limbs := ![⟨316219052,by change 316219052<2147483647;omega⟩,⟨84633384,by change 84633384<2147483647;omega⟩,⟨1321551925,by change 1321551925<2147483647;omega⟩,⟨1190764200,by change 1190764200<2147483647;omega⟩]
theorem window042 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*42)).take 16=cell042.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*42)).take 16=cell042.val
  rw [JFu_FlatWindow.source chunks lengths 42 (by change 42<116;omega)]
  rfl
#print axioms window042
theorem encoded042 : CandidateParserByteOrder.arrayBytes16 cell042=encodeQM31LE limbs042 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded042
theorem parser042 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell042)=
    ok (some ⟨⟨316219052#u32,84633384#u32⟩,⟨1321551925#u32,1190764200#u32⟩⟩) := JFr_EncodedCell.parser cell042 limbs042 encoded042
#print axioms parser042
def cell043 : Array U8 16#usize := ⟨[122#u8,148#u8,93#u8,17#u8,100#u8,240#u8,182#u8,95#u8,4#u8,132#u8,56#u8,114#u8,84#u8,75#u8,182#u8,127#u8],by rfl⟩
def limbs043 : QM31Limbs := ![⟨291345530,by change 291345530<2147483647;omega⟩,⟨1605824612,by change 1605824612<2147483647;omega⟩,⟨1916306436,by change 1916306436<2147483647;omega⟩,⟨2142653268,by change 2142653268<2147483647;omega⟩]
theorem window043 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*43)).take 16=cell043.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*43)).take 16=cell043.val
  rw [JFu_FlatWindow.source chunks lengths 43 (by change 43<116;omega)]
  rfl
#print axioms window043
theorem encoded043 : CandidateParserByteOrder.arrayBytes16 cell043=encodeQM31LE limbs043 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded043
theorem parser043 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell043)=
    ok (some ⟨⟨291345530#u32,1605824612#u32⟩,⟨1916306436#u32,2142653268#u32⟩⟩) := JFr_EncodedCell.parser cell043 limbs043 encoded043
#print axioms parser043
def cell044 : Array U8 16#usize := ⟨[52#u8,92#u8,46#u8,54#u8,34#u8,45#u8,27#u8,105#u8,44#u8,123#u8,150#u8,23#u8,44#u8,59#u8,203#u8,79#u8],by rfl⟩
def limbs044 : QM31Limbs := ![⟨909007924,by change 909007924<2147483647;omega⟩,⟨1763388706,by change 1763388706<2147483647;omega⟩,⟨395737900,by change 395737900<2147483647;omega⟩,⟨1338719020,by change 1338719020<2147483647;omega⟩]
theorem window044 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*44)).take 16=cell044.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*44)).take 16=cell044.val
  rw [JFu_FlatWindow.source chunks lengths 44 (by change 44<116;omega)]
  rfl
#print axioms window044
theorem encoded044 : CandidateParserByteOrder.arrayBytes16 cell044=encodeQM31LE limbs044 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded044
theorem parser044 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell044)=
    ok (some ⟨⟨909007924#u32,1763388706#u32⟩,⟨395737900#u32,1338719020#u32⟩⟩) := JFr_EncodedCell.parser cell044 limbs044 encoded044
#print axioms parser044
def cell045 : Array U8 16#usize := ⟨[233#u8,145#u8,26#u8,53#u8,9#u8,216#u8,237#u8,15#u8,152#u8,229#u8,154#u8,52#u8,235#u8,3#u8,145#u8,82#u8],by rfl⟩
def limbs045 : QM31Limbs := ![⟨890933737,by change 890933737<2147483647;omega⟩,⟨267245577,by change 267245577<2147483647;omega⟩,⟨882566552,by change 882566552<2147483647;omega⟩,⟨1385235435,by change 1385235435<2147483647;omega⟩]
theorem window045 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*45)).take 16=cell045.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*45)).take 16=cell045.val
  rw [JFu_FlatWindow.source chunks lengths 45 (by change 45<116;omega)]
  rfl
#print axioms window045
theorem encoded045 : CandidateParserByteOrder.arrayBytes16 cell045=encodeQM31LE limbs045 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded045
theorem parser045 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell045)=
    ok (some ⟨⟨890933737#u32,267245577#u32⟩,⟨882566552#u32,1385235435#u32⟩⟩) := JFr_EncodedCell.parser cell045 limbs045 encoded045
#print axioms parser045
def cell046 : Array U8 16#usize := ⟨[6#u8,29#u8,250#u8,92#u8,79#u8,187#u8,210#u8,55#u8,231#u8,99#u8,180#u8,57#u8,246#u8,100#u8,150#u8,66#u8],by rfl⟩
def limbs046 : QM31Limbs := ![⟨1559895302,by change 1559895302<2147483647;omega⟩,⟨936557391,by change 936557391<2147483647;omega⟩,⟨968123367,by change 968123367<2147483647;omega⟩,⟨1117152502,by change 1117152502<2147483647;omega⟩]
theorem window046 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*46)).take 16=cell046.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*46)).take 16=cell046.val
  rw [JFu_FlatWindow.source chunks lengths 46 (by change 46<116;omega)]
  rfl
#print axioms window046
theorem encoded046 : CandidateParserByteOrder.arrayBytes16 cell046=encodeQM31LE limbs046 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded046
theorem parser046 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell046)=
    ok (some ⟨⟨1559895302#u32,936557391#u32⟩,⟨968123367#u32,1117152502#u32⟩⟩) := JFr_EncodedCell.parser cell046 limbs046 encoded046
#print axioms parser046
def cell047 : Array U8 16#usize := ⟨[31#u8,70#u8,153#u8,64#u8,194#u8,151#u8,34#u8,34#u8,170#u8,229#u8,174#u8,82#u8,17#u8,254#u8,14#u8,85#u8],by rfl⟩
def limbs047 : QM31Limbs := ![⟨1083786783,by change 1083786783<2147483647;omega⟩,⟨572692418,by change 572692418<2147483647;omega⟩,⟨1387193770,by change 1387193770<2147483647;omega⟩,⟨1427045905,by change 1427045905<2147483647;omega⟩]
theorem window047 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*47)).take 16=cell047.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*47)).take 16=cell047.val
  rw [JFu_FlatWindow.source chunks lengths 47 (by change 47<116;omega)]
  rfl
#print axioms window047
theorem encoded047 : CandidateParserByteOrder.arrayBytes16 cell047=encodeQM31LE limbs047 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded047
theorem parser047 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell047)=
    ok (some ⟨⟨1083786783#u32,572692418#u32⟩,⟨1387193770#u32,1427045905#u32⟩⟩) := JFr_EncodedCell.parser cell047 limbs047 encoded047
#print axioms parser047
def cell048 : Array U8 16#usize := ⟨[153#u8,23#u8,212#u8,52#u8,35#u8,249#u8,42#u8,9#u8,89#u8,31#u8,41#u8,21#u8,247#u8,13#u8,216#u8,65#u8],by rfl⟩
def limbs048 : QM31Limbs := ![⟨886314905,by change 886314905<2147483647;omega⟩,⟨153811235,by change 153811235<2147483647;omega⟩,⟨355016537,by change 355016537<2147483647;omega⟩,⟨1104678391,by change 1104678391<2147483647;omega⟩]
theorem window048 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*48)).take 16=cell048.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*48)).take 16=cell048.val
  rw [JFu_FlatWindow.source chunks lengths 48 (by change 48<116;omega)]
  rfl
#print axioms window048
theorem encoded048 : CandidateParserByteOrder.arrayBytes16 cell048=encodeQM31LE limbs048 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded048
theorem parser048 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell048)=
    ok (some ⟨⟨886314905#u32,153811235#u32⟩,⟨355016537#u32,1104678391#u32⟩⟩) := JFr_EncodedCell.parser cell048 limbs048 encoded048
#print axioms parser048
def cell049 : Array U8 16#usize := ⟨[4#u8,217#u8,251#u8,112#u8,78#u8,92#u8,105#u8,26#u8,169#u8,163#u8,49#u8,123#u8,210#u8,96#u8,8#u8,22#u8],by rfl⟩
def limbs049 : QM31Limbs := ![⟨1895553284,by change 1895553284<2147483647;omega⟩,⟨443112526,by change 443112526<2147483647;omega⟩,⟨2066850729,by change 2066850729<2147483647;omega⟩,⟨369647826,by change 369647826<2147483647;omega⟩]
theorem window049 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*49)).take 16=cell049.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*49)).take 16=cell049.val
  rw [JFu_FlatWindow.source chunks lengths 49 (by change 49<116;omega)]
  rfl
#print axioms window049
theorem encoded049 : CandidateParserByteOrder.arrayBytes16 cell049=encodeQM31LE limbs049 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded049
theorem parser049 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell049)=
    ok (some ⟨⟨1895553284#u32,443112526#u32⟩,⟨2066850729#u32,369647826#u32⟩⟩) := JFr_EncodedCell.parser cell049 limbs049 encoded049
#print axioms parser049
def cell050 : Array U8 16#usize := ⟨[64#u8,137#u8,62#u8,34#u8,94#u8,71#u8,124#u8,123#u8,6#u8,68#u8,104#u8,39#u8,51#u8,61#u8,189#u8,123#u8],by rfl⟩
def limbs050 : QM31Limbs := ![⟨574523712,by change 574523712<2147483647;omega⟩,⟨2071742302,by change 2071742302<2147483647;omega⟩,⟨661144582,by change 661144582<2147483647;omega⟩,⟨2075999539,by change 2075999539<2147483647;omega⟩]
theorem window050 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*50)).take 16=cell050.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*50)).take 16=cell050.val
  rw [JFu_FlatWindow.source chunks lengths 50 (by change 50<116;omega)]
  rfl
#print axioms window050
theorem encoded050 : CandidateParserByteOrder.arrayBytes16 cell050=encodeQM31LE limbs050 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded050
theorem parser050 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell050)=
    ok (some ⟨⟨574523712#u32,2071742302#u32⟩,⟨661144582#u32,2075999539#u32⟩⟩) := JFr_EncodedCell.parser cell050 limbs050 encoded050
#print axioms parser050
def cell051 : Array U8 16#usize := ⟨[251#u8,179#u8,55#u8,93#u8,155#u8,194#u8,179#u8,61#u8,114#u8,21#u8,223#u8,8#u8,135#u8,251#u8,61#u8,96#u8],by rfl⟩
def limbs051 : QM31Limbs := ![⟨1563931643,by change 1563931643<2147483647;omega⟩,⟨1035190939,by change 1035190939<2147483647;omega⟩,⟨148837746,by change 148837746<2147483647;omega⟩,⟨1614674823,by change 1614674823<2147483647;omega⟩]
theorem window051 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*51)).take 16=cell051.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*51)).take 16=cell051.val
  rw [JFu_FlatWindow.source chunks lengths 51 (by change 51<116;omega)]
  rfl
#print axioms window051
theorem encoded051 : CandidateParserByteOrder.arrayBytes16 cell051=encodeQM31LE limbs051 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded051
theorem parser051 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell051)=
    ok (some ⟨⟨1563931643#u32,1035190939#u32⟩,⟨148837746#u32,1614674823#u32⟩⟩) := JFr_EncodedCell.parser cell051 limbs051 encoded051
#print axioms parser051
def cell052 : Array U8 16#usize := ⟨[155#u8,167#u8,233#u8,18#u8,4#u8,78#u8,11#u8,104#u8,193#u8,222#u8,23#u8,25#u8,107#u8,105#u8,120#u8,12#u8],by rfl⟩
def limbs052 : QM31Limbs := ![⟨317302683,by change 317302683<2147483647;omega⟩,⟨1745571332,by change 1745571332<2147483647;omega⟩,⟨420994753,by change 420994753<2147483647;omega⟩,⟨209217899,by change 209217899<2147483647;omega⟩]
theorem window052 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*52)).take 16=cell052.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*52)).take 16=cell052.val
  rw [JFu_FlatWindow.source chunks lengths 52 (by change 52<116;omega)]
  rfl
#print axioms window052
theorem encoded052 : CandidateParserByteOrder.arrayBytes16 cell052=encodeQM31LE limbs052 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded052
theorem parser052 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell052)=
    ok (some ⟨⟨317302683#u32,1745571332#u32⟩,⟨420994753#u32,209217899#u32⟩⟩) := JFr_EncodedCell.parser cell052 limbs052 encoded052
#print axioms parser052
def cell053 : Array U8 16#usize := ⟨[120#u8,189#u8,118#u8,5#u8,72#u8,22#u8,177#u8,88#u8,128#u8,181#u8,31#u8,15#u8,87#u8,229#u8,104#u8,75#u8],by rfl⟩
def limbs053 : QM31Limbs := ![⟨91667832,by change 91667832<2147483647;omega⟩,⟨1488000584,by change 1488000584<2147483647;omega⟩,⟨253736320,by change 253736320<2147483647;omega⟩,⟨1265165655,by change 1265165655<2147483647;omega⟩]
theorem window053 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*53)).take 16=cell053.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*53)).take 16=cell053.val
  rw [JFu_FlatWindow.source chunks lengths 53 (by change 53<116;omega)]
  rfl
#print axioms window053
theorem encoded053 : CandidateParserByteOrder.arrayBytes16 cell053=encodeQM31LE limbs053 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded053
theorem parser053 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell053)=
    ok (some ⟨⟨91667832#u32,1488000584#u32⟩,⟨253736320#u32,1265165655#u32⟩⟩) := JFr_EncodedCell.parser cell053 limbs053 encoded053
#print axioms parser053
def cell054 : Array U8 16#usize := ⟨[114#u8,10#u8,49#u8,2#u8,53#u8,76#u8,26#u8,20#u8,110#u8,114#u8,107#u8,26#u8,169#u8,192#u8,42#u8,75#u8],by rfl⟩
def limbs054 : QM31Limbs := ![⟨36768370,by change 36768370<2147483647;omega⟩,⟨337267765,by change 337267765<2147483647;omega⟩,⟨443249262,by change 443249262<2147483647;omega⟩,⟨1261093033,by change 1261093033<2147483647;omega⟩]
theorem window054 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*54)).take 16=cell054.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*54)).take 16=cell054.val
  rw [JFu_FlatWindow.source chunks lengths 54 (by change 54<116;omega)]
  rfl
#print axioms window054
theorem encoded054 : CandidateParserByteOrder.arrayBytes16 cell054=encodeQM31LE limbs054 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded054
theorem parser054 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell054)=
    ok (some ⟨⟨36768370#u32,337267765#u32⟩,⟨443249262#u32,1261093033#u32⟩⟩) := JFr_EncodedCell.parser cell054 limbs054 encoded054
#print axioms parser054
def cell055 : Array U8 16#usize := ⟨[49#u8,114#u8,140#u8,41#u8,187#u8,158#u8,62#u8,4#u8,138#u8,73#u8,44#u8,55#u8,14#u8,35#u8,246#u8,0#u8],by rfl⟩
def limbs055 : QM31Limbs := ![⟨697070129,by change 697070129<2147483647;omega⟩,⟨71212731,by change 71212731<2147483647;omega⟩,⟨925649290,by change 925649290<2147483647;omega⟩,⟨16130830,by change 16130830<2147483647;omega⟩]
theorem window055 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*55)).take 16=cell055.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*55)).take 16=cell055.val
  rw [JFu_FlatWindow.source chunks lengths 55 (by change 55<116;omega)]
  rfl
#print axioms window055
theorem encoded055 : CandidateParserByteOrder.arrayBytes16 cell055=encodeQM31LE limbs055 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded055
theorem parser055 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell055)=
    ok (some ⟨⟨697070129#u32,71212731#u32⟩,⟨925649290#u32,16130830#u32⟩⟩) := JFr_EncodedCell.parser cell055 limbs055 encoded055
#print axioms parser055
def cell056 : Array U8 16#usize := ⟨[22#u8,172#u8,206#u8,86#u8,159#u8,96#u8,148#u8,6#u8,22#u8,65#u8,102#u8,56#u8,34#u8,194#u8,217#u8,115#u8],by rfl⟩
def limbs056 : QM31Limbs := ![⟨1456385046,by change 1456385046<2147483647;omega⟩,⟨110387359,by change 110387359<2147483647;omega⟩,⟨946225430,by change 946225430<2147483647;omega⟩,⟨1943650850,by change 1943650850<2147483647;omega⟩]
theorem window056 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*56)).take 16=cell056.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*56)).take 16=cell056.val
  rw [JFu_FlatWindow.source chunks lengths 56 (by change 56<116;omega)]
  rfl
#print axioms window056
theorem encoded056 : CandidateParserByteOrder.arrayBytes16 cell056=encodeQM31LE limbs056 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded056
theorem parser056 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell056)=
    ok (some ⟨⟨1456385046#u32,110387359#u32⟩,⟨946225430#u32,1943650850#u32⟩⟩) := JFr_EncodedCell.parser cell056 limbs056 encoded056
#print axioms parser056
def cell057 : Array U8 16#usize := ⟨[76#u8,30#u8,192#u8,48#u8,58#u8,218#u8,182#u8,39#u8,131#u8,70#u8,226#u8,16#u8,178#u8,29#u8,113#u8,30#u8],by rfl⟩
def limbs057 : QM31Limbs := ![⟨817897036,by change 817897036<2147483647;omega⟩,⟨666294842,by change 666294842<2147483647;omega⟩,⟨283264643,by change 283264643<2147483647;omega⟩,⟨510729650,by change 510729650<2147483647;omega⟩]
theorem window057 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*57)).take 16=cell057.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*57)).take 16=cell057.val
  rw [JFu_FlatWindow.source chunks lengths 57 (by change 57<116;omega)]
  rfl
#print axioms window057
theorem encoded057 : CandidateParserByteOrder.arrayBytes16 cell057=encodeQM31LE limbs057 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded057
theorem parser057 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell057)=
    ok (some ⟨⟨817897036#u32,666294842#u32⟩,⟨283264643#u32,510729650#u32⟩⟩) := JFr_EncodedCell.parser cell057 limbs057 encoded057
#print axioms parser057
end AspisR1.JFu_ClaimsData
