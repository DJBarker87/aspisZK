import NDO_JFu_ClaimsData
set_option autoImplicit false
namespace AspisR1.JFu_ClaimsData
open Aeneas Aeneas.Std Result RetainedFieldByteCodec
open AspisR1PublicPreparation AspisS1ExtractedRoundChildren
open JFu_Q25Source.Input
def cell029 : Array U8 16#usize := ⟨[207#u8,182#u8,99#u8,85#u8,57#u8,60#u8,110#u8,44#u8,77#u8,241#u8,247#u8,67#u8,143#u8,113#u8,187#u8,87#u8],by rfl⟩
def limbs029 : QM31Limbs := ![⟨1432598223,by change 1432598223<2147483647;omega⟩,⟨745421881,by change 745421881<2147483647;omega⟩,⟨1140322637,by change 1140322637<2147483647;omega⟩,⟨1471902095,by change 1471902095<2147483647;omega⟩]
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
    ok (some ⟨⟨1432598223#u32,745421881#u32⟩,⟨1140322637#u32,1471902095#u32⟩⟩) := JFr_EncodedCell.parser cell029 limbs029 encoded029
#print axioms parser029
def cell030 : Array U8 16#usize := ⟨[250#u8,50#u8,171#u8,118#u8,98#u8,155#u8,46#u8,92#u8,198#u8,69#u8,157#u8,16#u8,251#u8,159#u8,248#u8,37#u8],by rfl⟩
def limbs030 : QM31Limbs := ![⟨1990931194,by change 1990931194<2147483647;omega⟩,⟨1546558306,by change 1546558306<2147483647;omega⟩,⟨278742470,by change 278742470<2147483647;omega⟩,⟨637050875,by change 637050875<2147483647;omega⟩]
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
    ok (some ⟨⟨1990931194#u32,1546558306#u32⟩,⟨278742470#u32,637050875#u32⟩⟩) := JFr_EncodedCell.parser cell030 limbs030 encoded030
#print axioms parser030
def cell031 : Array U8 16#usize := ⟨[144#u8,100#u8,24#u8,91#u8,171#u8,196#u8,102#u8,49#u8,55#u8,48#u8,31#u8,114#u8,64#u8,173#u8,145#u8,63#u8],by rfl⟩
def limbs031 : QM31Limbs := ![⟨1528325264,by change 1528325264<2147483647;omega⟩,⟨828818603,by change 828818603<2147483647;omega⟩,⟨1914646583,by change 1914646583<2147483647;omega⟩,⟨1066511680,by change 1066511680<2147483647;omega⟩]
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
    ok (some ⟨⟨1528325264#u32,828818603#u32⟩,⟨1914646583#u32,1066511680#u32⟩⟩) := JFr_EncodedCell.parser cell031 limbs031 encoded031
#print axioms parser031
def cell032 : Array U8 16#usize := ⟨[135#u8,164#u8,150#u8,3#u8,254#u8,28#u8,186#u8,23#u8,180#u8,255#u8,172#u8,90#u8,13#u8,12#u8,248#u8,105#u8],by rfl⟩
def limbs032 : QM31Limbs := ![⟨60204167,by change 60204167<2147483647;omega⟩,⟨398073086,by change 398073086<2147483647;omega⟩,⟨1521287092,by change 1521287092<2147483647;omega⟩,⟨1777863693,by change 1777863693<2147483647;omega⟩]
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
    ok (some ⟨⟨60204167#u32,398073086#u32⟩,⟨1521287092#u32,1777863693#u32⟩⟩) := JFr_EncodedCell.parser cell032 limbs032 encoded032
#print axioms parser032
def cell033 : Array U8 16#usize := ⟨[251#u8,193#u8,202#u8,31#u8,177#u8,21#u8,185#u8,33#u8,223#u8,6#u8,108#u8,46#u8,51#u8,41#u8,97#u8,37#u8],by rfl⟩
def limbs033 : QM31Limbs := ![⟨533381627,by change 533381627<2147483647;omega⟩,⟨565777841,by change 565777841<2147483647;omega⟩,⟨778831583,by change 778831583<2147483647;omega⟩,⟨627124531,by change 627124531<2147483647;omega⟩]
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
    ok (some ⟨⟨533381627#u32,565777841#u32⟩,⟨778831583#u32,627124531#u32⟩⟩) := JFr_EncodedCell.parser cell033 limbs033 encoded033
#print axioms parser033
def cell034 : Array U8 16#usize := ⟨[90#u8,252#u8,157#u8,97#u8,96#u8,204#u8,187#u8,110#u8,110#u8,17#u8,10#u8,89#u8,97#u8,29#u8,10#u8,96#u8],by rfl⟩
def limbs034 : QM31Limbs := ![⟨1637743706,by change 1637743706<2147483647;omega⟩,⟨1857801312,by change 1857801312<2147483647;omega⟩,⟨1493832046,by change 1493832046<2147483647;omega⟩,⟨1611275617,by change 1611275617<2147483647;omega⟩]
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
    ok (some ⟨⟨1637743706#u32,1857801312#u32⟩,⟨1493832046#u32,1611275617#u32⟩⟩) := JFr_EncodedCell.parser cell034 limbs034 encoded034
#print axioms parser034
def cell035 : Array U8 16#usize := ⟨[147#u8,89#u8,36#u8,71#u8,85#u8,8#u8,156#u8,115#u8,201#u8,82#u8,218#u8,38#u8,175#u8,254#u8,98#u8,46#u8],by rfl⟩
def limbs035 : QM31Limbs := ![⟨1193564563,by change 1193564563<2147483647;omega⟩,⟨1939605589,by change 1939605589<2147483647;omega⟩,⟨651842249,by change 651842249<2147483647;omega⟩,⟨778239663,by change 778239663<2147483647;omega⟩]
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
    ok (some ⟨⟨1193564563#u32,1939605589#u32⟩,⟨651842249#u32,778239663#u32⟩⟩) := JFr_EncodedCell.parser cell035 limbs035 encoded035
#print axioms parser035
def cell036 : Array U8 16#usize := ⟨[19#u8,67#u8,200#u8,46#u8,101#u8,46#u8,93#u8,52#u8,13#u8,139#u8,105#u8,25#u8,63#u8,172#u8,109#u8,103#u8],by rfl⟩
def limbs036 : QM31Limbs := ![⟨784876307,by change 784876307<2147483647;omega⟩,⟨878521957,by change 878521957<2147483647;omega⟩,⟨426347277,by change 426347277<2147483647;omega⟩,⟨1735240767,by change 1735240767<2147483647;omega⟩]
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
    ok (some ⟨⟨784876307#u32,878521957#u32⟩,⟨426347277#u32,1735240767#u32⟩⟩) := JFr_EncodedCell.parser cell036 limbs036 encoded036
#print axioms parser036
def cell037 : Array U8 16#usize := ⟨[60#u8,55#u8,238#u8,31#u8,41#u8,40#u8,255#u8,100#u8,194#u8,95#u8,34#u8,22#u8,132#u8,194#u8,147#u8,95#u8],by rfl⟩
def limbs037 : QM31Limbs := ![⟨535705404,by change 535705404<2147483647;omega⟩,⟨1694443561,by change 1694443561<2147483647;omega⟩,⟨371351490,by change 371351490<2147483647;omega⟩,⟨1603519108,by change 1603519108<2147483647;omega⟩]
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
    ok (some ⟨⟨535705404#u32,1694443561#u32⟩,⟨371351490#u32,1603519108#u32⟩⟩) := JFr_EncodedCell.parser cell037 limbs037 encoded037
#print axioms parser037
def cell038 : Array U8 16#usize := ⟨[216#u8,250#u8,213#u8,105#u8,210#u8,139#u8,29#u8,22#u8,166#u8,81#u8,125#u8,111#u8,255#u8,177#u8,164#u8,60#u8],by rfl⟩
def limbs038 : QM31Limbs := ![⟨1775631064,by change 1775631064<2147483647;omega⟩,⟨371035090,by change 371035090<2147483647;omega⟩,⟨1870483878,by change 1870483878<2147483647;omega⟩,⟨1017426431,by change 1017426431<2147483647;omega⟩]
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
    ok (some ⟨⟨1775631064#u32,371035090#u32⟩,⟨1870483878#u32,1017426431#u32⟩⟩) := JFr_EncodedCell.parser cell038 limbs038 encoded038
#print axioms parser038
def cell039 : Array U8 16#usize := ⟨[36#u8,239#u8,191#u8,100#u8,149#u8,137#u8,80#u8,24#u8,166#u8,16#u8,14#u8,73#u8,54#u8,211#u8,116#u8,113#u8],by rfl⟩
def limbs039 : QM31Limbs := ![⟨1690300196,by change 1690300196<2147483647;omega⟩,⟨407931285,by change 407931285<2147483647;omega⟩,⟨1225658534,by change 1225658534<2147483647;omega⟩,⟨1903481654,by change 1903481654<2147483647;omega⟩]
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
    ok (some ⟨⟨1690300196#u32,407931285#u32⟩,⟨1225658534#u32,1903481654#u32⟩⟩) := JFr_EncodedCell.parser cell039 limbs039 encoded039
#print axioms parser039
def cell040 : Array U8 16#usize := ⟨[181#u8,177#u8,101#u8,23#u8,78#u8,193#u8,78#u8,59#u8,53#u8,42#u8,195#u8,80#u8,12#u8,243#u8,110#u8,81#u8],by rfl⟩
def limbs040 : QM31Limbs := ![⟨392540597,by change 392540597<2147483647;omega⟩,⟨995017038,by change 995017038<2147483647;omega⟩,⟨1354967605,by change 1354967605<2147483647;omega⟩,⟨1366225676,by change 1366225676<2147483647;omega⟩]
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
    ok (some ⟨⟨392540597#u32,995017038#u32⟩,⟨1354967605#u32,1366225676#u32⟩⟩) := JFr_EncodedCell.parser cell040 limbs040 encoded040
#print axioms parser040
def cell041 : Array U8 16#usize := ⟨[172#u8,95#u8,78#u8,97#u8,29#u8,237#u8,173#u8,75#u8,24#u8,30#u8,1#u8,65#u8,164#u8,77#u8,4#u8,25#u8],by rfl⟩
def limbs041 : QM31Limbs := ![⟨1632526252,by change 1632526252<2147483647;omega⟩,⟨1269689629,by change 1269689629<2147483647;omega⟩,⟨1090592280,by change 1090592280<2147483647;omega⟩,⟨419712420,by change 419712420<2147483647;omega⟩]
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
    ok (some ⟨⟨1632526252#u32,1269689629#u32⟩,⟨1090592280#u32,419712420#u32⟩⟩) := JFr_EncodedCell.parser cell041 limbs041 encoded041
#print axioms parser041
def cell042 : Array U8 16#usize := ⟨[58#u8,103#u8,43#u8,29#u8,86#u8,116#u8,182#u8,27#u8,146#u8,54#u8,80#u8,76#u8,208#u8,93#u8,235#u8,107#u8],by rfl⟩
def limbs042 : QM31Limbs := ![⟨489383738,by change 489383738<2147483647;omega⟩,⟨464942166,by change 464942166<2147483647;omega⟩,⟨1280325266,by change 1280325266<2147483647;omega⟩,⟨1810587088,by change 1810587088<2147483647;omega⟩]
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
    ok (some ⟨⟨489383738#u32,464942166#u32⟩,⟨1280325266#u32,1810587088#u32⟩⟩) := JFr_EncodedCell.parser cell042 limbs042 encoded042
#print axioms parser042
def cell043 : Array U8 16#usize := ⟨[34#u8,166#u8,246#u8,22#u8,122#u8,58#u8,43#u8,5#u8,243#u8,86#u8,107#u8,29#u8,30#u8,78#u8,136#u8,8#u8],by rfl⟩
def limbs043 : QM31Limbs := ![⟨385263138,by change 385263138<2147483647;omega⟩,⟨86719098,by change 86719098<2147483647;omega⟩,⟨493573875,by change 493573875<2147483647;omega⟩,⟨143150622,by change 143150622<2147483647;omega⟩]
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
    ok (some ⟨⟨385263138#u32,86719098#u32⟩,⟨493573875#u32,143150622#u32⟩⟩) := JFr_EncodedCell.parser cell043 limbs043 encoded043
#print axioms parser043
def cell044 : Array U8 16#usize := ⟨[72#u8,183#u8,131#u8,25#u8,74#u8,23#u8,1#u8,56#u8,66#u8,49#u8,215#u8,54#u8,9#u8,101#u8,175#u8,38#u8],by rfl⟩
def limbs044 : QM31Limbs := ![⟨428062536,by change 428062536<2147483647;omega⟩,⟨939595594,by change 939595594<2147483647;omega⟩,⟨920072514,by change 920072514<2147483647;omega⟩,⟨649028873,by change 649028873<2147483647;omega⟩]
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
    ok (some ⟨⟨428062536#u32,939595594#u32⟩,⟨920072514#u32,649028873#u32⟩⟩) := JFr_EncodedCell.parser cell044 limbs044 encoded044
#print axioms parser044
def cell045 : Array U8 16#usize := ⟨[7#u8,252#u8,179#u8,77#u8,198#u8,153#u8,239#u8,67#u8,48#u8,97#u8,140#u8,51#u8,103#u8,146#u8,26#u8,122#u8],by rfl⟩
def limbs045 : QM31Limbs := ![⟨1303641095,by change 1303641095<2147483647;omega⟩,⟨1139775942,by change 1139775942<2147483647;omega⟩,⟨864837936,by change 864837936<2147483647;omega⟩,⟨2048561767,by change 2048561767<2147483647;omega⟩]
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
    ok (some ⟨⟨1303641095#u32,1139775942#u32⟩,⟨864837936#u32,2048561767#u32⟩⟩) := JFr_EncodedCell.parser cell045 limbs045 encoded045
#print axioms parser045
def cell046 : Array U8 16#usize := ⟨[244#u8,30#u8,69#u8,47#u8,79#u8,86#u8,44#u8,41#u8,131#u8,3#u8,252#u8,68#u8,184#u8,128#u8,244#u8,34#u8],by rfl⟩
def limbs046 : QM31Limbs := ![⟨793059060,by change 793059060<2147483647;omega⟩,⟨690771535,by change 690771535<2147483647;omega⟩,⟨1157366659,by change 1157366659<2147483647;omega⟩,⟨586449080,by change 586449080<2147483647;omega⟩]
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
    ok (some ⟨⟨793059060#u32,690771535#u32⟩,⟨1157366659#u32,586449080#u32⟩⟩) := JFr_EncodedCell.parser cell046 limbs046 encoded046
#print axioms parser046
def cell047 : Array U8 16#usize := ⟨[104#u8,207#u8,63#u8,80#u8,192#u8,235#u8,211#u8,106#u8,238#u8,23#u8,42#u8,85#u8,19#u8,61#u8,23#u8,20#u8],by rfl⟩
def limbs047 : QM31Limbs := ![⟨1346359144,by change 1346359144<2147483647;omega⟩,⟨1792273344,by change 1792273344<2147483647;omega⟩,⟨1428821998,by change 1428821998<2147483647;omega⟩,⟨337067283,by change 337067283<2147483647;omega⟩]
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
    ok (some ⟨⟨1346359144#u32,1792273344#u32⟩,⟨1428821998#u32,337067283#u32⟩⟩) := JFr_EncodedCell.parser cell047 limbs047 encoded047
#print axioms parser047
def cell048 : Array U8 16#usize := ⟨[52#u8,18#u8,133#u8,74#u8,125#u8,24#u8,217#u8,20#u8,39#u8,44#u8,156#u8,7#u8,255#u8,64#u8,33#u8,74#u8],by rfl⟩
def limbs048 : QM31Limbs := ![⟨1250234932,by change 1250234932<2147483647;omega⟩,⟨349771901,by change 349771901<2147483647;omega⟩,⟨127675431,by change 127675431<2147483647;omega⟩,⟨1243693311,by change 1243693311<2147483647;omega⟩]
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
    ok (some ⟨⟨1250234932#u32,349771901#u32⟩,⟨127675431#u32,1243693311#u32⟩⟩) := JFr_EncodedCell.parser cell048 limbs048 encoded048
#print axioms parser048
def cell049 : Array U8 16#usize := ⟨[227#u8,221#u8,13#u8,75#u8,178#u8,171#u8,144#u8,16#u8,181#u8,16#u8,63#u8,39#u8,181#u8,86#u8,139#u8,24#u8],by rfl⟩
def limbs049 : QM31Limbs := ![⟨1259199971,by change 1259199971<2147483647;omega⟩,⟨277916594,by change 277916594<2147483647;omega⟩,⟨658444469,by change 658444469<2147483647;omega⟩,⟨411784885,by change 411784885<2147483647;omega⟩]
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
    ok (some ⟨⟨1259199971#u32,277916594#u32⟩,⟨658444469#u32,411784885#u32⟩⟩) := JFr_EncodedCell.parser cell049 limbs049 encoded049
#print axioms parser049
def cell050 : Array U8 16#usize := ⟨[125#u8,20#u8,211#u8,96#u8,42#u8,142#u8,243#u8,110#u8,155#u8,30#u8,171#u8,111#u8,176#u8,216#u8,72#u8,14#u8],by rfl⟩
def limbs050 : QM31Limbs := ![⟨1624446077,by change 1624446077<2147483647;omega⟩,⟨1861455402,by change 1861455402<2147483647;omega⟩,⟨1873485467,by change 1873485467<2147483647;omega⟩,⟨239655088,by change 239655088<2147483647;omega⟩]
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
    ok (some ⟨⟨1624446077#u32,1861455402#u32⟩,⟨1873485467#u32,239655088#u32⟩⟩) := JFr_EncodedCell.parser cell050 limbs050 encoded050
#print axioms parser050
def cell051 : Array U8 16#usize := ⟨[123#u8,35#u8,23#u8,79#u8,72#u8,194#u8,33#u8,107#u8,124#u8,184#u8,36#u8,112#u8,200#u8,191#u8,222#u8,116#u8],by rfl⟩
def limbs051 : QM31Limbs := ![⟨1326916475,by change 1326916475<2147483647;omega⟩,⟨1797374536,by change 1797374536<2147483647;omega⟩,⟨1881454716,by change 1881454716<2147483647;omega⟩,⟨1960755144,by change 1960755144<2147483647;omega⟩]
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
    ok (some ⟨⟨1326916475#u32,1797374536#u32⟩,⟨1881454716#u32,1960755144#u32⟩⟩) := JFr_EncodedCell.parser cell051 limbs051 encoded051
#print axioms parser051
def cell052 : Array U8 16#usize := ⟨[23#u8,150#u8,48#u8,30#u8,10#u8,100#u8,214#u8,74#u8,9#u8,198#u8,81#u8,115#u8,228#u8,128#u8,254#u8,83#u8],by rfl⟩
def limbs052 : QM31Limbs := ![⟨506500631,by change 506500631<2147483647;omega⟩,⟨1255564298,by change 1255564298<2147483647;omega⟩,⟨1934738953,by change 1934738953<2147483647;omega⟩,⟨1409188068,by change 1409188068<2147483647;omega⟩]
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
    ok (some ⟨⟨506500631#u32,1255564298#u32⟩,⟨1934738953#u32,1409188068#u32⟩⟩) := JFr_EncodedCell.parser cell052 limbs052 encoded052
#print axioms parser052
def cell053 : Array U8 16#usize := ⟨[13#u8,190#u8,233#u8,57#u8,41#u8,144#u8,152#u8,75#u8,79#u8,15#u8,54#u8,8#u8,114#u8,136#u8,50#u8,42#u8],by rfl⟩
def limbs053 : QM31Limbs := ![⟨971619853,by change 971619853<2147483647;omega⟩,⟨1268289577,by change 1268289577<2147483647;omega⟩,⟨137760591,by change 137760591<2147483647;omega⟩,⟨707954802,by change 707954802<2147483647;omega⟩]
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
    ok (some ⟨⟨971619853#u32,1268289577#u32⟩,⟨137760591#u32,707954802#u32⟩⟩) := JFr_EncodedCell.parser cell053 limbs053 encoded053
#print axioms parser053
def cell054 : Array U8 16#usize := ⟨[55#u8,47#u8,228#u8,31#u8,126#u8,45#u8,59#u8,77#u8,222#u8,196#u8,194#u8,86#u8,194#u8,245#u8,151#u8,105#u8],by rfl⟩
def limbs054 : QM31Limbs := ![⟨535047991,by change 535047991<2147483647;omega⟩,⟨1295723902,by change 1295723902<2147483647;omega⟩,⟨1455604958,by change 1455604958<2147483647;omega⟩,⟨1771566530,by change 1771566530<2147483647;omega⟩]
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
    ok (some ⟨⟨535047991#u32,1295723902#u32⟩,⟨1455604958#u32,1771566530#u32⟩⟩) := JFr_EncodedCell.parser cell054 limbs054 encoded054
#print axioms parser054
def cell055 : Array U8 16#usize := ⟨[5#u8,65#u8,103#u8,11#u8,187#u8,233#u8,130#u8,88#u8,184#u8,11#u8,65#u8,60#u8,182#u8,235#u8,38#u8,125#u8],by rfl⟩
def limbs055 : QM31Limbs := ![⟨191316229,by change 191316229<2147483647;omega⟩,⟨1484974523,by change 1484974523<2147483647;omega⟩,⟨1010895800,by change 1010895800<2147483647;omega⟩,⟨2099702710,by change 2099702710<2147483647;omega⟩]
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
    ok (some ⟨⟨191316229#u32,1484974523#u32⟩,⟨1010895800#u32,2099702710#u32⟩⟩) := JFr_EncodedCell.parser cell055 limbs055 encoded055
#print axioms parser055
def cell056 : Array U8 16#usize := ⟨[212#u8,142#u8,169#u8,78#u8,141#u8,108#u8,243#u8,79#u8,76#u8,188#u8,60#u8,33#u8,172#u8,254#u8,228#u8,119#u8],by rfl⟩
def limbs056 : QM31Limbs := ![⟨1319734996,by change 1319734996<2147483647;omega⟩,⟨1341353101,by change 1341353101<2147483647;omega⟩,⟨557628492,by change 557628492<2147483647;omega⟩,⟨2011496108,by change 2011496108<2147483647;omega⟩]
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
    ok (some ⟨⟨1319734996#u32,1341353101#u32⟩,⟨557628492#u32,2011496108#u32⟩⟩) := JFr_EncodedCell.parser cell056 limbs056 encoded056
#print axioms parser056
def cell057 : Array U8 16#usize := ⟨[203#u8,0#u8,178#u8,126#u8,20#u8,16#u8,119#u8,60#u8,57#u8,188#u8,71#u8,24#u8,115#u8,180#u8,3#u8,99#u8],by rfl⟩
def limbs057 : QM31Limbs := ![⟨2125594827,by change 2125594827<2147483647;omega⟩,⟨1014435860,by change 1014435860<2147483647;omega⟩,⟨407354425,by change 407354425<2147483647;omega⟩,⟨1661187187,by change 1661187187<2147483647;omega⟩]
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
    ok (some ⟨⟨2125594827#u32,1014435860#u32⟩,⟨407354425#u32,1661187187#u32⟩⟩) := JFr_EncodedCell.parser cell057 limbs057 encoded057
#print axioms parser057
end AspisR1.JFu_ClaimsData
