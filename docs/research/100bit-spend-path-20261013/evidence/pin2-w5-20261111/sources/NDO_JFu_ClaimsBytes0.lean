import NDO_JFu_ClaimsData
set_option autoImplicit false
namespace AspisR1.JFu_ClaimsData
open Aeneas Aeneas.Std Result RetainedFieldByteCodec
open AspisR1PublicPreparation AspisS1ExtractedRoundChildren
open JFu_Q25Source.Input
def cell000 : Array U8 16#usize := ⟨[163#u8,112#u8,101#u8,53#u8,9#u8,97#u8,241#u8,103#u8,142#u8,192#u8,246#u8,90#u8,246#u8,95#u8,190#u8,103#u8],by rfl⟩
def limbs000 : QM31Limbs := ![⟨895840419,by change 895840419<2147483647;omega⟩,⟨1743872265,by change 1743872265<2147483647;omega⟩,⟨1526120590,by change 1526120590<2147483647;omega⟩,⟨1740529654,by change 1740529654<2147483647;omega⟩]
theorem window000 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*0)).take 16=cell000.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*0)).take 16=cell000.val
  rw [JFu_FlatWindow.source chunks lengths 0 (by change 0<116;omega)]
  rfl
#print axioms window000
theorem encoded000 : CandidateParserByteOrder.arrayBytes16 cell000=encodeQM31LE limbs000 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded000
theorem parser000 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell000)=
    ok (some ⟨⟨895840419#u32,1743872265#u32⟩,⟨1526120590#u32,1740529654#u32⟩⟩) := JFr_EncodedCell.parser cell000 limbs000 encoded000
#print axioms parser000
def cell001 : Array U8 16#usize := ⟨[154#u8,218#u8,129#u8,24#u8,208#u8,151#u8,62#u8,73#u8,253#u8,251#u8,248#u8,43#u8,142#u8,82#u8,179#u8,112#u8],by rfl⟩
def limbs001 : QM31Limbs := ![⟨411163290,by change 411163290<2147483647;omega⟩,⟨1228838864,by change 1228838864<2147483647;omega⟩,⟨737737725,by change 737737725<2147483647;omega⟩,⟨1890800270,by change 1890800270<2147483647;omega⟩]
theorem window001 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*1)).take 16=cell001.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*1)).take 16=cell001.val
  rw [JFu_FlatWindow.source chunks lengths 1 (by change 1<116;omega)]
  rfl
#print axioms window001
theorem encoded001 : CandidateParserByteOrder.arrayBytes16 cell001=encodeQM31LE limbs001 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded001
theorem parser001 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell001)=
    ok (some ⟨⟨411163290#u32,1228838864#u32⟩,⟨737737725#u32,1890800270#u32⟩⟩) := JFr_EncodedCell.parser cell001 limbs001 encoded001
#print axioms parser001
def cell002 : Array U8 16#usize := ⟨[78#u8,110#u8,145#u8,102#u8,135#u8,132#u8,37#u8,9#u8,21#u8,131#u8,229#u8,70#u8,86#u8,45#u8,226#u8,75#u8],by rfl⟩
def limbs002 : QM31Limbs := ![⟨1720806990,by change 1720806990<2147483647;omega⟩,⟨153453703,by change 153453703<2147483647;omega⟩,⟨1189446421,by change 1189446421<2147483647;omega⟩,⟨1273113942,by change 1273113942<2147483647;omega⟩]
theorem window002 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*2)).take 16=cell002.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*2)).take 16=cell002.val
  rw [JFu_FlatWindow.source chunks lengths 2 (by change 2<116;omega)]
  rfl
#print axioms window002
theorem encoded002 : CandidateParserByteOrder.arrayBytes16 cell002=encodeQM31LE limbs002 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded002
theorem parser002 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell002)=
    ok (some ⟨⟨1720806990#u32,153453703#u32⟩,⟨1189446421#u32,1273113942#u32⟩⟩) := JFr_EncodedCell.parser cell002 limbs002 encoded002
#print axioms parser002
def cell003 : Array U8 16#usize := ⟨[1#u8,107#u8,45#u8,120#u8,166#u8,67#u8,34#u8,18#u8,111#u8,103#u8,109#u8,1#u8,107#u8,167#u8,173#u8,81#u8],by rfl⟩
def limbs003 : QM31Limbs := ![⟨2016242433,by change 2016242433<2147483647;omega⟩,⟨304235430,by change 304235430<2147483647;omega⟩,⟨23947119,by change 23947119<2147483647;omega⟩,⟨1370335083,by change 1370335083<2147483647;omega⟩]
theorem window003 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*3)).take 16=cell003.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*3)).take 16=cell003.val
  rw [JFu_FlatWindow.source chunks lengths 3 (by change 3<116;omega)]
  rfl
#print axioms window003
theorem encoded003 : CandidateParserByteOrder.arrayBytes16 cell003=encodeQM31LE limbs003 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded003
theorem parser003 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell003)=
    ok (some ⟨⟨2016242433#u32,304235430#u32⟩,⟨23947119#u32,1370335083#u32⟩⟩) := JFr_EncodedCell.parser cell003 limbs003 encoded003
#print axioms parser003
def cell004 : Array U8 16#usize := ⟨[13#u8,87#u8,6#u8,102#u8,202#u8,253#u8,122#u8,120#u8,169#u8,237#u8,164#u8,64#u8,163#u8,221#u8,151#u8,7#u8],by rfl⟩
def limbs004 : QM31Limbs := ![⟨1711691533,by change 1711691533<2147483647;omega⟩,⟨2021326282,by change 2021326282<2147483647;omega⟩,⟨1084550569,by change 1084550569<2147483647;omega⟩,⟨127393187,by change 127393187<2147483647;omega⟩]
theorem window004 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*4)).take 16=cell004.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*4)).take 16=cell004.val
  rw [JFu_FlatWindow.source chunks lengths 4 (by change 4<116;omega)]
  rfl
#print axioms window004
theorem encoded004 : CandidateParserByteOrder.arrayBytes16 cell004=encodeQM31LE limbs004 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded004
theorem parser004 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell004)=
    ok (some ⟨⟨1711691533#u32,2021326282#u32⟩,⟨1084550569#u32,127393187#u32⟩⟩) := JFr_EncodedCell.parser cell004 limbs004 encoded004
#print axioms parser004
def cell005 : Array U8 16#usize := ⟨[221#u8,4#u8,51#u8,56#u8,155#u8,120#u8,77#u8,89#u8,16#u8,59#u8,5#u8,73#u8,123#u8,19#u8,184#u8,17#u8],by rfl⟩
def limbs005 : QM31Limbs := ![⟨942867677,by change 942867677<2147483647;omega⟩,⟨1498249371,by change 1498249371<2147483647;omega⟩,⟨1225079568,by change 1225079568<2147483647;omega⟩,⟨297276283,by change 297276283<2147483647;omega⟩]
theorem window005 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*5)).take 16=cell005.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*5)).take 16=cell005.val
  rw [JFu_FlatWindow.source chunks lengths 5 (by change 5<116;omega)]
  rfl
#print axioms window005
theorem encoded005 : CandidateParserByteOrder.arrayBytes16 cell005=encodeQM31LE limbs005 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded005
theorem parser005 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell005)=
    ok (some ⟨⟨942867677#u32,1498249371#u32⟩,⟨1225079568#u32,297276283#u32⟩⟩) := JFr_EncodedCell.parser cell005 limbs005 encoded005
#print axioms parser005
def cell006 : Array U8 16#usize := ⟨[80#u8,87#u8,206#u8,87#u8,8#u8,251#u8,227#u8,45#u8,123#u8,17#u8,251#u8,83#u8,107#u8,174#u8,207#u8,87#u8],by rfl⟩
def limbs006 : QM31Limbs := ![⟨1473140560,by change 1473140560<2147483647;omega⟩,⟨769915656,by change 769915656<2147483647;omega⟩,⟨1408962939,by change 1408962939<2147483647;omega⟩,⟨1473228395,by change 1473228395<2147483647;omega⟩]
theorem window006 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*6)).take 16=cell006.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*6)).take 16=cell006.val
  rw [JFu_FlatWindow.source chunks lengths 6 (by change 6<116;omega)]
  rfl
#print axioms window006
theorem encoded006 : CandidateParserByteOrder.arrayBytes16 cell006=encodeQM31LE limbs006 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded006
theorem parser006 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell006)=
    ok (some ⟨⟨1473140560#u32,769915656#u32⟩,⟨1408962939#u32,1473228395#u32⟩⟩) := JFr_EncodedCell.parser cell006 limbs006 encoded006
#print axioms parser006
def cell007 : Array U8 16#usize := ⟨[231#u8,99#u8,255#u8,61#u8,220#u8,139#u8,34#u8,82#u8,245#u8,8#u8,38#u8,124#u8,19#u8,79#u8,98#u8,105#u8],by rfl⟩
def limbs007 : QM31Limbs := ![⟨1040147431,by change 1040147431<2147483647;omega⟩,⟨1377995740,by change 1377995740<2147483647;omega⟩,⟨2082867445,by change 2082867445<2147483647;omega⟩,⟨1768050451,by change 1768050451<2147483647;omega⟩]
theorem window007 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*7)).take 16=cell007.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*7)).take 16=cell007.val
  rw [JFu_FlatWindow.source chunks lengths 7 (by change 7<116;omega)]
  rfl
#print axioms window007
theorem encoded007 : CandidateParserByteOrder.arrayBytes16 cell007=encodeQM31LE limbs007 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded007
theorem parser007 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell007)=
    ok (some ⟨⟨1040147431#u32,1377995740#u32⟩,⟨2082867445#u32,1768050451#u32⟩⟩) := JFr_EncodedCell.parser cell007 limbs007 encoded007
#print axioms parser007
def cell008 : Array U8 16#usize := ⟨[64#u8,25#u8,180#u8,54#u8,235#u8,204#u8,250#u8,21#u8,52#u8,184#u8,156#u8,9#u8,171#u8,100#u8,14#u8,58#u8],by rfl⟩
def limbs008 : QM31Limbs := ![⟨917772608,by change 917772608<2147483647;omega⟩,⟨368757995,by change 368757995<2147483647;omega⟩,⟨161265716,by change 161265716<2147483647;omega⟩,⟨974021803,by change 974021803<2147483647;omega⟩]
theorem window008 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*8)).take 16=cell008.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*8)).take 16=cell008.val
  rw [JFu_FlatWindow.source chunks lengths 8 (by change 8<116;omega)]
  rfl
#print axioms window008
theorem encoded008 : CandidateParserByteOrder.arrayBytes16 cell008=encodeQM31LE limbs008 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded008
theorem parser008 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell008)=
    ok (some ⟨⟨917772608#u32,368757995#u32⟩,⟨161265716#u32,974021803#u32⟩⟩) := JFr_EncodedCell.parser cell008 limbs008 encoded008
#print axioms parser008
def cell009 : Array U8 16#usize := ⟨[100#u8,233#u8,32#u8,71#u8,213#u8,9#u8,43#u8,18#u8,118#u8,92#u8,53#u8,96#u8,93#u8,37#u8,81#u8,59#u8],by rfl⟩
def limbs009 : QM31Limbs := ![⟨1193339236,by change 1193339236<2147483647;omega⟩,⟨304810453,by change 304810453<2147483647;omega⟩,⟨1614109814,by change 1614109814<2147483647;omega⟩,⟨995173725,by change 995173725<2147483647;omega⟩]
theorem window009 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*9)).take 16=cell009.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*9)).take 16=cell009.val
  rw [JFu_FlatWindow.source chunks lengths 9 (by change 9<116;omega)]
  rfl
#print axioms window009
theorem encoded009 : CandidateParserByteOrder.arrayBytes16 cell009=encodeQM31LE limbs009 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded009
theorem parser009 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell009)=
    ok (some ⟨⟨1193339236#u32,304810453#u32⟩,⟨1614109814#u32,995173725#u32⟩⟩) := JFr_EncodedCell.parser cell009 limbs009 encoded009
#print axioms parser009
def cell010 : Array U8 16#usize := ⟨[110#u8,12#u8,190#u8,87#u8,222#u8,220#u8,149#u8,78#u8,84#u8,12#u8,91#u8,30#u8,84#u8,167#u8,153#u8,48#u8],by rfl⟩
def limbs010 : QM31Limbs := ![⟨1472072814,by change 1472072814<2147483647;omega⟩,⟨1318444254,by change 1318444254<2147483647;omega⟩,⟨509283412,by change 509283412<2147483647;omega⟩,⟨815376212,by change 815376212<2147483647;omega⟩]
theorem window010 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*10)).take 16=cell010.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*10)).take 16=cell010.val
  rw [JFu_FlatWindow.source chunks lengths 10 (by change 10<116;omega)]
  rfl
#print axioms window010
theorem encoded010 : CandidateParserByteOrder.arrayBytes16 cell010=encodeQM31LE limbs010 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded010
theorem parser010 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell010)=
    ok (some ⟨⟨1472072814#u32,1318444254#u32⟩,⟨509283412#u32,815376212#u32⟩⟩) := JFr_EncodedCell.parser cell010 limbs010 encoded010
#print axioms parser010
def cell011 : Array U8 16#usize := ⟨[114#u8,37#u8,112#u8,14#u8,79#u8,219#u8,240#u8,61#u8,80#u8,133#u8,37#u8,82#u8,44#u8,245#u8,36#u8,83#u8],by rfl⟩
def limbs011 : QM31Limbs := ![⟨242230642,by change 242230642<2147483647;omega⟩,⟨1039194959,by change 1039194959<2147483647;omega⟩,⟨1378190672,by change 1378190672<2147483647;omega⟩,⟨1394930988,by change 1394930988<2147483647;omega⟩]
theorem window011 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*11)).take 16=cell011.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*11)).take 16=cell011.val
  rw [JFu_FlatWindow.source chunks lengths 11 (by change 11<116;omega)]
  rfl
#print axioms window011
theorem encoded011 : CandidateParserByteOrder.arrayBytes16 cell011=encodeQM31LE limbs011 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded011
theorem parser011 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell011)=
    ok (some ⟨⟨242230642#u32,1039194959#u32⟩,⟨1378190672#u32,1394930988#u32⟩⟩) := JFr_EncodedCell.parser cell011 limbs011 encoded011
#print axioms parser011
def cell012 : Array U8 16#usize := ⟨[215#u8,16#u8,157#u8,70#u8,24#u8,242#u8,68#u8,119#u8,107#u8,221#u8,227#u8,99#u8,20#u8,116#u8,40#u8,115#u8],by rfl⟩
def limbs012 : QM31Limbs := ![⟨1184698583,by change 1184698583<2147483647;omega⟩,⟨2001007128,by change 2001007128<2147483647;omega⟩,⟨1675877739,by change 1675877739<2147483647;omega⟩,⟨1932030996,by change 1932030996<2147483647;omega⟩]
theorem window012 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*12)).take 16=cell012.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*12)).take 16=cell012.val
  rw [JFu_FlatWindow.source chunks lengths 12 (by change 12<116;omega)]
  rfl
#print axioms window012
theorem encoded012 : CandidateParserByteOrder.arrayBytes16 cell012=encodeQM31LE limbs012 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded012
theorem parser012 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell012)=
    ok (some ⟨⟨1184698583#u32,2001007128#u32⟩,⟨1675877739#u32,1932030996#u32⟩⟩) := JFr_EncodedCell.parser cell012 limbs012 encoded012
#print axioms parser012
def cell013 : Array U8 16#usize := ⟨[155#u8,105#u8,38#u8,127#u8,13#u8,138#u8,243#u8,72#u8,114#u8,207#u8,42#u8,79#u8,140#u8,92#u8,82#u8,6#u8],by rfl⟩
def limbs013 : QM31Limbs := ![⟨2133223835,by change 2133223835<2147483647;omega⟩,⟨1223920141,by change 1223920141<2147483647;omega⟩,⟨1328205682,by change 1328205682<2147483647;omega⟩,⟨106060940,by change 106060940<2147483647;omega⟩]
theorem window013 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*13)).take 16=cell013.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*13)).take 16=cell013.val
  rw [JFu_FlatWindow.source chunks lengths 13 (by change 13<116;omega)]
  rfl
#print axioms window013
theorem encoded013 : CandidateParserByteOrder.arrayBytes16 cell013=encodeQM31LE limbs013 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded013
theorem parser013 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell013)=
    ok (some ⟨⟨2133223835#u32,1223920141#u32⟩,⟨1328205682#u32,106060940#u32⟩⟩) := JFr_EncodedCell.parser cell013 limbs013 encoded013
#print axioms parser013
def cell014 : Array U8 16#usize := ⟨[215#u8,5#u8,171#u8,88#u8,21#u8,206#u8,201#u8,9#u8,76#u8,201#u8,60#u8,33#u8,201#u8,139#u8,251#u8,11#u8],by rfl⟩
def limbs014 : QM31Limbs := ![⟨1487603159,by change 1487603159<2147483647;omega⟩,⟨164220437,by change 164220437<2147483647;omega⟩,⟨557631820,by change 557631820<2147483647;omega⟩,⟨201034697,by change 201034697<2147483647;omega⟩]
theorem window014 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*14)).take 16=cell014.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*14)).take 16=cell014.val
  rw [JFu_FlatWindow.source chunks lengths 14 (by change 14<116;omega)]
  rfl
#print axioms window014
theorem encoded014 : CandidateParserByteOrder.arrayBytes16 cell014=encodeQM31LE limbs014 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded014
theorem parser014 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell014)=
    ok (some ⟨⟨1487603159#u32,164220437#u32⟩,⟨557631820#u32,201034697#u32⟩⟩) := JFr_EncodedCell.parser cell014 limbs014 encoded014
#print axioms parser014
def cell015 : Array U8 16#usize := ⟨[240#u8,99#u8,85#u8,18#u8,219#u8,188#u8,185#u8,0#u8,159#u8,213#u8,215#u8,17#u8,139#u8,23#u8,99#u8,70#u8],by rfl⟩
def limbs015 : QM31Limbs := ![⟨307586032,by change 307586032<2147483647;omega⟩,⟨12172507,by change 12172507<2147483647;omega⟩,⟨299357599,by change 299357599<2147483647;omega⟩,⟨1180899211,by change 1180899211<2147483647;omega⟩]
theorem window015 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*15)).take 16=cell015.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*15)).take 16=cell015.val
  rw [JFu_FlatWindow.source chunks lengths 15 (by change 15<116;omega)]
  rfl
#print axioms window015
theorem encoded015 : CandidateParserByteOrder.arrayBytes16 cell015=encodeQM31LE limbs015 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded015
theorem parser015 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell015)=
    ok (some ⟨⟨307586032#u32,12172507#u32⟩,⟨299357599#u32,1180899211#u32⟩⟩) := JFr_EncodedCell.parser cell015 limbs015 encoded015
#print axioms parser015
def cell016 : Array U8 16#usize := ⟨[94#u8,164#u8,86#u8,46#u8,195#u8,208#u8,137#u8,71#u8,99#u8,94#u8,206#u8,83#u8,121#u8,214#u8,15#u8,69#u8],by rfl⟩
def limbs016 : QM31Limbs := ![⟨777430110,by change 777430110<2147483647;omega⟩,⟨1200214211,by change 1200214211<2147483647;omega⟩,⟨1406033507,by change 1406033507<2147483647;omega⟩,⟨1158665849,by change 1158665849<2147483647;omega⟩]
theorem window016 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*16)).take 16=cell016.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*16)).take 16=cell016.val
  rw [JFu_FlatWindow.source chunks lengths 16 (by change 16<116;omega)]
  rfl
#print axioms window016
theorem encoded016 : CandidateParserByteOrder.arrayBytes16 cell016=encodeQM31LE limbs016 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded016
theorem parser016 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell016)=
    ok (some ⟨⟨777430110#u32,1200214211#u32⟩,⟨1406033507#u32,1158665849#u32⟩⟩) := JFr_EncodedCell.parser cell016 limbs016 encoded016
#print axioms parser016
def cell017 : Array U8 16#usize := ⟨[189#u8,145#u8,22#u8,105#u8,39#u8,22#u8,120#u8,82#u8,241#u8,61#u8,161#u8,111#u8,111#u8,170#u8,11#u8,41#u8],by rfl⟩
def limbs017 : QM31Limbs := ![⟨1763086781,by change 1763086781<2147483647;omega⟩,⟨1383601703,by change 1383601703<2147483647;omega⟩,⟨1872838129,by change 1872838129<2147483647;omega⟩,⟨688630383,by change 688630383<2147483647;omega⟩]
theorem window017 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*17)).take 16=cell017.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*17)).take 16=cell017.val
  rw [JFu_FlatWindow.source chunks lengths 17 (by change 17<116;omega)]
  rfl
#print axioms window017
theorem encoded017 : CandidateParserByteOrder.arrayBytes16 cell017=encodeQM31LE limbs017 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded017
theorem parser017 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell017)=
    ok (some ⟨⟨1763086781#u32,1383601703#u32⟩,⟨1872838129#u32,688630383#u32⟩⟩) := JFr_EncodedCell.parser cell017 limbs017 encoded017
#print axioms parser017
def cell018 : Array U8 16#usize := ⟨[108#u8,20#u8,237#u8,53#u8,79#u8,36#u8,237#u8,19#u8,10#u8,54#u8,245#u8,122#u8,231#u8,35#u8,202#u8,67#u8],by rfl⟩
def limbs018 : QM31Limbs := ![⟨904729708,by change 904729708<2147483647;omega⟩,⟨334308431,by change 334308431<2147483647;omega⟩,⟨2062890506,by change 2062890506<2147483647;omega⟩,⟨1137320935,by change 1137320935<2147483647;omega⟩]
theorem window018 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*18)).take 16=cell018.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*18)).take 16=cell018.val
  rw [JFu_FlatWindow.source chunks lengths 18 (by change 18<116;omega)]
  rfl
#print axioms window018
theorem encoded018 : CandidateParserByteOrder.arrayBytes16 cell018=encodeQM31LE limbs018 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded018
theorem parser018 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell018)=
    ok (some ⟨⟨904729708#u32,334308431#u32⟩,⟨2062890506#u32,1137320935#u32⟩⟩) := JFr_EncodedCell.parser cell018 limbs018 encoded018
#print axioms parser018
def cell019 : Array U8 16#usize := ⟨[82#u8,236#u8,66#u8,33#u8,135#u8,227#u8,57#u8,96#u8,79#u8,24#u8,244#u8,119#u8,66#u8,30#u8,105#u8,59#u8],by rfl⟩
def limbs019 : QM31Limbs := ![⟨558034002,by change 558034002<2147483647;omega⟩,⟨1614406535,by change 1614406535<2147483647;omega⟩,⟨2012485711,by change 2012485711<2147483647;omega⟩,⟨996744770,by change 996744770<2147483647;omega⟩]
theorem window019 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*19)).take 16=cell019.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*19)).take 16=cell019.val
  rw [JFu_FlatWindow.source chunks lengths 19 (by change 19<116;omega)]
  rfl
#print axioms window019
theorem encoded019 : CandidateParserByteOrder.arrayBytes16 cell019=encodeQM31LE limbs019 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded019
theorem parser019 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell019)=
    ok (some ⟨⟨558034002#u32,1614406535#u32⟩,⟨2012485711#u32,996744770#u32⟩⟩) := JFr_EncodedCell.parser cell019 limbs019 encoded019
#print axioms parser019
def cell020 : Array U8 16#usize := ⟨[233#u8,172#u8,59#u8,38#u8,155#u8,159#u8,25#u8,60#u8,8#u8,199#u8,135#u8,85#u8,15#u8,10#u8,228#u8,72#u8],by rfl⟩
def limbs020 : QM31Limbs := ![⟨641445097,by change 641445097<2147483647;omega⟩,⟨1008312219,by change 1008312219<2147483647;omega⟩,⟨1434961672,by change 1434961672<2147483647;omega⟩,⟨1222904335,by change 1222904335<2147483647;omega⟩]
theorem window020 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*20)).take 16=cell020.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*20)).take 16=cell020.val
  rw [JFu_FlatWindow.source chunks lengths 20 (by change 20<116;omega)]
  rfl
#print axioms window020
theorem encoded020 : CandidateParserByteOrder.arrayBytes16 cell020=encodeQM31LE limbs020 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded020
theorem parser020 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell020)=
    ok (some ⟨⟨641445097#u32,1008312219#u32⟩,⟨1434961672#u32,1222904335#u32⟩⟩) := JFr_EncodedCell.parser cell020 limbs020 encoded020
#print axioms parser020
def cell021 : Array U8 16#usize := ⟨[231#u8,32#u8,31#u8,122#u8,62#u8,111#u8,87#u8,67#u8,66#u8,46#u8,89#u8,32#u8,215#u8,116#u8,82#u8,54#u8],by rfl⟩
def limbs021 : QM31Limbs := ![⟨2048860391,by change 2048860391<2147483647;omega⟩,⟨1129803582,by change 1129803582<2147483647;omega⟩,⟨542715458,by change 542715458<2147483647;omega⟩,⟨911373527,by change 911373527<2147483647;omega⟩]
theorem window021 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*21)).take 16=cell021.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*21)).take 16=cell021.val
  rw [JFu_FlatWindow.source chunks lengths 21 (by change 21<116;omega)]
  rfl
#print axioms window021
theorem encoded021 : CandidateParserByteOrder.arrayBytes16 cell021=encodeQM31LE limbs021 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded021
theorem parser021 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell021)=
    ok (some ⟨⟨2048860391#u32,1129803582#u32⟩,⟨542715458#u32,911373527#u32⟩⟩) := JFr_EncodedCell.parser cell021 limbs021 encoded021
#print axioms parser021
def cell022 : Array U8 16#usize := ⟨[252#u8,188#u8,178#u8,79#u8,228#u8,136#u8,27#u8,67#u8,204#u8,80#u8,250#u8,102#u8,141#u8,48#u8,44#u8,107#u8],by rfl⟩
def limbs022 : QM31Limbs := ![⟨1337113852,by change 1337113852<2147483647;omega⟩,⟨1125877988,by change 1125877988<2147483647;omega⟩,⟨1727680716,by change 1727680716<2147483647;omega⟩,⟨1798058125,by change 1798058125<2147483647;omega⟩]
theorem window022 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*22)).take 16=cell022.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*22)).take 16=cell022.val
  rw [JFu_FlatWindow.source chunks lengths 22 (by change 22<116;omega)]
  rfl
#print axioms window022
theorem encoded022 : CandidateParserByteOrder.arrayBytes16 cell022=encodeQM31LE limbs022 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded022
theorem parser022 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell022)=
    ok (some ⟨⟨1337113852#u32,1125877988#u32⟩,⟨1727680716#u32,1798058125#u32⟩⟩) := JFr_EncodedCell.parser cell022 limbs022 encoded022
#print axioms parser022
def cell023 : Array U8 16#usize := ⟨[146#u8,75#u8,249#u8,45#u8,120#u8,134#u8,77#u8,30#u8,35#u8,189#u8,120#u8,103#u8,175#u8,224#u8,4#u8,105#u8],by rfl⟩
def limbs023 : QM31Limbs := ![⟨771312530,by change 771312530<2147483647;omega⟩,⟨508397176,by change 508397176<2147483647;omega⟩,⟨1735965987,by change 1735965987<2147483647;omega⟩,⟨1761927343,by change 1761927343<2147483647;omega⟩]
theorem window023 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*23)).take 16=cell023.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*23)).take 16=cell023.val
  rw [JFu_FlatWindow.source chunks lengths 23 (by change 23<116;omega)]
  rfl
#print axioms window023
theorem encoded023 : CandidateParserByteOrder.arrayBytes16 cell023=encodeQM31LE limbs023 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded023
theorem parser023 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell023)=
    ok (some ⟨⟨771312530#u32,508397176#u32⟩,⟨1735965987#u32,1761927343#u32⟩⟩) := JFr_EncodedCell.parser cell023 limbs023 encoded023
#print axioms parser023
def cell024 : Array U8 16#usize := ⟨[196#u8,188#u8,26#u8,114#u8,17#u8,87#u8,143#u8,78#u8,156#u8,230#u8,92#u8,7#u8,172#u8,80#u8,177#u8,78#u8],by rfl⟩
def limbs024 : QM31Limbs := ![⟨1914354884,by change 1914354884<2147483647;omega⟩,⟨1318016785,by change 1318016785<2147483647;omega⟩,⟨123528860,by change 123528860<2147483647;omega⟩,⟨1320243372,by change 1320243372<2147483647;omega⟩]
theorem window024 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*24)).take 16=cell024.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*24)).take 16=cell024.val
  rw [JFu_FlatWindow.source chunks lengths 24 (by change 24<116;omega)]
  rfl
#print axioms window024
theorem encoded024 : CandidateParserByteOrder.arrayBytes16 cell024=encodeQM31LE limbs024 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded024
theorem parser024 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell024)=
    ok (some ⟨⟨1914354884#u32,1318016785#u32⟩,⟨123528860#u32,1320243372#u32⟩⟩) := JFr_EncodedCell.parser cell024 limbs024 encoded024
#print axioms parser024
def cell025 : Array U8 16#usize := ⟨[216#u8,193#u8,187#u8,42#u8,102#u8,26#u8,79#u8,94#u8,166#u8,45#u8,204#u8,84#u8,207#u8,219#u8,173#u8,78#u8],by rfl⟩
def limbs025 : QM31Limbs := ![⟨716947928,by change 716947928<2147483647;omega⟩,⟨1582242406,by change 1582242406<2147483647;omega⟩,⟨1422667174,by change 1422667174<2147483647;omega⟩,⟨1320016847,by change 1320016847<2147483647;omega⟩]
theorem window025 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*25)).take 16=cell025.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*25)).take 16=cell025.val
  rw [JFu_FlatWindow.source chunks lengths 25 (by change 25<116;omega)]
  rfl
#print axioms window025
theorem encoded025 : CandidateParserByteOrder.arrayBytes16 cell025=encodeQM31LE limbs025 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded025
theorem parser025 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell025)=
    ok (some ⟨⟨716947928#u32,1582242406#u32⟩,⟨1422667174#u32,1320016847#u32⟩⟩) := JFr_EncodedCell.parser cell025 limbs025 encoded025
#print axioms parser025
def cell026 : Array U8 16#usize := ⟨[233#u8,130#u8,188#u8,2#u8,65#u8,10#u8,227#u8,33#u8,5#u8,184#u8,164#u8,18#u8,176#u8,173#u8,232#u8,7#u8],by rfl⟩
def limbs026 : QM31Limbs := ![⟨45908713,by change 45908713<2147483647;omega⟩,⟨568527425,by change 568527425<2147483647;omega⟩,⟨312784901,by change 312784901<2147483647;omega⟩,⟨132689328,by change 132689328<2147483647;omega⟩]
theorem window026 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*26)).take 16=cell026.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*26)).take 16=cell026.val
  rw [JFu_FlatWindow.source chunks lengths 26 (by change 26<116;omega)]
  rfl
#print axioms window026
theorem encoded026 : CandidateParserByteOrder.arrayBytes16 cell026=encodeQM31LE limbs026 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded026
theorem parser026 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell026)=
    ok (some ⟨⟨45908713#u32,568527425#u32⟩,⟨312784901#u32,132689328#u32⟩⟩) := JFr_EncodedCell.parser cell026 limbs026 encoded026
#print axioms parser026
def cell027 : Array U8 16#usize := ⟨[202#u8,52#u8,153#u8,35#u8,70#u8,167#u8,139#u8,110#u8,5#u8,112#u8,237#u8,0#u8,30#u8,29#u8,120#u8,1#u8],by rfl⟩
def limbs027 : QM31Limbs := ![⟨597243082,by change 597243082<2147483647;omega⟩,⟨1854646086,by change 1854646086<2147483647;omega⟩,⟨15560709,by change 15560709<2147483647;omega⟩,⟨24648990,by change 24648990<2147483647;omega⟩]
theorem window027 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*27)).take 16=cell027.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*27)).take 16=cell027.val
  rw [JFu_FlatWindow.source chunks lengths 27 (by change 27<116;omega)]
  rfl
#print axioms window027
theorem encoded027 : CandidateParserByteOrder.arrayBytes16 cell027=encodeQM31LE limbs027 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded027
theorem parser027 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell027)=
    ok (some ⟨⟨597243082#u32,1854646086#u32⟩,⟨15560709#u32,24648990#u32⟩⟩) := JFr_EncodedCell.parser cell027 limbs027 encoded027
#print axioms parser027
def cell028 : Array U8 16#usize := ⟨[84#u8,1#u8,53#u8,74#u8,207#u8,253#u8,12#u8,104#u8,52#u8,117#u8,212#u8,110#u8,19#u8,158#u8,176#u8,2#u8],by rfl⟩
def limbs028 : QM31Limbs := ![⟨1244987732,by change 1244987732<2147483647;omega⟩,⟨1745681871,by change 1745681871<2147483647;omega⟩,⟨1859417396,by change 1859417396<2147483647;omega⟩,⟨45129235,by change 45129235<2147483647;omega⟩]
theorem window028 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*28)).take 16=cell028.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*28)).take 16=cell028.val
  rw [JFu_FlatWindow.source chunks lengths 28 (by change 28<116;omega)]
  rfl
#print axioms window028
theorem encoded028 : CandidateParserByteOrder.arrayBytes16 cell028=encodeQM31LE limbs028 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded028
theorem parser028 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell028)=
    ok (some ⟨⟨1244987732#u32,1745681871#u32⟩,⟨1859417396#u32,45129235#u32⟩⟩) := JFr_EncodedCell.parser cell028 limbs028 encoded028
#print axioms parser028
end AspisR1.JFu_ClaimsData
