import NDO_JFu_ClaimsData
set_option autoImplicit false
namespace AspisR1.JFu_ClaimsData
open Aeneas Aeneas.Std Result RetainedFieldByteCodec
open AspisR1PublicPreparation AspisS1ExtractedRoundChildren
open JFu_Q25Source.Input
def cell000 : Array U8 16#usize := ⟨[34#u8,223#u8,66#u8,75#u8,236#u8,13#u8,63#u8,103#u8,122#u8,93#u8,191#u8,89#u8,98#u8,227#u8,173#u8,35#u8],by rfl⟩
def limbs000 : QM31Limbs := ![⟨1262673698,by change 1262673698<2147483647;omega⟩,⟨1732185580,by change 1732185580<2147483647;omega⟩,⟨1505713530,by change 1505713530<2147483647;omega⟩,⟨598598498,by change 598598498<2147483647;omega⟩]
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
    ok (some ⟨⟨1262673698#u32,1732185580#u32⟩,⟨1505713530#u32,598598498#u32⟩⟩) := JFr_EncodedCell.parser cell000 limbs000 encoded000
#print axioms parser000
def cell001 : Array U8 16#usize := ⟨[142#u8,0#u8,72#u8,7#u8,220#u8,99#u8,36#u8,91#u8,211#u8,49#u8,65#u8,107#u8,113#u8,117#u8,178#u8,112#u8],by rfl⟩
def limbs001 : QM31Limbs := ![⟨122159246,by change 122159246<2147483647;omega⟩,⟨1529111516,by change 1529111516<2147483647;omega⟩,⟨1799434707,by change 1799434707<2147483647;omega⟩,⟨1890743665,by change 1890743665<2147483647;omega⟩]
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
    ok (some ⟨⟨122159246#u32,1529111516#u32⟩,⟨1799434707#u32,1890743665#u32⟩⟩) := JFr_EncodedCell.parser cell001 limbs001 encoded001
#print axioms parser001
def cell002 : Array U8 16#usize := ⟨[203#u8,165#u8,165#u8,35#u8,80#u8,173#u8,144#u8,21#u8,75#u8,178#u8,103#u8,88#u8,169#u8,233#u8,98#u8,5#u8],by rfl⟩
def limbs002 : QM31Limbs := ![⟨598058443,by change 598058443<2147483647;omega⟩,⟨361803088,by change 361803088<2147483647;omega⟩,⟨1483190859,by change 1483190859<2147483647;omega⟩,⟨90368425,by change 90368425<2147483647;omega⟩]
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
    ok (some ⟨⟨598058443#u32,361803088#u32⟩,⟨1483190859#u32,90368425#u32⟩⟩) := JFr_EncodedCell.parser cell002 limbs002 encoded002
#print axioms parser002
def cell003 : Array U8 16#usize := ⟨[45#u8,220#u8,233#u8,94#u8,183#u8,30#u8,242#u8,115#u8,243#u8,132#u8,1#u8,106#u8,90#u8,214#u8,59#u8,32#u8],by rfl⟩
def limbs003 : QM31Limbs := ![⟨1592384557,by change 1592384557<2147483647;omega⟩,⟨1945247415,by change 1945247415<2147483647;omega⟩,⟨1778484467,by change 1778484467<2147483647;omega⟩,⟨540792410,by change 540792410<2147483647;omega⟩]
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
    ok (some ⟨⟨1592384557#u32,1945247415#u32⟩,⟨1778484467#u32,540792410#u32⟩⟩) := JFr_EncodedCell.parser cell003 limbs003 encoded003
#print axioms parser003
def cell004 : Array U8 16#usize := ⟨[168#u8,65#u8,230#u8,38#u8,149#u8,23#u8,80#u8,34#u8,238#u8,223#u8,180#u8,103#u8,25#u8,20#u8,226#u8,126#u8],by rfl⟩
def limbs004 : QM31Limbs := ![⟨652624296,by change 652624296<2147483647;omega⟩,⟨575674261,by change 575674261<2147483647;omega⟩,⟨1739907054,by change 1739907054<2147483647;omega⟩,⟨2128745497,by change 2128745497<2147483647;omega⟩]
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
    ok (some ⟨⟨652624296#u32,575674261#u32⟩,⟨1739907054#u32,2128745497#u32⟩⟩) := JFr_EncodedCell.parser cell004 limbs004 encoded004
#print axioms parser004
def cell005 : Array U8 16#usize := ⟨[86#u8,144#u8,142#u8,15#u8,142#u8,57#u8,118#u8,85#u8,167#u8,49#u8,196#u8,124#u8,189#u8,200#u8,6#u8,107#u8],by rfl⟩
def limbs005 : QM31Limbs := ![⟨261001302,by change 261001302<2147483647;omega⟩,⟨1433811342,by change 1433811342<2147483647;omega⟩,⟨2093232551,by change 2093232551<2147483647;omega⟩,⟨1795606717,by change 1795606717<2147483647;omega⟩]
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
    ok (some ⟨⟨261001302#u32,1433811342#u32⟩,⟨2093232551#u32,1795606717#u32⟩⟩) := JFr_EncodedCell.parser cell005 limbs005 encoded005
#print axioms parser005
def cell006 : Array U8 16#usize := ⟨[69#u8,21#u8,150#u8,90#u8,177#u8,199#u8,231#u8,24#u8,150#u8,61#u8,179#u8,101#u8,150#u8,157#u8,24#u8,95#u8],by rfl⟩
def limbs006 : QM31Limbs := ![⟨1519785285,by change 1519785285<2147483647;omega⟩,⟨417843121,by change 417843121<2147483647;omega⟩,⟨1706245526,by change 1706245526<2147483647;omega⟩,⟨1595448726,by change 1595448726<2147483647;omega⟩]
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
    ok (some ⟨⟨1519785285#u32,417843121#u32⟩,⟨1706245526#u32,1595448726#u32⟩⟩) := JFr_EncodedCell.parser cell006 limbs006 encoded006
#print axioms parser006
def cell007 : Array U8 16#usize := ⟨[135#u8,197#u8,79#u8,50#u8,44#u8,170#u8,72#u8,108#u8,54#u8,5#u8,15#u8,101#u8,7#u8,201#u8,91#u8,35#u8],by rfl⟩
def limbs007 : QM31Limbs := ![⟨844088711,by change 844088711<2147483647;omega⟩,⟨1816701484,by change 1816701484<2147483647;omega⟩,⟨1695483190,by change 1695483190<2147483647;omega⟩,⟨593217799,by change 593217799<2147483647;omega⟩]
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
    ok (some ⟨⟨844088711#u32,1816701484#u32⟩,⟨1695483190#u32,593217799#u32⟩⟩) := JFr_EncodedCell.parser cell007 limbs007 encoded007
#print axioms parser007
def cell008 : Array U8 16#usize := ⟨[205#u8,250#u8,207#u8,104#u8,66#u8,80#u8,5#u8,102#u8,105#u8,34#u8,63#u8,115#u8,226#u8,98#u8,216#u8,94#u8],by rfl⟩
def limbs008 : QM31Limbs := ![⟨1758460621,by change 1758460621<2147483647;omega⟩,⟨1711624258,by change 1711624258<2147483647;omega⟩,⟨1933517417,by change 1933517417<2147483647;omega⟩,⟨1591239394,by change 1591239394<2147483647;omega⟩]
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
    ok (some ⟨⟨1758460621#u32,1711624258#u32⟩,⟨1933517417#u32,1591239394#u32⟩⟩) := JFr_EncodedCell.parser cell008 limbs008 encoded008
#print axioms parser008
def cell009 : Array U8 16#usize := ⟨[88#u8,133#u8,77#u8,106#u8,222#u8,80#u8,65#u8,120#u8,244#u8,137#u8,93#u8,112#u8,8#u8,157#u8,9#u8,16#u8],by rfl⟩
def limbs009 : QM31Limbs := ![⟨1783465304,by change 1783465304<2147483647;omega⟩,⟨2017546462,by change 2017546462<2147483647;omega⟩,⟨1885178356,by change 1885178356<2147483647;omega⟩,⟨269065480,by change 269065480<2147483647;omega⟩]
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
    ok (some ⟨⟨1783465304#u32,2017546462#u32⟩,⟨1885178356#u32,269065480#u32⟩⟩) := JFr_EncodedCell.parser cell009 limbs009 encoded009
#print axioms parser009
def cell010 : Array U8 16#usize := ⟨[246#u8,128#u8,114#u8,80#u8,29#u8,194#u8,185#u8,12#u8,116#u8,5#u8,200#u8,7#u8,5#u8,255#u8,118#u8,69#u8],by rfl⟩
def limbs010 : QM31Limbs := ![⟨1349681398,by change 1349681398<2147483647;omega⟩,⟨213500445,by change 213500445<2147483647;omega⟩,⟨130549108,by change 130549108<2147483647;omega⟩,⟨1165426437,by change 1165426437<2147483647;omega⟩]
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
    ok (some ⟨⟨1349681398#u32,213500445#u32⟩,⟨130549108#u32,1165426437#u32⟩⟩) := JFr_EncodedCell.parser cell010 limbs010 encoded010
#print axioms parser010
def cell011 : Array U8 16#usize := ⟨[100#u8,235#u8,164#u8,6#u8,82#u8,233#u8,94#u8,120#u8,36#u8,101#u8,175#u8,11#u8,113#u8,16#u8,29#u8,27#u8],by rfl⟩
def limbs011 : QM31Limbs := ![⟨111471460,by change 111471460<2147483647;omega⟩,⟨2019486034,by change 2019486034<2147483647;omega⟩,⟨196044068,by change 196044068<2147483647;omega⟩,⟨454889585,by change 454889585<2147483647;omega⟩]
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
    ok (some ⟨⟨111471460#u32,2019486034#u32⟩,⟨196044068#u32,454889585#u32⟩⟩) := JFr_EncodedCell.parser cell011 limbs011 encoded011
#print axioms parser011
def cell012 : Array U8 16#usize := ⟨[205#u8,19#u8,211#u8,82#u8,158#u8,229#u8,64#u8,29#u8,130#u8,253#u8,174#u8,29#u8,86#u8,190#u8,153#u8,31#u8],by rfl⟩
def limbs012 : QM31Limbs := ![⟨1389564877,by change 1389564877<2147483647;omega⟩,⟨490792350,by change 490792350<2147483647;omega⟩,⟨498007426,by change 498007426<2147483647;omega⟩,⟨530169430,by change 530169430<2147483647;omega⟩]
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
    ok (some ⟨⟨1389564877#u32,490792350#u32⟩,⟨498007426#u32,530169430#u32⟩⟩) := JFr_EncodedCell.parser cell012 limbs012 encoded012
#print axioms parser012
def cell013 : Array U8 16#usize := ⟨[150#u8,26#u8,211#u8,57#u8,29#u8,75#u8,16#u8,21#u8,184#u8,154#u8,131#u8,39#u8,55#u8,147#u8,189#u8,86#u8],by rfl⟩
def limbs013 : QM31Limbs := ![⟨970136214,by change 970136214<2147483647;omega⟩,⟨353389341,by change 353389341<2147483647;omega⟩,⟨662936248,by change 662936248<2147483647;omega⟩,⟨1455264567,by change 1455264567<2147483647;omega⟩]
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
    ok (some ⟨⟨970136214#u32,353389341#u32⟩,⟨662936248#u32,1455264567#u32⟩⟩) := JFr_EncodedCell.parser cell013 limbs013 encoded013
#print axioms parser013
def cell014 : Array U8 16#usize := ⟨[205#u8,209#u8,117#u8,52#u8,47#u8,127#u8,222#u8,63#u8,124#u8,133#u8,255#u8,111#u8,164#u8,90#u8,32#u8,79#u8],by rfl⟩
def limbs014 : QM31Limbs := ![⟨880136653,by change 880136653<2147483647;omega⟩,⟨1071546159,by change 1071546159<2147483647;omega⟩,⟨1879016828,by change 1879016828<2147483647;omega⟩,⟨1327520420,by change 1327520420<2147483647;omega⟩]
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
    ok (some ⟨⟨880136653#u32,1071546159#u32⟩,⟨1879016828#u32,1327520420#u32⟩⟩) := JFr_EncodedCell.parser cell014 limbs014 encoded014
#print axioms parser014
def cell015 : Array U8 16#usize := ⟨[30#u8,191#u8,249#u8,114#u8,146#u8,15#u8,196#u8,100#u8,119#u8,181#u8,25#u8,19#u8,124#u8,113#u8,145#u8,90#u8],by rfl⟩
def limbs015 : QM31Limbs := ![⟨1928970014,by change 1928970014<2147483647;omega⟩,⟨1690570642,by change 1690570642<2147483647;omega⟩,⟨320451959,by change 320451959<2147483647;omega⟩,⟨1519481212,by change 1519481212<2147483647;omega⟩]
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
    ok (some ⟨⟨1928970014#u32,1690570642#u32⟩,⟨320451959#u32,1519481212#u32⟩⟩) := JFr_EncodedCell.parser cell015 limbs015 encoded015
#print axioms parser015
def cell016 : Array U8 16#usize := ⟨[0#u8,119#u8,149#u8,28#u8,152#u8,103#u8,243#u8,18#u8,37#u8,144#u8,60#u8,18#u8,119#u8,233#u8,223#u8,85#u8],by rfl⟩
def limbs016 : QM31Limbs := ![⟨479557376,by change 479557376<2147483647;omega⟩,⟨317941656,by change 317941656<2147483647;omega⟩,⟨305958949,by change 305958949<2147483647;omega⟩,⟨1440737655,by change 1440737655<2147483647;omega⟩]
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
    ok (some ⟨⟨479557376#u32,317941656#u32⟩,⟨305958949#u32,1440737655#u32⟩⟩) := JFr_EncodedCell.parser cell016 limbs016 encoded016
#print axioms parser016
def cell017 : Array U8 16#usize := ⟨[41#u8,161#u8,237#u8,68#u8,172#u8,109#u8,69#u8,112#u8,237#u8,11#u8,115#u8,104#u8,49#u8,162#u8,218#u8,123#u8],by rfl⟩
def limbs017 : QM31Limbs := ![⟨1156423977,by change 1156423977<2147483647;omega⟩,⟨1883598252,by change 1883598252<2147483647;omega⟩,⟨1752370157,by change 1752370157<2147483647;omega⟩,⟨2077925937,by change 2077925937<2147483647;omega⟩]
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
    ok (some ⟨⟨1156423977#u32,1883598252#u32⟩,⟨1752370157#u32,2077925937#u32⟩⟩) := JFr_EncodedCell.parser cell017 limbs017 encoded017
#print axioms parser017
def cell018 : Array U8 16#usize := ⟨[105#u8,9#u8,198#u8,22#u8,202#u8,243#u8,125#u8,82#u8,213#u8,26#u8,54#u8,65#u8,69#u8,202#u8,22#u8,65#u8],by rfl⟩
def limbs018 : QM31Limbs := ![⟨382077289,by change 382077289<2147483647;omega⟩,⟨1383986122,by change 1383986122<2147483647;omega⟩,⟨1094064853,by change 1094064853<2147483647;omega⟩,⟨1092012613,by change 1092012613<2147483647;omega⟩]
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
    ok (some ⟨⟨382077289#u32,1383986122#u32⟩,⟨1094064853#u32,1092012613#u32⟩⟩) := JFr_EncodedCell.parser cell018 limbs018 encoded018
#print axioms parser018
def cell019 : Array U8 16#usize := ⟨[13#u8,200#u8,82#u8,9#u8,9#u8,87#u8,201#u8,45#u8,159#u8,156#u8,73#u8,27#u8,43#u8,2#u8,123#u8,126#u8],by rfl⟩
def limbs019 : QM31Limbs := ![⟨156420109,by change 156420109<2147483647;omega⟩,⟨768169737,by change 768169737<2147483647;omega⟩,⟨457809055,by change 457809055<2147483647;omega⟩,⟨2121990699,by change 2121990699<2147483647;omega⟩]
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
    ok (some ⟨⟨156420109#u32,768169737#u32⟩,⟨457809055#u32,2121990699#u32⟩⟩) := JFr_EncodedCell.parser cell019 limbs019 encoded019
#print axioms parser019
def cell020 : Array U8 16#usize := ⟨[245#u8,193#u8,173#u8,103#u8,186#u8,19#u8,153#u8,36#u8,37#u8,245#u8,106#u8,0#u8,179#u8,116#u8,170#u8,61#u8],by rfl⟩
def limbs020 : QM31Limbs := ![⟨1739440629,by change 1739440629<2147483647;omega⟩,⟨614011834,by change 614011834<2147483647;omega⟩,⟨7009573,by change 7009573<2147483647;omega⟩,⟨1034581171,by change 1034581171<2147483647;omega⟩]
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
    ok (some ⟨⟨1739440629#u32,614011834#u32⟩,⟨7009573#u32,1034581171#u32⟩⟩) := JFr_EncodedCell.parser cell020 limbs020 encoded020
#print axioms parser020
def cell021 : Array U8 16#usize := ⟨[45#u8,122#u8,176#u8,121#u8,162#u8,212#u8,136#u8,50#u8,3#u8,61#u8,55#u8,101#u8,133#u8,200#u8,203#u8,100#u8],by rfl⟩
def limbs021 : QM31Limbs := ![⟨2041608749,by change 2041608749<2147483647;omega⟩,⟨847828130,by change 847828130<2147483647;omega⟩,⟨1698118915,by change 1698118915<2147483647;omega⟩,⟨1691076741,by change 1691076741<2147483647;omega⟩]
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
    ok (some ⟨⟨2041608749#u32,847828130#u32⟩,⟨1698118915#u32,1691076741#u32⟩⟩) := JFr_EncodedCell.parser cell021 limbs021 encoded021
#print axioms parser021
def cell022 : Array U8 16#usize := ⟨[212#u8,196#u8,122#u8,108#u8,70#u8,229#u8,208#u8,105#u8,18#u8,202#u8,66#u8,111#u8,159#u8,11#u8,94#u8,92#u8],by rfl⟩
def limbs022 : QM31Limbs := ![⟨1819985108,by change 1819985108<2147483647;omega⟩,⟨1775297862,by change 1775297862<2147483647;omega⟩,⟨1866648082,by change 1866648082<2147483647;omega⟩,⟨1549667231,by change 1549667231<2147483647;omega⟩]
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
    ok (some ⟨⟨1819985108#u32,1775297862#u32⟩,⟨1866648082#u32,1549667231#u32⟩⟩) := JFr_EncodedCell.parser cell022 limbs022 encoded022
#print axioms parser022
def cell023 : Array U8 16#usize := ⟨[140#u8,136#u8,85#u8,34#u8,182#u8,154#u8,211#u8,116#u8,99#u8,156#u8,229#u8,15#u8,240#u8,133#u8,226#u8,80#u8],by rfl⟩
def limbs023 : QM31Limbs := ![⟨576030860,by change 576030860<2147483647;omega⟩,⟨1960024758,by change 1960024758<2147483647;omega⟩,⟨266706019,by change 266706019<2147483647;omega⟩,⟨1357022704,by change 1357022704<2147483647;omega⟩]
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
    ok (some ⟨⟨576030860#u32,1960024758#u32⟩,⟨266706019#u32,1357022704#u32⟩⟩) := JFr_EncodedCell.parser cell023 limbs023 encoded023
#print axioms parser023
def cell024 : Array U8 16#usize := ⟨[68#u8,246#u8,99#u8,2#u8,224#u8,117#u8,192#u8,93#u8,180#u8,8#u8,73#u8,67#u8,66#u8,56#u8,141#u8,86#u8],by rfl⟩
def limbs024 : QM31Limbs := ![⟨40105540,by change 40105540<2147483647;omega⟩,⟨1572894176,by change 1572894176<2147483647;omega⟩,⟨1128859828,by change 1128859828<2147483647;omega⟩,⟨1452095554,by change 1452095554<2147483647;omega⟩]
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
    ok (some ⟨⟨40105540#u32,1572894176#u32⟩,⟨1128859828#u32,1452095554#u32⟩⟩) := JFr_EncodedCell.parser cell024 limbs024 encoded024
#print axioms parser024
def cell025 : Array U8 16#usize := ⟨[237#u8,207#u8,227#u8,1#u8,147#u8,132#u8,11#u8,68#u8,82#u8,253#u8,185#u8,92#u8,127#u8,77#u8,67#u8,40#u8],by rfl⟩
def limbs025 : QM31Limbs := ![⟨31707117,by change 31707117<2147483647;omega⟩,⟨1141605523,by change 1141605523<2147483647;omega⟩,⟨1555692882,by change 1555692882<2147483647;omega⟩,⟨675499391,by change 675499391<2147483647;omega⟩]
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
    ok (some ⟨⟨31707117#u32,1141605523#u32⟩,⟨1555692882#u32,675499391#u32⟩⟩) := JFr_EncodedCell.parser cell025 limbs025 encoded025
#print axioms parser025
def cell026 : Array U8 16#usize := ⟨[28#u8,184#u8,153#u8,90#u8,58#u8,166#u8,150#u8,117#u8,88#u8,30#u8,185#u8,12#u8,147#u8,141#u8,157#u8,93#u8],by rfl⟩
def limbs026 : QM31Limbs := ![⟨1520023580,by change 1520023580<2147483647;omega⟩,⟨1972807226,by change 1972807226<2147483647;omega⟩,⟨213458520,by change 213458520<2147483647;omega⟩,⟨1570606483,by change 1570606483<2147483647;omega⟩]
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
    ok (some ⟨⟨1520023580#u32,1972807226#u32⟩,⟨213458520#u32,1570606483#u32⟩⟩) := JFr_EncodedCell.parser cell026 limbs026 encoded026
#print axioms parser026
def cell027 : Array U8 16#usize := ⟨[35#u8,234#u8,16#u8,50#u8,254#u8,61#u8,15#u8,83#u8,165#u8,230#u8,124#u8,86#u8,125#u8,161#u8,85#u8,29#u8],by rfl⟩
def limbs027 : QM31Limbs := ![⟨839969315,by change 839969315<2147483647;omega⟩,⟨1393507838,by change 1393507838<2147483647;omega⟩,⟨1451026085,by change 1451026085<2147483647;omega⟩,⟨492151165,by change 492151165<2147483647;omega⟩]
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
    ok (some ⟨⟨839969315#u32,1393507838#u32⟩,⟨1451026085#u32,492151165#u32⟩⟩) := JFr_EncodedCell.parser cell027 limbs027 encoded027
#print axioms parser027
def cell028 : Array U8 16#usize := ⟨[134#u8,136#u8,199#u8,95#u8,133#u8,116#u8,35#u8,66#u8,163#u8,48#u8,244#u8,16#u8,193#u8,10#u8,195#u8,92#u8],by rfl⟩
def limbs028 : QM31Limbs := ![⟨1606912134,by change 1606912134<2147483647;omega⟩,⟨1109619845,by change 1109619845<2147483647;omega⟩,⟨284438691,by change 284438691<2147483647;omega⟩,⟨1556286145,by change 1556286145<2147483647;omega⟩]
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
    ok (some ⟨⟨1606912134#u32,1109619845#u32⟩,⟨284438691#u32,1556286145#u32⟩⟩) := JFr_EncodedCell.parser cell028 limbs028 encoded028
#print axioms parser028
end AspisR1.JFu_ClaimsData
