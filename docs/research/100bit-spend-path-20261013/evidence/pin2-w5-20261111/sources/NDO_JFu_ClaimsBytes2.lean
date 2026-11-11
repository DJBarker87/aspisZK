import NDO_JFu_ClaimsData
set_option autoImplicit false
namespace AspisR1.JFu_ClaimsData
open Aeneas Aeneas.Std Result RetainedFieldByteCodec
open AspisR1PublicPreparation AspisS1ExtractedRoundChildren
open JFu_Q25Source.Input
def cell058 : Array U8 16#usize := ⟨[124#u8,180#u8,126#u8,4#u8,183#u8,46#u8,68#u8,102#u8,109#u8,16#u8,215#u8,46#u8,179#u8,169#u8,252#u8,108#u8],by rfl⟩
def limbs058 : QM31Limbs := ![⟨75412604,by change 75412604<2147483647;omega⟩,⟨1715744439,by change 1715744439<2147483647;omega⟩,⟨785846381,by change 785846381<2147483647;omega⟩,⟨1828497843,by change 1828497843<2147483647;omega⟩]
theorem window058 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*58)).take 16=cell058.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*58)).take 16=cell058.val
  rw [JFu_FlatWindow.source chunks lengths 58 (by change 58<116;omega)]
  rfl
#print axioms window058
theorem encoded058 : CandidateParserByteOrder.arrayBytes16 cell058=encodeQM31LE limbs058 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded058
theorem parser058 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell058)=
    ok (some ⟨⟨75412604#u32,1715744439#u32⟩,⟨785846381#u32,1828497843#u32⟩⟩) := JFr_EncodedCell.parser cell058 limbs058 encoded058
#print axioms parser058
def cell059 : Array U8 16#usize := ⟨[40#u8,144#u8,120#u8,74#u8,136#u8,109#u8,99#u8,78#u8,211#u8,105#u8,194#u8,127#u8,78#u8,37#u8,232#u8,121#u8],by rfl⟩
def limbs059 : QM31Limbs := ![⟨1249415208,by change 1249415208<2147483647;omega⟩,⟨1315138952,by change 1315138952<2147483647;omega⟩,⟨2143447507,by change 2143447507<2147483647;omega⟩,⟨2045257038,by change 2045257038<2147483647;omega⟩]
theorem window059 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*59)).take 16=cell059.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*59)).take 16=cell059.val
  rw [JFu_FlatWindow.source chunks lengths 59 (by change 59<116;omega)]
  rfl
#print axioms window059
theorem encoded059 : CandidateParserByteOrder.arrayBytes16 cell059=encodeQM31LE limbs059 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded059
theorem parser059 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell059)=
    ok (some ⟨⟨1249415208#u32,1315138952#u32⟩,⟨2143447507#u32,2045257038#u32⟩⟩) := JFr_EncodedCell.parser cell059 limbs059 encoded059
#print axioms parser059
def cell060 : Array U8 16#usize := ⟨[35#u8,34#u8,175#u8,88#u8,32#u8,125#u8,64#u8,111#u8,160#u8,154#u8,109#u8,104#u8,137#u8,191#u8,165#u8,61#u8],by rfl⟩
def limbs060 : QM31Limbs := ![⟨1487872547,by change 1487872547<2147483647;omega⟩,⟨1866497312,by change 1866497312<2147483647;omega⟩,⟨1752013472,by change 1752013472<2147483647;omega⟩,⟨1034272649,by change 1034272649<2147483647;omega⟩]
theorem window060 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*60)).take 16=cell060.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*60)).take 16=cell060.val
  rw [JFu_FlatWindow.source chunks lengths 60 (by change 60<116;omega)]
  rfl
#print axioms window060
theorem encoded060 : CandidateParserByteOrder.arrayBytes16 cell060=encodeQM31LE limbs060 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded060
theorem parser060 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell060)=
    ok (some ⟨⟨1487872547#u32,1866497312#u32⟩,⟨1752013472#u32,1034272649#u32⟩⟩) := JFr_EncodedCell.parser cell060 limbs060 encoded060
#print axioms parser060
def cell061 : Array U8 16#usize := ⟨[232#u8,183#u8,37#u8,11#u8,202#u8,253#u8,79#u8,68#u8,87#u8,194#u8,132#u8,123#u8,149#u8,244#u8,205#u8,26#u8],by rfl⟩
def limbs061 : QM31Limbs := ![⟨187021288,by change 187021288<2147483647;omega⟩,⟨1146093002,by change 1146093002<2147483647;omega⟩,⟨2072298071,by change 2072298071<2147483647;omega⟩,⟨449705109,by change 449705109<2147483647;omega⟩]
theorem window061 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*61)).take 16=cell061.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*61)).take 16=cell061.val
  rw [JFu_FlatWindow.source chunks lengths 61 (by change 61<116;omega)]
  rfl
#print axioms window061
theorem encoded061 : CandidateParserByteOrder.arrayBytes16 cell061=encodeQM31LE limbs061 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded061
theorem parser061 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell061)=
    ok (some ⟨⟨187021288#u32,1146093002#u32⟩,⟨2072298071#u32,449705109#u32⟩⟩) := JFr_EncodedCell.parser cell061 limbs061 encoded061
#print axioms parser061
def cell062 : Array U8 16#usize := ⟨[54#u8,75#u8,228#u8,1#u8,188#u8,109#u8,5#u8,47#u8,215#u8,32#u8,48#u8,7#u8,252#u8,131#u8,142#u8,74#u8],by rfl⟩
def limbs062 : QM31Limbs := ![⟨31738678,by change 31738678<2147483647;omega⟩,⟨788884924,by change 788884924<2147483647;omega⟩,⟨120594647,by change 120594647<2147483647;omega⟩,⟨1250853884,by change 1250853884<2147483647;omega⟩]
theorem window062 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*62)).take 16=cell062.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*62)).take 16=cell062.val
  rw [JFu_FlatWindow.source chunks lengths 62 (by change 62<116;omega)]
  rfl
#print axioms window062
theorem encoded062 : CandidateParserByteOrder.arrayBytes16 cell062=encodeQM31LE limbs062 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded062
theorem parser062 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell062)=
    ok (some ⟨⟨31738678#u32,788884924#u32⟩,⟨120594647#u32,1250853884#u32⟩⟩) := JFr_EncodedCell.parser cell062 limbs062 encoded062
#print axioms parser062
def cell063 : Array U8 16#usize := ⟨[65#u8,186#u8,61#u8,100#u8,230#u8,114#u8,2#u8,76#u8,96#u8,134#u8,40#u8,21#u8,87#u8,2#u8,214#u8,49#u8],by rfl⟩
def limbs063 : QM31Limbs := ![⟨1681766977,by change 1681766977<2147483647;omega⟩,⟨1275228902,by change 1275228902<2147483647;omega⟩,⟨354977376,by change 354977376<2147483647;omega⟩,⟨836108887,by change 836108887<2147483647;omega⟩]
theorem window063 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*63)).take 16=cell063.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*63)).take 16=cell063.val
  rw [JFu_FlatWindow.source chunks lengths 63 (by change 63<116;omega)]
  rfl
#print axioms window063
theorem encoded063 : CandidateParserByteOrder.arrayBytes16 cell063=encodeQM31LE limbs063 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded063
theorem parser063 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell063)=
    ok (some ⟨⟨1681766977#u32,1275228902#u32⟩,⟨354977376#u32,836108887#u32⟩⟩) := JFr_EncodedCell.parser cell063 limbs063 encoded063
#print axioms parser063
def cell064 : Array U8 16#usize := ⟨[36#u8,33#u8,131#u8,79#u8,127#u8,136#u8,233#u8,98#u8,57#u8,34#u8,126#u8,94#u8,50#u8,198#u8,149#u8,19#u8],by rfl⟩
def limbs064 : QM31Limbs := ![⟨1333993764,by change 1333993764<2147483647;omega⟩,⟨1659471999,by change 1659471999<2147483647;omega⟩,⟨1585324601,by change 1585324601<2147483647;omega⟩,⟨328582706,by change 328582706<2147483647;omega⟩]
theorem window064 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*64)).take 16=cell064.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*64)).take 16=cell064.val
  rw [JFu_FlatWindow.source chunks lengths 64 (by change 64<116;omega)]
  rfl
#print axioms window064
theorem encoded064 : CandidateParserByteOrder.arrayBytes16 cell064=encodeQM31LE limbs064 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded064
theorem parser064 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell064)=
    ok (some ⟨⟨1333993764#u32,1659471999#u32⟩,⟨1585324601#u32,328582706#u32⟩⟩) := JFr_EncodedCell.parser cell064 limbs064 encoded064
#print axioms parser064
def cell065 : Array U8 16#usize := ⟨[43#u8,68#u8,51#u8,32#u8,235#u8,111#u8,16#u8,94#u8,152#u8,237#u8,59#u8,122#u8,158#u8,68#u8,166#u8,33#u8],by rfl⟩
def limbs065 : QM31Limbs := ![⟨540230699,by change 540230699<2147483647;omega⟩,⟨1578135531,by change 1578135531<2147483647;omega⟩,⟨2050747800,by change 2050747800<2147483647;omega⟩,⟨564544670,by change 564544670<2147483647;omega⟩]
theorem window065 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*65)).take 16=cell065.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*65)).take 16=cell065.val
  rw [JFu_FlatWindow.source chunks lengths 65 (by change 65<116;omega)]
  rfl
#print axioms window065
theorem encoded065 : CandidateParserByteOrder.arrayBytes16 cell065=encodeQM31LE limbs065 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded065
theorem parser065 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell065)=
    ok (some ⟨⟨540230699#u32,1578135531#u32⟩,⟨2050747800#u32,564544670#u32⟩⟩) := JFr_EncodedCell.parser cell065 limbs065 encoded065
#print axioms parser065
def cell066 : Array U8 16#usize := ⟨[43#u8,200#u8,236#u8,21#u8,165#u8,111#u8,182#u8,60#u8,61#u8,151#u8,50#u8,61#u8,79#u8,99#u8,199#u8,85#u8],by rfl⟩
def limbs066 : QM31Limbs := ![⟨367839275,by change 367839275<2147483647;omega⟩,⟨1018589093,by change 1018589093<2147483647;omega⟩,⟨1026725693,by change 1026725693<2147483647;omega⟩,⟨1439130447,by change 1439130447<2147483647;omega⟩]
theorem window066 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*66)).take 16=cell066.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*66)).take 16=cell066.val
  rw [JFu_FlatWindow.source chunks lengths 66 (by change 66<116;omega)]
  rfl
#print axioms window066
theorem encoded066 : CandidateParserByteOrder.arrayBytes16 cell066=encodeQM31LE limbs066 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded066
theorem parser066 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell066)=
    ok (some ⟨⟨367839275#u32,1018589093#u32⟩,⟨1026725693#u32,1439130447#u32⟩⟩) := JFr_EncodedCell.parser cell066 limbs066 encoded066
#print axioms parser066
def cell067 : Array U8 16#usize := ⟨[227#u8,49#u8,116#u8,20#u8,217#u8,190#u8,2#u8,75#u8,207#u8,115#u8,201#u8,40#u8,95#u8,169#u8,186#u8,20#u8],by rfl⟩
def limbs067 : QM31Limbs := ![⟨343159267,by change 343159267<2147483647;omega⟩,⟨1258471129,by change 1258471129<2147483647;omega⟩,⟨684291023,by change 684291023<2147483647;omega⟩,⟨347777375,by change 347777375<2147483647;omega⟩]
theorem window067 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*67)).take 16=cell067.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*67)).take 16=cell067.val
  rw [JFu_FlatWindow.source chunks lengths 67 (by change 67<116;omega)]
  rfl
#print axioms window067
theorem encoded067 : CandidateParserByteOrder.arrayBytes16 cell067=encodeQM31LE limbs067 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded067
theorem parser067 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell067)=
    ok (some ⟨⟨343159267#u32,1258471129#u32⟩,⟨684291023#u32,347777375#u32⟩⟩) := JFr_EncodedCell.parser cell067 limbs067 encoded067
#print axioms parser067
def cell068 : Array U8 16#usize := ⟨[201#u8,252#u8,74#u8,98#u8,89#u8,130#u8,134#u8,97#u8,6#u8,127#u8,218#u8,47#u8,9#u8,234#u8,233#u8,113#u8],by rfl⟩
def limbs068 : QM31Limbs := ![⟨1649081545,by change 1649081545<2147483647;omega⟩,⟨1636205145,by change 1636205145<2147483647;omega⟩,⟨802848518,by change 802848518<2147483647;omega⟩,⟨1911155209,by change 1911155209<2147483647;omega⟩]
theorem window068 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*68)).take 16=cell068.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*68)).take 16=cell068.val
  rw [JFu_FlatWindow.source chunks lengths 68 (by change 68<116;omega)]
  rfl
#print axioms window068
theorem encoded068 : CandidateParserByteOrder.arrayBytes16 cell068=encodeQM31LE limbs068 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded068
theorem parser068 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell068)=
    ok (some ⟨⟨1649081545#u32,1636205145#u32⟩,⟨802848518#u32,1911155209#u32⟩⟩) := JFr_EncodedCell.parser cell068 limbs068 encoded068
#print axioms parser068
def cell069 : Array U8 16#usize := ⟨[108#u8,124#u8,172#u8,113#u8,180#u8,89#u8,181#u8,94#u8,8#u8,43#u8,197#u8,118#u8,155#u8,63#u8,29#u8,82#u8],by rfl⟩
def limbs069 : QM31Limbs := ![⟨1907129452,by change 1907129452<2147483647;omega⟩,⟨1588943284,by change 1588943284<2147483647;omega⟩,⟨1992633096,by change 1992633096<2147483647;omega⟩,⟨1377648539,by change 1377648539<2147483647;omega⟩]
theorem window069 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*69)).take 16=cell069.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*69)).take 16=cell069.val
  rw [JFu_FlatWindow.source chunks lengths 69 (by change 69<116;omega)]
  rfl
#print axioms window069
theorem encoded069 : CandidateParserByteOrder.arrayBytes16 cell069=encodeQM31LE limbs069 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded069
theorem parser069 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell069)=
    ok (some ⟨⟨1907129452#u32,1588943284#u32⟩,⟨1992633096#u32,1377648539#u32⟩⟩) := JFr_EncodedCell.parser cell069 limbs069 encoded069
#print axioms parser069
def cell070 : Array U8 16#usize := ⟨[139#u8,6#u8,7#u8,41#u8,154#u8,138#u8,127#u8,25#u8,225#u8,112#u8,245#u8,51#u8,207#u8,185#u8,129#u8,17#u8],by rfl⟩
def limbs070 : QM31Limbs := ![⟨688326283,by change 688326283<2147483647;omega⟩,⟨427788954,by change 427788954<2147483647;omega⟩,⟨871723233,by change 871723233<2147483647;omega⟩,⟨293714383,by change 293714383<2147483647;omega⟩]
theorem window070 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*70)).take 16=cell070.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*70)).take 16=cell070.val
  rw [JFu_FlatWindow.source chunks lengths 70 (by change 70<116;omega)]
  rfl
#print axioms window070
theorem encoded070 : CandidateParserByteOrder.arrayBytes16 cell070=encodeQM31LE limbs070 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded070
theorem parser070 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell070)=
    ok (some ⟨⟨688326283#u32,427788954#u32⟩,⟨871723233#u32,293714383#u32⟩⟩) := JFr_EncodedCell.parser cell070 limbs070 encoded070
#print axioms parser070
def cell071 : Array U8 16#usize := ⟨[156#u8,126#u8,1#u8,15#u8,51#u8,164#u8,122#u8,82#u8,247#u8,155#u8,4#u8,34#u8,23#u8,170#u8,206#u8,80#u8],by rfl⟩
def limbs071 : QM31Limbs := ![⟨251756188,by change 251756188<2147483647;omega⟩,⟨1383769139,by change 1383769139<2147483647;omega⟩,⟨570727415,by change 570727415<2147483647;omega⟩,⟨1355721239,by change 1355721239<2147483647;omega⟩]
theorem window071 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*71)).take 16=cell071.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*71)).take 16=cell071.val
  rw [JFu_FlatWindow.source chunks lengths 71 (by change 71<116;omega)]
  rfl
#print axioms window071
theorem encoded071 : CandidateParserByteOrder.arrayBytes16 cell071=encodeQM31LE limbs071 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded071
theorem parser071 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell071)=
    ok (some ⟨⟨251756188#u32,1383769139#u32⟩,⟨570727415#u32,1355721239#u32⟩⟩) := JFr_EncodedCell.parser cell071 limbs071 encoded071
#print axioms parser071
def cell072 : Array U8 16#usize := ⟨[56#u8,97#u8,171#u8,77#u8,116#u8,31#u8,129#u8,82#u8,205#u8,166#u8,106#u8,81#u8,222#u8,23#u8,61#u8,56#u8],by rfl⟩
def limbs072 : QM31Limbs := ![⟨1303077176,by change 1303077176<2147483647;omega⟩,⟨1384193908,by change 1384193908<2147483647;omega⟩,⟨1365944013,by change 1365944013<2147483647;omega⟩,⟨943527902,by change 943527902<2147483647;omega⟩]
theorem window072 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*72)).take 16=cell072.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*72)).take 16=cell072.val
  rw [JFu_FlatWindow.source chunks lengths 72 (by change 72<116;omega)]
  rfl
#print axioms window072
theorem encoded072 : CandidateParserByteOrder.arrayBytes16 cell072=encodeQM31LE limbs072 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded072
theorem parser072 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell072)=
    ok (some ⟨⟨1303077176#u32,1384193908#u32⟩,⟨1365944013#u32,943527902#u32⟩⟩) := JFr_EncodedCell.parser cell072 limbs072 encoded072
#print axioms parser072
def cell073 : Array U8 16#usize := ⟨[118#u8,211#u8,100#u8,109#u8,174#u8,86#u8,220#u8,99#u8,142#u8,69#u8,64#u8,113#u8,245#u8,106#u8,223#u8,34#u8],by rfl⟩
def limbs073 : QM31Limbs := ![⟨1835324278,by change 1835324278<2147483647;omega⟩,⟨1675384494,by change 1675384494<2147483647;omega⟩,⟨1900037518,by change 1900037518<2147483647;omega⟩,⟨585067253,by change 585067253<2147483647;omega⟩]
theorem window073 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*73)).take 16=cell073.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*73)).take 16=cell073.val
  rw [JFu_FlatWindow.source chunks lengths 73 (by change 73<116;omega)]
  rfl
#print axioms window073
theorem encoded073 : CandidateParserByteOrder.arrayBytes16 cell073=encodeQM31LE limbs073 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded073
theorem parser073 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell073)=
    ok (some ⟨⟨1835324278#u32,1675384494#u32⟩,⟨1900037518#u32,585067253#u32⟩⟩) := JFr_EncodedCell.parser cell073 limbs073 encoded073
#print axioms parser073
def cell074 : Array U8 16#usize := ⟨[107#u8,237#u8,130#u8,14#u8,29#u8,35#u8,56#u8,6#u8,59#u8,79#u8,64#u8,65#u8,187#u8,134#u8,122#u8,120#u8],by rfl⟩
def limbs074 : QM31Limbs := ![⟨243461483,by change 243461483<2147483647;omega⟩,⟨104342301,by change 104342301<2147483647;omega⟩,⟨1094733627,by change 1094733627<2147483647;omega⟩,⟨2021295803,by change 2021295803<2147483647;omega⟩]
theorem window074 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*74)).take 16=cell074.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*74)).take 16=cell074.val
  rw [JFu_FlatWindow.source chunks lengths 74 (by change 74<116;omega)]
  rfl
#print axioms window074
theorem encoded074 : CandidateParserByteOrder.arrayBytes16 cell074=encodeQM31LE limbs074 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded074
theorem parser074 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell074)=
    ok (some ⟨⟨243461483#u32,104342301#u32⟩,⟨1094733627#u32,2021295803#u32⟩⟩) := JFr_EncodedCell.parser cell074 limbs074 encoded074
#print axioms parser074
def cell075 : Array U8 16#usize := ⟨[49#u8,178#u8,220#u8,19#u8,141#u8,122#u8,136#u8,54#u8,172#u8,96#u8,153#u8,124#u8,81#u8,151#u8,111#u8,82#u8],by rfl⟩
def limbs075 : QM31Limbs := ![⟨333230641,by change 333230641<2147483647;omega⟩,⟨914913933,by change 914913933<2147483647;omega⟩,⟨2090426540,by change 2090426540<2147483647;omega⟩,⟨1383044945,by change 1383044945<2147483647;omega⟩]
theorem window075 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*75)).take 16=cell075.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*75)).take 16=cell075.val
  rw [JFu_FlatWindow.source chunks lengths 75 (by change 75<116;omega)]
  rfl
#print axioms window075
theorem encoded075 : CandidateParserByteOrder.arrayBytes16 cell075=encodeQM31LE limbs075 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded075
theorem parser075 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell075)=
    ok (some ⟨⟨333230641#u32,914913933#u32⟩,⟨2090426540#u32,1383044945#u32⟩⟩) := JFr_EncodedCell.parser cell075 limbs075 encoded075
#print axioms parser075
def cell076 : Array U8 16#usize := ⟨[182#u8,226#u8,66#u8,99#u8,209#u8,217#u8,3#u8,7#u8,199#u8,46#u8,71#u8,24#u8,59#u8,172#u8,179#u8,78#u8],by rfl⟩
def limbs076 : QM31Limbs := ![⟨1665327798,by change 1665327798<2147483647;omega⟩,⟨117692881,by change 117692881<2147483647;omega⟩,⟨407318215,by change 407318215<2147483647;omega⟩,⟨1320397883,by change 1320397883<2147483647;omega⟩]
theorem window076 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*76)).take 16=cell076.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*76)).take 16=cell076.val
  rw [JFu_FlatWindow.source chunks lengths 76 (by change 76<116;omega)]
  rfl
#print axioms window076
theorem encoded076 : CandidateParserByteOrder.arrayBytes16 cell076=encodeQM31LE limbs076 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded076
theorem parser076 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell076)=
    ok (some ⟨⟨1665327798#u32,117692881#u32⟩,⟨407318215#u32,1320397883#u32⟩⟩) := JFr_EncodedCell.parser cell076 limbs076 encoded076
#print axioms parser076
def cell077 : Array U8 16#usize := ⟨[189#u8,231#u8,192#u8,42#u8,15#u8,210#u8,26#u8,6#u8,145#u8,94#u8,4#u8,122#u8,196#u8,30#u8,20#u8,123#u8],by rfl⟩
def limbs077 : QM31Limbs := ![⟨717285309,by change 717285309<2147483647;omega⟩,⟨102421007,by change 102421007<2147483647;omega⟩,⟨2047106705,by change 2047106705<2147483647;omega⟩,⟨2064916164,by change 2064916164<2147483647;omega⟩]
theorem window077 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*77)).take 16=cell077.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*77)).take 16=cell077.val
  rw [JFu_FlatWindow.source chunks lengths 77 (by change 77<116;omega)]
  rfl
#print axioms window077
theorem encoded077 : CandidateParserByteOrder.arrayBytes16 cell077=encodeQM31LE limbs077 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded077
theorem parser077 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell077)=
    ok (some ⟨⟨717285309#u32,102421007#u32⟩,⟨2047106705#u32,2064916164#u32⟩⟩) := JFr_EncodedCell.parser cell077 limbs077 encoded077
#print axioms parser077
def cell078 : Array U8 16#usize := ⟨[240#u8,77#u8,76#u8,61#u8,128#u8,93#u8,130#u8,99#u8,55#u8,252#u8,48#u8,25#u8,74#u8,130#u8,3#u8,69#u8],by rfl⟩
def limbs078 : QM31Limbs := ![⟨1028410864,by change 1028410864<2147483647;omega⟩,⟨1669488000,by change 1669488000<2147483647;omega⟩,⟨422640695,by change 422640695<2147483647;omega⟩,⟨1157857866,by change 1157857866<2147483647;omega⟩]
theorem window078 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*78)).take 16=cell078.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*78)).take 16=cell078.val
  rw [JFu_FlatWindow.source chunks lengths 78 (by change 78<116;omega)]
  rfl
#print axioms window078
theorem encoded078 : CandidateParserByteOrder.arrayBytes16 cell078=encodeQM31LE limbs078 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded078
theorem parser078 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell078)=
    ok (some ⟨⟨1028410864#u32,1669488000#u32⟩,⟨422640695#u32,1157857866#u32⟩⟩) := JFr_EncodedCell.parser cell078 limbs078 encoded078
#print axioms parser078
def cell079 : Array U8 16#usize := ⟨[73#u8,34#u8,164#u8,80#u8,11#u8,167#u8,170#u8,112#u8,45#u8,166#u8,110#u8,103#u8,14#u8,110#u8,130#u8,36#u8],by rfl⟩
def limbs079 : QM31Limbs := ![⟨1352933961,by change 1352933961<2147483647;omega⟩,⟨1890232075,by change 1890232075<2147483647;omega⟩,⟨1735304749,by change 1735304749<2147483647;omega⟩,⟨612527630,by change 612527630<2147483647;omega⟩]
theorem window079 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*79)).take 16=cell079.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*79)).take 16=cell079.val
  rw [JFu_FlatWindow.source chunks lengths 79 (by change 79<116;omega)]
  rfl
#print axioms window079
theorem encoded079 : CandidateParserByteOrder.arrayBytes16 cell079=encodeQM31LE limbs079 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded079
theorem parser079 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell079)=
    ok (some ⟨⟨1352933961#u32,1890232075#u32⟩,⟨1735304749#u32,612527630#u32⟩⟩) := JFr_EncodedCell.parser cell079 limbs079 encoded079
#print axioms parser079
def cell080 : Array U8 16#usize := ⟨[143#u8,191#u8,156#u8,44#u8,60#u8,202#u8,8#u8,51#u8,216#u8,244#u8,167#u8,53#u8,224#u8,26#u8,45#u8,31#u8],by rfl⟩
def limbs080 : QM31Limbs := ![⟨748470159,by change 748470159<2147483647;omega⟩,⟨856214076,by change 856214076<2147483647;omega⟩,⟨900199640,by change 900199640<2147483647;omega⟩,⟨523049696,by change 523049696<2147483647;omega⟩]
theorem window080 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*80)).take 16=cell080.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*80)).take 16=cell080.val
  rw [JFu_FlatWindow.source chunks lengths 80 (by change 80<116;omega)]
  rfl
#print axioms window080
theorem encoded080 : CandidateParserByteOrder.arrayBytes16 cell080=encodeQM31LE limbs080 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded080
theorem parser080 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell080)=
    ok (some ⟨⟨748470159#u32,856214076#u32⟩,⟨900199640#u32,523049696#u32⟩⟩) := JFr_EncodedCell.parser cell080 limbs080 encoded080
#print axioms parser080
def cell081 : Array U8 16#usize := ⟨[138#u8,46#u8,61#u8,50#u8,157#u8,84#u8,108#u8,12#u8,163#u8,208#u8,113#u8,67#u8,222#u8,122#u8,141#u8,52#u8],by rfl⟩
def limbs081 : QM31Limbs := ![⟨842870410,by change 842870410<2147483647;omega⟩,⟨208426141,by change 208426141<2147483647;omega⟩,⟨1131532451,by change 1131532451<2147483647;omega⟩,⟨881687262,by change 881687262<2147483647;omega⟩]
theorem window081 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*81)).take 16=cell081.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*81)).take 16=cell081.val
  rw [JFu_FlatWindow.source chunks lengths 81 (by change 81<116;omega)]
  rfl
#print axioms window081
theorem encoded081 : CandidateParserByteOrder.arrayBytes16 cell081=encodeQM31LE limbs081 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded081
theorem parser081 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell081)=
    ok (some ⟨⟨842870410#u32,208426141#u32⟩,⟨1131532451#u32,881687262#u32⟩⟩) := JFr_EncodedCell.parser cell081 limbs081 encoded081
#print axioms parser081
def cell082 : Array U8 16#usize := ⟨[88#u8,180#u8,5#u8,43#u8,58#u8,184#u8,227#u8,52#u8,223#u8,167#u8,17#u8,34#u8,0#u8,211#u8,197#u8,92#u8],by rfl⟩
def limbs082 : QM31Limbs := ![⟨721794136,by change 721794136<2147483647;omega⟩,⟨887339066,by change 887339066<2147483647;omega⟩,⟨571582431,by change 571582431<2147483647;omega⟩,⟨1556468480,by change 1556468480<2147483647;omega⟩]
theorem window082 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*82)).take 16=cell082.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*82)).take 16=cell082.val
  rw [JFu_FlatWindow.source chunks lengths 82 (by change 82<116;omega)]
  rfl
#print axioms window082
theorem encoded082 : CandidateParserByteOrder.arrayBytes16 cell082=encodeQM31LE limbs082 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded082
theorem parser082 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell082)=
    ok (some ⟨⟨721794136#u32,887339066#u32⟩,⟨571582431#u32,1556468480#u32⟩⟩) := JFr_EncodedCell.parser cell082 limbs082 encoded082
#print axioms parser082
def cell083 : Array U8 16#usize := ⟨[16#u8,165#u8,74#u8,9#u8,94#u8,31#u8,88#u8,123#u8,253#u8,44#u8,172#u8,109#u8,141#u8,53#u8,129#u8,66#u8],by rfl⟩
def limbs083 : QM31Limbs := ![⟨155886864,by change 155886864<2147483647;omega⟩,⟨2069372766,by change 2069372766<2147483647;omega⟩,⟨1840000253,by change 1840000253<2147483647;omega⟩,⟨1115764109,by change 1115764109<2147483647;omega⟩]
theorem window083 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*83)).take 16=cell083.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*83)).take 16=cell083.val
  rw [JFu_FlatWindow.source chunks lengths 83 (by change 83<116;omega)]
  rfl
#print axioms window083
theorem encoded083 : CandidateParserByteOrder.arrayBytes16 cell083=encodeQM31LE limbs083 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded083
theorem parser083 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell083)=
    ok (some ⟨⟨155886864#u32,2069372766#u32⟩,⟨1840000253#u32,1115764109#u32⟩⟩) := JFr_EncodedCell.parser cell083 limbs083 encoded083
#print axioms parser083
def cell084 : Array U8 16#usize := ⟨[229#u8,15#u8,93#u8,42#u8,81#u8,243#u8,252#u8,101#u8,32#u8,248#u8,38#u8,68#u8,127#u8,195#u8,54#u8,50#u8],by rfl⟩
def limbs084 : QM31Limbs := ![⟨710741989,by change 710741989<2147483647;omega⟩,⟨1711076177,by change 1711076177<2147483647;omega⟩,⟨1143404576,by change 1143404576<2147483647;omega⟩,⟨842449791,by change 842449791<2147483647;omega⟩]
theorem window084 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*84)).take 16=cell084.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*84)).take 16=cell084.val
  rw [JFu_FlatWindow.source chunks lengths 84 (by change 84<116;omega)]
  rfl
#print axioms window084
theorem encoded084 : CandidateParserByteOrder.arrayBytes16 cell084=encodeQM31LE limbs084 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded084
theorem parser084 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell084)=
    ok (some ⟨⟨710741989#u32,1711076177#u32⟩,⟨1143404576#u32,842449791#u32⟩⟩) := JFr_EncodedCell.parser cell084 limbs084 encoded084
#print axioms parser084
def cell085 : Array U8 16#usize := ⟨[233#u8,89#u8,244#u8,114#u8,75#u8,59#u8,126#u8,25#u8,83#u8,52#u8,90#u8,109#u8,30#u8,148#u8,49#u8,103#u8],by rfl⟩
def limbs085 : QM31Limbs := ![⟨1928616425,by change 1928616425<2147483647;omega⟩,⟨427703115,by change 427703115<2147483647;omega⟩,⟨1834628179,by change 1834628179<2147483647;omega⟩,⟨1731302430,by change 1731302430<2147483647;omega⟩]
theorem window085 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*85)).take 16=cell085.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*85)).take 16=cell085.val
  rw [JFu_FlatWindow.source chunks lengths 85 (by change 85<116;omega)]
  rfl
#print axioms window085
theorem encoded085 : CandidateParserByteOrder.arrayBytes16 cell085=encodeQM31LE limbs085 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded085
theorem parser085 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell085)=
    ok (some ⟨⟨1928616425#u32,427703115#u32⟩,⟨1834628179#u32,1731302430#u32⟩⟩) := JFr_EncodedCell.parser cell085 limbs085 encoded085
#print axioms parser085
def cell086 : Array U8 16#usize := ⟨[71#u8,242#u8,208#u8,83#u8,43#u8,71#u8,43#u8,86#u8,118#u8,214#u8,240#u8,123#u8,49#u8,12#u8,200#u8,12#u8],by rfl⟩
def limbs086 : QM31Limbs := ![⟨1406202439,by change 1406202439<2147483647;omega⟩,⟨1445676843,by change 1445676843<2147483647;omega⟩,⟨2079381110,by change 2079381110<2147483647;omega⟩,⟨214436913,by change 214436913<2147483647;omega⟩]
theorem window086 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*86)).take 16=cell086.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*86)).take 16=cell086.val
  rw [JFu_FlatWindow.source chunks lengths 86 (by change 86<116;omega)]
  rfl
#print axioms window086
theorem encoded086 : CandidateParserByteOrder.arrayBytes16 cell086=encodeQM31LE limbs086 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded086
theorem parser086 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell086)=
    ok (some ⟨⟨1406202439#u32,1445676843#u32⟩,⟨2079381110#u32,214436913#u32⟩⟩) := JFr_EncodedCell.parser cell086 limbs086 encoded086
#print axioms parser086
end AspisR1.JFu_ClaimsData
