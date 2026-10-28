import NDO_JFu_ClaimsData
set_option autoImplicit false
namespace AspisR1.JFu_ClaimsData
open Aeneas Aeneas.Std Result RetainedFieldByteCodec
open AspisR1PublicPreparation AspisS1ExtractedRoundChildren
open JFu_Q25Source.Input
def cell058 : Array U8 16#usize := ⟨[127#u8,252#u8,42#u8,78#u8,251#u8,176#u8,113#u8,45#u8,235#u8,9#u8,94#u8,115#u8,53#u8,252#u8,13#u8,102#u8],by rfl⟩
def limbs058 : QM31Limbs := ![⟨1311439999,by change 1311439999<2147483647;omega⟩,⟨762425595,by change 762425595<2147483647;omega⟩,⟨1935542763,by change 1935542763<2147483647;omega⟩,⟨1712192565,by change 1712192565<2147483647;omega⟩]
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
    ok (some ⟨⟨1311439999#u32,762425595#u32⟩,⟨1935542763#u32,1712192565#u32⟩⟩) := JFr_EncodedCell.parser cell058 limbs058 encoded058
#print axioms parser058
def cell059 : Array U8 16#usize := ⟨[172#u8,91#u8,37#u8,78#u8,8#u8,21#u8,196#u8,25#u8,240#u8,222#u8,4#u8,112#u8,99#u8,216#u8,106#u8,77#u8],by rfl⟩
def limbs059 : QM31Limbs := ![⟨1311071148,by change 1311071148<2147483647;omega⟩,⟨432280840,by change 432280840<2147483647;omega⟩,⟨1879367408,by change 1879367408<2147483647;omega⟩,⟨1298847843,by change 1298847843<2147483647;omega⟩]
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
    ok (some ⟨⟨1311071148#u32,432280840#u32⟩,⟨1879367408#u32,1298847843#u32⟩⟩) := JFr_EncodedCell.parser cell059 limbs059 encoded059
#print axioms parser059
def cell060 : Array U8 16#usize := ⟨[117#u8,15#u8,145#u8,87#u8,253#u8,141#u8,43#u8,101#u8,60#u8,156#u8,139#u8,96#u8,50#u8,61#u8,74#u8,18#u8],by rfl⟩
def limbs060 : QM31Limbs := ![⟨1469124469,by change 1469124469<2147483647;omega⟩,⟨1697353213,by change 1697353213<2147483647;omega⟩,⟨1619762236,by change 1619762236<2147483647;omega⟩,⟨306855218,by change 306855218<2147483647;omega⟩]
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
    ok (some ⟨⟨1469124469#u32,1697353213#u32⟩,⟨1619762236#u32,306855218#u32⟩⟩) := JFr_EncodedCell.parser cell060 limbs060 encoded060
#print axioms parser060
def cell061 : Array U8 16#usize := ⟨[176#u8,242#u8,16#u8,68#u8,138#u8,2#u8,3#u8,50#u8,56#u8,177#u8,249#u8,81#u8,244#u8,135#u8,10#u8,19#u8],by rfl⟩
def limbs061 : QM31Limbs := ![⟨1141961392,by change 1141961392<2147483647;omega⟩,⟨839058058,by change 839058058<2147483647;omega⟩,⟨1375318328,by change 1375318328<2147483647;omega⟩,⟨319457268,by change 319457268<2147483647;omega⟩]
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
    ok (some ⟨⟨1141961392#u32,839058058#u32⟩,⟨1375318328#u32,319457268#u32⟩⟩) := JFr_EncodedCell.parser cell061 limbs061 encoded061
#print axioms parser061
def cell062 : Array U8 16#usize := ⟨[12#u8,206#u8,223#u8,125#u8,186#u8,51#u8,16#u8,125#u8,76#u8,27#u8,22#u8,5#u8,29#u8,228#u8,115#u8,112#u8],by rfl⟩
def limbs062 : QM31Limbs := ![⟨2111819276,by change 2111819276<2147483647;omega⟩,⟨2098213818,by change 2098213818<2147483647;omega⟩,⟨85334860,by change 85334860<2147483647;omega⟩,⟨1886643229,by change 1886643229<2147483647;omega⟩]
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
    ok (some ⟨⟨2111819276#u32,2098213818#u32⟩,⟨85334860#u32,1886643229#u32⟩⟩) := JFr_EncodedCell.parser cell062 limbs062 encoded062
#print axioms parser062
def cell063 : Array U8 16#usize := ⟨[144#u8,199#u8,207#u8,74#u8,88#u8,202#u8,195#u8,122#u8,249#u8,234#u8,151#u8,81#u8,31#u8,203#u8,38#u8,127#u8],by rfl⟩
def limbs063 : QM31Limbs := ![⟨1255131024,by change 1255131024<2147483647;omega⟩,⟨2059651672,by change 2059651672<2147483647;omega⟩,⟨1368910585,by change 1368910585<2147483647;omega⟩,⟨2133248799,by change 2133248799<2147483647;omega⟩]
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
    ok (some ⟨⟨1255131024#u32,2059651672#u32⟩,⟨1368910585#u32,2133248799#u32⟩⟩) := JFr_EncodedCell.parser cell063 limbs063 encoded063
#print axioms parser063
def cell064 : Array U8 16#usize := ⟨[254#u8,251#u8,218#u8,44#u8,93#u8,85#u8,68#u8,28#u8,240#u8,199#u8,16#u8,71#u8,185#u8,201#u8,109#u8,87#u8],by rfl⟩
def limbs064 : QM31Limbs := ![⟨752548862,by change 752548862<2147483647;omega⟩,⟨474240349,by change 474240349<2147483647;omega⟩,⟨1192282096,by change 1192282096<2147483647;omega⟩,⟨1466812857,by change 1466812857<2147483647;omega⟩]
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
    ok (some ⟨⟨752548862#u32,474240349#u32⟩,⟨1192282096#u32,1466812857#u32⟩⟩) := JFr_EncodedCell.parser cell064 limbs064 encoded064
#print axioms parser064
def cell065 : Array U8 16#usize := ⟨[221#u8,179#u8,118#u8,83#u8,248#u8,102#u8,143#u8,82#u8,105#u8,150#u8,219#u8,115#u8,87#u8,206#u8,233#u8,40#u8],by rfl⟩
def limbs065 : QM31Limbs := ![⟨1400288221,by change 1400288221<2147483647;omega⟩,⟨1385129720,by change 1385129720<2147483647;omega⟩,⟨1943770729,by change 1943770729<2147483647;omega⟩,⟨686411351,by change 686411351<2147483647;omega⟩]
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
    ok (some ⟨⟨1400288221#u32,1385129720#u32⟩,⟨1943770729#u32,686411351#u32⟩⟩) := JFr_EncodedCell.parser cell065 limbs065 encoded065
#print axioms parser065
def cell066 : Array U8 16#usize := ⟨[119#u8,50#u8,135#u8,112#u8,18#u8,66#u8,121#u8,87#u8,49#u8,120#u8,230#u8,110#u8,119#u8,247#u8,122#u8,87#u8],by rfl⟩
def limbs066 : QM31Limbs := ![⟨1887908471,by change 1887908471<2147483647;omega⟩,⟨1467564562,by change 1467564562<2147483647;omega⟩,⟨1860597809,by change 1860597809<2147483647;omega⟩,⟨1467676535,by change 1467676535<2147483647;omega⟩]
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
    ok (some ⟨⟨1887908471#u32,1467564562#u32⟩,⟨1860597809#u32,1467676535#u32⟩⟩) := JFr_EncodedCell.parser cell066 limbs066 encoded066
#print axioms parser066
def cell067 : Array U8 16#usize := ⟨[219#u8,31#u8,252#u8,86#u8,182#u8,147#u8,116#u8,97#u8,173#u8,11#u8,34#u8,125#u8,169#u8,253#u8,250#u8,56#u8],by rfl⟩
def limbs067 : QM31Limbs := ![⟨1459363803,by change 1459363803<2147483647;omega⟩,⟨1635029942,by change 1635029942<2147483647;omega⟩,⟨2099383213,by change 2099383213<2147483647;omega⟩,⟨955973033,by change 955973033<2147483647;omega⟩]
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
    ok (some ⟨⟨1459363803#u32,1635029942#u32⟩,⟨2099383213#u32,955973033#u32⟩⟩) := JFr_EncodedCell.parser cell067 limbs067 encoded067
#print axioms parser067
def cell068 : Array U8 16#usize := ⟨[166#u8,252#u8,10#u8,109#u8,161#u8,228#u8,104#u8,28#u8,202#u8,130#u8,171#u8,44#u8,99#u8,135#u8,186#u8,60#u8],by rfl⟩
def limbs068 : QM31Limbs := ![⟨1829436582,by change 1829436582<2147483647;omega⟩,⟨476636321,by change 476636321<2147483647;omega⟩,⟨749437642,by change 749437642<2147483647;omega⟩,⟨1018857315,by change 1018857315<2147483647;omega⟩]
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
    ok (some ⟨⟨1829436582#u32,476636321#u32⟩,⟨749437642#u32,1018857315#u32⟩⟩) := JFr_EncodedCell.parser cell068 limbs068 encoded068
#print axioms parser068
def cell069 : Array U8 16#usize := ⟨[33#u8,42#u8,13#u8,95#u8,252#u8,73#u8,0#u8,93#u8,246#u8,205#u8,95#u8,74#u8,201#u8,16#u8,230#u8,100#u8],by rfl⟩
def limbs069 : QM31Limbs := ![⟨1594698273,by change 1594698273<2147483647;omega⟩,⟨1560300028,by change 1560300028<2147483647;omega⟩,⟨1247792630,by change 1247792630<2147483647;omega⟩,⟨1692799177,by change 1692799177<2147483647;omega⟩]
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
    ok (some ⟨⟨1594698273#u32,1560300028#u32⟩,⟨1247792630#u32,1692799177#u32⟩⟩) := JFr_EncodedCell.parser cell069 limbs069 encoded069
#print axioms parser069
def cell070 : Array U8 16#usize := ⟨[58#u8,18#u8,144#u8,25#u8,190#u8,30#u8,227#u8,120#u8,91#u8,6#u8,129#u8,109#u8,190#u8,178#u8,162#u8,113#u8],by rfl⟩
def limbs070 : QM31Limbs := ![⟨428872250,by change 428872250<2147483647;omega⟩,⟨2028150462,by change 2028150462<2147483647;omega⟩,⟨1837172315,by change 1837172315<2147483647;omega⟩,⟨1906487998,by change 1906487998<2147483647;omega⟩]
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
    ok (some ⟨⟨428872250#u32,2028150462#u32⟩,⟨1837172315#u32,1906487998#u32⟩⟩) := JFr_EncodedCell.parser cell070 limbs070 encoded070
#print axioms parser070
def cell071 : Array U8 16#usize := ⟨[123#u8,163#u8,62#u8,79#u8,246#u8,3#u8,194#u8,37#u8,76#u8,94#u8,211#u8,62#u8,88#u8,147#u8,181#u8,2#u8],by rfl⟩
def limbs071 : QM31Limbs := ![⟨1329505147,by change 1329505147<2147483647;omega⟩,⟨633471990,by change 633471990<2147483647;omega⟩,⟨1054039628,by change 1054039628<2147483647;omega⟩,⟨45454168,by change 45454168<2147483647;omega⟩]
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
    ok (some ⟨⟨1329505147#u32,633471990#u32⟩,⟨1054039628#u32,45454168#u32⟩⟩) := JFr_EncodedCell.parser cell071 limbs071 encoded071
#print axioms parser071
def cell072 : Array U8 16#usize := ⟨[210#u8,112#u8,9#u8,46#u8,198#u8,178#u8,227#u8,0#u8,21#u8,125#u8,243#u8,83#u8,5#u8,218#u8,199#u8,96#u8],by rfl⟩
def limbs072 : QM31Limbs := ![⟨772370642,by change 772370642<2147483647;omega⟩,⟨14922438,by change 14922438<2147483647;omega⟩,⟨1408466197,by change 1408466197<2147483647;omega⟩,⟨1623710213,by change 1623710213<2147483647;omega⟩]
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
    ok (some ⟨⟨772370642#u32,14922438#u32⟩,⟨1408466197#u32,1623710213#u32⟩⟩) := JFr_EncodedCell.parser cell072 limbs072 encoded072
#print axioms parser072
def cell073 : Array U8 16#usize := ⟨[52#u8,95#u8,13#u8,84#u8,194#u8,206#u8,252#u8,37#u8,246#u8,30#u8,241#u8,33#u8,196#u8,77#u8,10#u8,32#u8],by rfl⟩
def limbs073 : QM31Limbs := ![⟨1410162484,by change 1410162484<2147483647;omega⟩,⟨637324994,by change 637324994<2147483647;omega⟩,⟨569450230,by change 569450230<2147483647;omega⟩,⟨537546180,by change 537546180<2147483647;omega⟩]
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
    ok (some ⟨⟨1410162484#u32,637324994#u32⟩,⟨569450230#u32,537546180#u32⟩⟩) := JFr_EncodedCell.parser cell073 limbs073 encoded073
#print axioms parser073
def cell074 : Array U8 16#usize := ⟨[139#u8,85#u8,1#u8,69#u8,81#u8,98#u8,99#u8,20#u8,128#u8,155#u8,220#u8,106#u8,88#u8,23#u8,152#u8,86#u8],by rfl⟩
def limbs074 : QM31Limbs := ![⟨1157715339,by change 1157715339<2147483647;omega⟩,⟨342057553,by change 342057553<2147483647;omega⟩,⟨1792842624,by change 1792842624<2147483647;omega⟩,⟨1452808024,by change 1452808024<2147483647;omega⟩]
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
    ok (some ⟨⟨1157715339#u32,342057553#u32⟩,⟨1792842624#u32,1452808024#u32⟩⟩) := JFr_EncodedCell.parser cell074 limbs074 encoded074
#print axioms parser074
def cell075 : Array U8 16#usize := ⟨[26#u8,217#u8,94#u8,91#u8,21#u8,184#u8,18#u8,10#u8,146#u8,87#u8,238#u8,34#u8,48#u8,227#u8,242#u8,67#u8],by rfl⟩
def limbs075 : QM31Limbs := ![⟨1532942618,by change 1532942618<2147483647;omega⟩,⟨168998933,by change 168998933<2147483647;omega⟩,⟨586045330,by change 586045330<2147483647;omega⟩,⟨1139991344,by change 1139991344<2147483647;omega⟩]
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
    ok (some ⟨⟨1532942618#u32,168998933#u32⟩,⟨586045330#u32,1139991344#u32⟩⟩) := JFr_EncodedCell.parser cell075 limbs075 encoded075
#print axioms parser075
def cell076 : Array U8 16#usize := ⟨[161#u8,37#u8,226#u8,94#u8,178#u8,105#u8,166#u8,113#u8,237#u8,32#u8,168#u8,99#u8,239#u8,52#u8,154#u8,22#u8],by rfl⟩
def limbs076 : QM31Limbs := ![⟨1591879073,by change 1591879073<2147483647;omega⟩,⟨1906731442,by change 1906731442<2147483647;omega⟩,⟨1671962861,by change 1671962861<2147483647;omega⟩,⟨379204847,by change 379204847<2147483647;omega⟩]
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
    ok (some ⟨⟨1591879073#u32,1906731442#u32⟩,⟨1671962861#u32,379204847#u32⟩⟩) := JFr_EncodedCell.parser cell076 limbs076 encoded076
#print axioms parser076
def cell077 : Array U8 16#usize := ⟨[151#u8,87#u8,141#u8,40#u8,159#u8,37#u8,239#u8,73#u8,121#u8,204#u8,138#u8,7#u8,238#u8,165#u8,2#u8,32#u8],by rfl⟩
def limbs077 : QM31Limbs := ![⟨680351639,by change 680351639<2147483647;omega⟩,⟨1240409503,by change 1240409503<2147483647;omega⟩,⟨126536825,by change 126536825<2147483647;omega⟩,⟨537044462,by change 537044462<2147483647;omega⟩]
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
    ok (some ⟨⟨680351639#u32,1240409503#u32⟩,⟨126536825#u32,537044462#u32⟩⟩) := JFr_EncodedCell.parser cell077 limbs077 encoded077
#print axioms parser077
def cell078 : Array U8 16#usize := ⟨[90#u8,241#u8,94#u8,109#u8,219#u8,199#u8,120#u8,22#u8,81#u8,123#u8,185#u8,16#u8,14#u8,143#u8,27#u8,44#u8],by rfl⟩
def limbs078 : QM31Limbs := ![⟨1834938714,by change 1834938714<2147483647;omega⟩,⟨377014235,by change 377014235<2147483647;omega⟩,⟨280591185,by change 280591185<2147483647;omega⟩,⟨740003598,by change 740003598<2147483647;omega⟩]
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
    ok (some ⟨⟨1834938714#u32,377014235#u32⟩,⟨280591185#u32,740003598#u32⟩⟩) := JFr_EncodedCell.parser cell078 limbs078 encoded078
#print axioms parser078
def cell079 : Array U8 16#usize := ⟨[33#u8,252#u8,72#u8,51#u8,174#u8,117#u8,208#u8,58#u8,148#u8,8#u8,214#u8,16#u8,4#u8,208#u8,236#u8,9#u8],by rfl⟩
def limbs079 : QM31Limbs := ![⟨860421153,by change 860421153<2147483647;omega⟩,⟨986740142,by change 986740142<2147483647;omega⟩,⟨282462356,by change 282462356<2147483647;omega⟩,⟨166514692,by change 166514692<2147483647;omega⟩]
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
    ok (some ⟨⟨860421153#u32,986740142#u32⟩,⟨282462356#u32,166514692#u32⟩⟩) := JFr_EncodedCell.parser cell079 limbs079 encoded079
#print axioms parser079
def cell080 : Array U8 16#usize := ⟨[199#u8,252#u8,35#u8,8#u8,86#u8,244#u8,104#u8,107#u8,174#u8,65#u8,69#u8,63#u8,108#u8,235#u8,118#u8,36#u8],by rfl⟩
def limbs080 : QM31Limbs := ![⟨136576199,by change 136576199<2147483647;omega⟩,⟨1802040406,by change 1802040406<2147483647;omega⟩,⟨1061503406,by change 1061503406<2147483647;omega⟩,⟨611773292,by change 611773292<2147483647;omega⟩]
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
    ok (some ⟨⟨136576199#u32,1802040406#u32⟩,⟨1061503406#u32,611773292#u32⟩⟩) := JFr_EncodedCell.parser cell080 limbs080 encoded080
#print axioms parser080
def cell081 : Array U8 16#usize := ⟨[21#u8,186#u8,242#u8,56#u8,10#u8,166#u8,5#u8,121#u8,21#u8,198#u8,15#u8,59#u8,173#u8,209#u8,36#u8,28#u8],by rfl⟩
def limbs081 : QM31Limbs := ![⟨955431445,by change 955431445<2147483647;omega⟩,⟨2030413322,by change 2030413322<2147483647;omega⟩,⟨990889493,by change 990889493<2147483647;omega⟩,⟨472175021,by change 472175021<2147483647;omega⟩]
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
    ok (some ⟨⟨955431445#u32,2030413322#u32⟩,⟨990889493#u32,472175021#u32⟩⟩) := JFr_EncodedCell.parser cell081 limbs081 encoded081
#print axioms parser081
def cell082 : Array U8 16#usize := ⟨[74#u8,234#u8,77#u8,55#u8,209#u8,184#u8,53#u8,9#u8,107#u8,145#u8,87#u8,70#u8,62#u8,70#u8,164#u8,48#u8],by rfl⟩
def limbs082 : QM31Limbs := ![⟨927853130,by change 927853130<2147483647;omega⟩,⟨154515665,by change 154515665<2147483647;omega⟩,⟨1180143979,by change 1180143979<2147483647;omega⟩,⟨816072254,by change 816072254<2147483647;omega⟩]
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
    ok (some ⟨⟨927853130#u32,154515665#u32⟩,⟨1180143979#u32,816072254#u32⟩⟩) := JFr_EncodedCell.parser cell082 limbs082 encoded082
#print axioms parser082
def cell083 : Array U8 16#usize := ⟨[31#u8,85#u8,111#u8,29#u8,125#u8,20#u8,220#u8,18#u8,199#u8,205#u8,87#u8,4#u8,212#u8,62#u8,80#u8,54#u8],by rfl⟩
def limbs083 : QM31Limbs := ![⟨493835551,by change 493835551<2147483647;omega⟩,⟨316413053,by change 316413053<2147483647;omega⟩,⟨72863175,by change 72863175<2147483647;omega⟩,⟨911228628,by change 911228628<2147483647;omega⟩]
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
    ok (some ⟨⟨493835551#u32,316413053#u32⟩,⟨72863175#u32,911228628#u32⟩⟩) := JFr_EncodedCell.parser cell083 limbs083 encoded083
#print axioms parser083
def cell084 : Array U8 16#usize := ⟨[122#u8,119#u8,180#u8,80#u8,64#u8,203#u8,234#u8,89#u8,159#u8,86#u8,192#u8,31#u8,15#u8,121#u8,239#u8,9#u8],by rfl⟩
def limbs084 : QM31Limbs := ![⟨1354004346,by change 1354004346<2147483647;omega⟩,⟨1508559680,by change 1508559680<2147483647;omega⟩,⟨532698783,by change 532698783<2147483647;omega⟩,⟨166689039,by change 166689039<2147483647;omega⟩]
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
    ok (some ⟨⟨1354004346#u32,1508559680#u32⟩,⟨532698783#u32,166689039#u32⟩⟩) := JFr_EncodedCell.parser cell084 limbs084 encoded084
#print axioms parser084
def cell085 : Array U8 16#usize := ⟨[154#u8,228#u8,117#u8,88#u8,33#u8,47#u8,233#u8,42#u8,133#u8,224#u8,21#u8,37#u8,224#u8,148#u8,164#u8,78#u8],by rfl⟩
def limbs085 : QM31Limbs := ![⟨1484121242,by change 1484121242<2147483647;omega⟩,⟨719925025,by change 719925025<2147483647;omega⟩,⟨622190725,by change 622190725<2147483647;omega⟩,⟨1319408864,by change 1319408864<2147483647;omega⟩]
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
    ok (some ⟨⟨1484121242#u32,719925025#u32⟩,⟨622190725#u32,1319408864#u32⟩⟩) := JFr_EncodedCell.parser cell085 limbs085 encoded085
#print axioms parser085
def cell086 : Array U8 16#usize := ⟨[78#u8,143#u8,19#u8,45#u8,102#u8,186#u8,53#u8,75#u8,44#u8,226#u8,178#u8,8#u8,230#u8,194#u8,98#u8,79#u8],by rfl⟩
def limbs086 : QM31Limbs := ![⟨756256590,by change 756256590<2147483647;omega⟩,⟨1261812326,by change 1261812326<2147483647;omega⟩,⟨145941036,by change 145941036<2147483647;omega⟩,⟨1331872486,by change 1331872486<2147483647;omega⟩]
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
    ok (some ⟨⟨756256590#u32,1261812326#u32⟩,⟨145941036#u32,1331872486#u32⟩⟩) := JFr_EncodedCell.parser cell086 limbs086 encoded086
#print axioms parser086
end AspisR1.JFu_ClaimsData
