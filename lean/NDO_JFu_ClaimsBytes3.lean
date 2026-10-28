import NDO_JFu_ClaimsData
set_option autoImplicit false
namespace AspisR1.JFu_ClaimsData
open Aeneas Aeneas.Std Result RetainedFieldByteCodec
open AspisR1PublicPreparation AspisS1ExtractedRoundChildren
open JFu_Q25Source.Input
def cell087 : Array U8 16#usize := ⟨[54#u8,85#u8,193#u8,10#u8,1#u8,171#u8,37#u8,49#u8,136#u8,108#u8,34#u8,64#u8,175#u8,164#u8,1#u8,122#u8],by rfl⟩
def limbs087 : QM31Limbs := ![⟨180442422,by change 180442422<2147483647;omega⟩,⟨824552193,by change 824552193<2147483647;omega⟩,⟨1075997832,by change 1075997832<2147483647;omega⟩,⟨2046928047,by change 2046928047<2147483647;omega⟩]
theorem window087 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*87)).take 16=cell087.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*87)).take 16=cell087.val
  rw [JFu_FlatWindow.source chunks lengths 87 (by change 87<116;omega)]
  rfl
#print axioms window087
theorem encoded087 : CandidateParserByteOrder.arrayBytes16 cell087=encodeQM31LE limbs087 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded087
theorem parser087 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell087)=
    ok (some ⟨⟨180442422#u32,824552193#u32⟩,⟨1075997832#u32,2046928047#u32⟩⟩) := JFr_EncodedCell.parser cell087 limbs087 encoded087
#print axioms parser087
def cell088 : Array U8 16#usize := ⟨[85#u8,225#u8,95#u8,86#u8,217#u8,16#u8,98#u8,53#u8,8#u8,100#u8,128#u8,76#u8,70#u8,206#u8,60#u8,113#u8],by rfl⟩
def limbs088 : QM31Limbs := ![⟨1449124181,by change 1449124181<2147483647;omega⟩,⟨895619289,by change 895619289<2147483647;omega⟩,⟨1283482632,by change 1283482632<2147483647;omega⟩,⟨1899810374,by change 1899810374<2147483647;omega⟩]
theorem window088 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*88)).take 16=cell088.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*88)).take 16=cell088.val
  rw [JFu_FlatWindow.source chunks lengths 88 (by change 88<116;omega)]
  rfl
#print axioms window088
theorem encoded088 : CandidateParserByteOrder.arrayBytes16 cell088=encodeQM31LE limbs088 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded088
theorem parser088 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell088)=
    ok (some ⟨⟨1449124181#u32,895619289#u32⟩,⟨1283482632#u32,1899810374#u32⟩⟩) := JFr_EncodedCell.parser cell088 limbs088 encoded088
#print axioms parser088
def cell089 : Array U8 16#usize := ⟨[153#u8,51#u8,176#u8,121#u8,171#u8,178#u8,124#u8,25#u8,113#u8,27#u8,10#u8,67#u8,180#u8,96#u8,75#u8,7#u8],by rfl⟩
def limbs089 : QM31Limbs := ![⟨2041590681,by change 2041590681<2147483647;omega⟩,⟨427602603,by change 427602603<2147483647;omega⟩,⟨1124735857,by change 1124735857<2147483647;omega⟩,⟨122380468,by change 122380468<2147483647;omega⟩]
theorem window089 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*89)).take 16=cell089.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*89)).take 16=cell089.val
  rw [JFu_FlatWindow.source chunks lengths 89 (by change 89<116;omega)]
  rfl
#print axioms window089
theorem encoded089 : CandidateParserByteOrder.arrayBytes16 cell089=encodeQM31LE limbs089 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded089
theorem parser089 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell089)=
    ok (some ⟨⟨2041590681#u32,427602603#u32⟩,⟨1124735857#u32,122380468#u32⟩⟩) := JFr_EncodedCell.parser cell089 limbs089 encoded089
#print axioms parser089
def cell090 : Array U8 16#usize := ⟨[61#u8,33#u8,142#u8,57#u8,4#u8,148#u8,98#u8,125#u8,212#u8,241#u8,125#u8,9#u8,79#u8,3#u8,176#u8,4#u8],by rfl⟩
def limbs090 : QM31Limbs := ![⟨965615933,by change 965615933<2147483647;omega⟩,⟨2103612420,by change 2103612420<2147483647;omega⟩,⟨159248852,by change 159248852<2147483647;omega⟩,⟨78644047,by change 78644047<2147483647;omega⟩]
theorem window090 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*90)).take 16=cell090.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*90)).take 16=cell090.val
  rw [JFu_FlatWindow.source chunks lengths 90 (by change 90<116;omega)]
  rfl
#print axioms window090
theorem encoded090 : CandidateParserByteOrder.arrayBytes16 cell090=encodeQM31LE limbs090 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded090
theorem parser090 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell090)=
    ok (some ⟨⟨965615933#u32,2103612420#u32⟩,⟨159248852#u32,78644047#u32⟩⟩) := JFr_EncodedCell.parser cell090 limbs090 encoded090
#print axioms parser090
def cell091 : Array U8 16#usize := ⟨[17#u8,218#u8,248#u8,67#u8,148#u8,46#u8,3#u8,66#u8,69#u8,137#u8,193#u8,85#u8,171#u8,153#u8,233#u8,0#u8],by rfl⟩
def limbs091 : QM31Limbs := ![⟨1140382225,by change 1140382225<2147483647;omega⟩,⟨1107504788,by change 1107504788<2147483647;omega⟩,⟨1438746949,by change 1438746949<2147483647;omega⟩,⟨15309227,by change 15309227<2147483647;omega⟩]
theorem window091 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*91)).take 16=cell091.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*91)).take 16=cell091.val
  rw [JFu_FlatWindow.source chunks lengths 91 (by change 91<116;omega)]
  rfl
#print axioms window091
theorem encoded091 : CandidateParserByteOrder.arrayBytes16 cell091=encodeQM31LE limbs091 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded091
theorem parser091 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell091)=
    ok (some ⟨⟨1140382225#u32,1107504788#u32⟩,⟨1438746949#u32,15309227#u32⟩⟩) := JFr_EncodedCell.parser cell091 limbs091 encoded091
#print axioms parser091
def cell092 : Array U8 16#usize := ⟨[6#u8,125#u8,174#u8,114#u8,140#u8,27#u8,239#u8,117#u8,162#u8,113#u8,191#u8,72#u8,122#u8,231#u8,121#u8,18#u8],by rfl⟩
def limbs092 : QM31Limbs := ![⟨1924037894,by change 1924037894<2147483647;omega⟩,⟨1978604428,by change 1978604428<2147483647;omega⟩,⟨1220506018,by change 1220506018<2147483647;omega⟩,⟨309979002,by change 309979002<2147483647;omega⟩]
theorem window092 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*92)).take 16=cell092.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*92)).take 16=cell092.val
  rw [JFu_FlatWindow.source chunks lengths 92 (by change 92<116;omega)]
  rfl
#print axioms window092
theorem encoded092 : CandidateParserByteOrder.arrayBytes16 cell092=encodeQM31LE limbs092 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded092
theorem parser092 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell092)=
    ok (some ⟨⟨1924037894#u32,1978604428#u32⟩,⟨1220506018#u32,309979002#u32⟩⟩) := JFr_EncodedCell.parser cell092 limbs092 encoded092
#print axioms parser092
def cell093 : Array U8 16#usize := ⟨[189#u8,111#u8,103#u8,67#u8,218#u8,76#u8,161#u8,37#u8,25#u8,59#u8,115#u8,100#u8,204#u8,76#u8,70#u8,84#u8],by rfl⟩
def limbs093 : QM31Limbs := ![⟨1130852285,by change 1130852285<2147483647;omega⟩,⟨631327962,by change 631327962<2147483647;omega⟩,⟨1685273369,by change 1685273369<2147483647;omega⟩,⟨1413893324,by change 1413893324<2147483647;omega⟩]
theorem window093 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*93)).take 16=cell093.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*93)).take 16=cell093.val
  rw [JFu_FlatWindow.source chunks lengths 93 (by change 93<116;omega)]
  rfl
#print axioms window093
theorem encoded093 : CandidateParserByteOrder.arrayBytes16 cell093=encodeQM31LE limbs093 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded093
theorem parser093 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell093)=
    ok (some ⟨⟨1130852285#u32,631327962#u32⟩,⟨1685273369#u32,1413893324#u32⟩⟩) := JFr_EncodedCell.parser cell093 limbs093 encoded093
#print axioms parser093
def cell094 : Array U8 16#usize := ⟨[21#u8,155#u8,0#u8,100#u8,180#u8,207#u8,186#u8,82#u8,76#u8,61#u8,13#u8,87#u8,225#u8,153#u8,202#u8,49#u8],by rfl⟩
def limbs094 : QM31Limbs := ![⟨1677761301,by change 1677761301<2147483647;omega⟩,⟨1387974580,by change 1387974580<2147483647;omega⟩,⟨1460485452,by change 1460485452<2147483647;omega⟩,⟨835361249,by change 835361249<2147483647;omega⟩]
theorem window094 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*94)).take 16=cell094.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*94)).take 16=cell094.val
  rw [JFu_FlatWindow.source chunks lengths 94 (by change 94<116;omega)]
  rfl
#print axioms window094
theorem encoded094 : CandidateParserByteOrder.arrayBytes16 cell094=encodeQM31LE limbs094 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded094
theorem parser094 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell094)=
    ok (some ⟨⟨1677761301#u32,1387974580#u32⟩,⟨1460485452#u32,835361249#u32⟩⟩) := JFr_EncodedCell.parser cell094 limbs094 encoded094
#print axioms parser094
def cell095 : Array U8 16#usize := ⟨[25#u8,39#u8,216#u8,100#u8,91#u8,135#u8,199#u8,98#u8,170#u8,6#u8,131#u8,83#u8,226#u8,64#u8,197#u8,4#u8],by rfl⟩
def limbs095 : QM31Limbs := ![⟨1691887385,by change 1691887385<2147483647;omega⟩,⟨1657243483,by change 1657243483<2147483647;omega⟩,⟨1401095850,by change 1401095850<2147483647;omega⟩,⟨80036066,by change 80036066<2147483647;omega⟩]
theorem window095 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*95)).take 16=cell095.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*95)).take 16=cell095.val
  rw [JFu_FlatWindow.source chunks lengths 95 (by change 95<116;omega)]
  rfl
#print axioms window095
theorem encoded095 : CandidateParserByteOrder.arrayBytes16 cell095=encodeQM31LE limbs095 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded095
theorem parser095 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell095)=
    ok (some ⟨⟨1691887385#u32,1657243483#u32⟩,⟨1401095850#u32,80036066#u32⟩⟩) := JFr_EncodedCell.parser cell095 limbs095 encoded095
#print axioms parser095
def cell096 : Array U8 16#usize := ⟨[160#u8,200#u8,235#u8,65#u8,92#u8,245#u8,173#u8,7#u8,114#u8,51#u8,238#u8,0#u8,77#u8,189#u8,45#u8,17#u8],by rfl⟩
def limbs096 : QM31Limbs := ![⟨1105971360,by change 1105971360<2147483647;omega⟩,⟨128841052,by change 128841052<2147483647;omega⟩,⟨15610738,by change 15610738<2147483647;omega⟩,⟨288210253,by change 288210253<2147483647;omega⟩]
theorem window096 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*96)).take 16=cell096.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*96)).take 16=cell096.val
  rw [JFu_FlatWindow.source chunks lengths 96 (by change 96<116;omega)]
  rfl
#print axioms window096
theorem encoded096 : CandidateParserByteOrder.arrayBytes16 cell096=encodeQM31LE limbs096 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded096
theorem parser096 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell096)=
    ok (some ⟨⟨1105971360#u32,128841052#u32⟩,⟨15610738#u32,288210253#u32⟩⟩) := JFr_EncodedCell.parser cell096 limbs096 encoded096
#print axioms parser096
def cell097 : Array U8 16#usize := ⟨[122#u8,104#u8,27#u8,66#u8,0#u8,97#u8,224#u8,68#u8,172#u8,212#u8,142#u8,16#u8,202#u8,166#u8,208#u8,41#u8],by rfl⟩
def limbs097 : QM31Limbs := ![⟨1109092474,by change 1109092474<2147483647;omega⟩,⟨1155555584,by change 1155555584<2147483647;omega⟩,⟨277796012,by change 277796012<2147483647;omega⟩,⟨701540042,by change 701540042<2147483647;omega⟩]
theorem window097 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*97)).take 16=cell097.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*97)).take 16=cell097.val
  rw [JFu_FlatWindow.source chunks lengths 97 (by change 97<116;omega)]
  rfl
#print axioms window097
theorem encoded097 : CandidateParserByteOrder.arrayBytes16 cell097=encodeQM31LE limbs097 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded097
theorem parser097 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell097)=
    ok (some ⟨⟨1109092474#u32,1155555584#u32⟩,⟨277796012#u32,701540042#u32⟩⟩) := JFr_EncodedCell.parser cell097 limbs097 encoded097
#print axioms parser097
def cell098 : Array U8 16#usize := ⟨[77#u8,103#u8,25#u8,74#u8,50#u8,80#u8,194#u8,52#u8,154#u8,16#u8,134#u8,40#u8,31#u8,146#u8,1#u8,95#u8],by rfl⟩
def limbs098 : QM31Limbs := ![⟨1243178829,by change 1243178829<2147483647;omega⟩,⟨885149746,by change 885149746<2147483647;omega⟩,⟨679874714,by change 679874714<2147483647;omega⟩,⟨1593938463,by change 1593938463<2147483647;omega⟩]
theorem window098 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*98)).take 16=cell098.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*98)).take 16=cell098.val
  rw [JFu_FlatWindow.source chunks lengths 98 (by change 98<116;omega)]
  rfl
#print axioms window098
theorem encoded098 : CandidateParserByteOrder.arrayBytes16 cell098=encodeQM31LE limbs098 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded098
theorem parser098 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell098)=
    ok (some ⟨⟨1243178829#u32,885149746#u32⟩,⟨679874714#u32,1593938463#u32⟩⟩) := JFr_EncodedCell.parser cell098 limbs098 encoded098
#print axioms parser098
def cell099 : Array U8 16#usize := ⟨[233#u8,205#u8,14#u8,105#u8,116#u8,68#u8,169#u8,99#u8,251#u8,117#u8,218#u8,127#u8,58#u8,26#u8,244#u8,118#u8],by rfl⟩
def limbs099 : QM31Limbs := ![⟨1762577897,by change 1762577897<2147483647;omega⟩,⟨1672037492,by change 1672037492<2147483647;omega⟩,⟨2145023483,by change 2145023483<2147483647;omega⟩,⟨1995708986,by change 1995708986<2147483647;omega⟩]
theorem window099 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*99)).take 16=cell099.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*99)).take 16=cell099.val
  rw [JFu_FlatWindow.source chunks lengths 99 (by change 99<116;omega)]
  rfl
#print axioms window099
theorem encoded099 : CandidateParserByteOrder.arrayBytes16 cell099=encodeQM31LE limbs099 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded099
theorem parser099 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell099)=
    ok (some ⟨⟨1762577897#u32,1672037492#u32⟩,⟨2145023483#u32,1995708986#u32⟩⟩) := JFr_EncodedCell.parser cell099 limbs099 encoded099
#print axioms parser099
def cell100 : Array U8 16#usize := ⟨[116#u8,112#u8,174#u8,83#u8,178#u8,6#u8,210#u8,12#u8,116#u8,119#u8,83#u8,80#u8,114#u8,78#u8,204#u8,105#u8],by rfl⟩
def limbs100 : QM31Limbs := ![⟨1403940980,by change 1403940980<2147483647;omega⟩,⟨215090866,by change 215090866<2147483647;omega⟩,⟨1347647348,by change 1347647348<2147483647;omega⟩,⟨1774997106,by change 1774997106<2147483647;omega⟩]
theorem window100 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*100)).take 16=cell100.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*100)).take 16=cell100.val
  rw [JFu_FlatWindow.source chunks lengths 100 (by change 100<116;omega)]
  rfl
#print axioms window100
theorem encoded100 : CandidateParserByteOrder.arrayBytes16 cell100=encodeQM31LE limbs100 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded100
theorem parser100 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell100)=
    ok (some ⟨⟨1403940980#u32,215090866#u32⟩,⟨1347647348#u32,1774997106#u32⟩⟩) := JFr_EncodedCell.parser cell100 limbs100 encoded100
#print axioms parser100
def cell101 : Array U8 16#usize := ⟨[102#u8,146#u8,171#u8,83#u8,252#u8,127#u8,123#u8,68#u8,187#u8,41#u8,141#u8,6#u8,144#u8,35#u8,120#u8,44#u8],by rfl⟩
def limbs101 : QM31Limbs := ![⟨1403753062,by change 1403753062<2147483647;omega⟩,⟨1148944380,by change 1148944380<2147483647;omega⟩,⟨109914555,by change 109914555<2147483647;omega⟩,⟨746070928,by change 746070928<2147483647;omega⟩]
theorem window101 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*101)).take 16=cell101.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*101)).take 16=cell101.val
  rw [JFu_FlatWindow.source chunks lengths 101 (by change 101<116;omega)]
  rfl
#print axioms window101
theorem encoded101 : CandidateParserByteOrder.arrayBytes16 cell101=encodeQM31LE limbs101 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded101
theorem parser101 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell101)=
    ok (some ⟨⟨1403753062#u32,1148944380#u32⟩,⟨109914555#u32,746070928#u32⟩⟩) := JFr_EncodedCell.parser cell101 limbs101 encoded101
#print axioms parser101
def cell102 : Array U8 16#usize := ⟨[178#u8,85#u8,180#u8,117#u8,97#u8,175#u8,39#u8,126#u8,139#u8,113#u8,250#u8,113#u8,220#u8,199#u8,186#u8,22#u8],by rfl⟩
def limbs102 : QM31Limbs := ![⟨1974752690,by change 1974752690<2147483647;omega⟩,⟨2116530017,by change 2116530017<2147483647;omega⟩,⟨1912238475,by change 1912238475<2147483647;omega⟩,⟨381339612,by change 381339612<2147483647;omega⟩]
theorem window102 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*102)).take 16=cell102.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*102)).take 16=cell102.val
  rw [JFu_FlatWindow.source chunks lengths 102 (by change 102<116;omega)]
  rfl
#print axioms window102
theorem encoded102 : CandidateParserByteOrder.arrayBytes16 cell102=encodeQM31LE limbs102 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded102
theorem parser102 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell102)=
    ok (some ⟨⟨1974752690#u32,2116530017#u32⟩,⟨1912238475#u32,381339612#u32⟩⟩) := JFr_EncodedCell.parser cell102 limbs102 encoded102
#print axioms parser102
def cell103 : Array U8 16#usize := ⟨[94#u8,26#u8,0#u8,1#u8,111#u8,90#u8,178#u8,92#u8,171#u8,105#u8,137#u8,10#u8,80#u8,162#u8,219#u8,34#u8],by rfl⟩
def limbs103 : QM31Limbs := ![⟨16783966,by change 16783966<2147483647;omega⟩,⟨1555192431,by change 1555192431<2147483647;omega⟩,⟨176777643,by change 176777643<2147483647;omega⟩,⟨584819280,by change 584819280<2147483647;omega⟩]
theorem window103 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*103)).take 16=cell103.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*103)).take 16=cell103.val
  rw [JFu_FlatWindow.source chunks lengths 103 (by change 103<116;omega)]
  rfl
#print axioms window103
theorem encoded103 : CandidateParserByteOrder.arrayBytes16 cell103=encodeQM31LE limbs103 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded103
theorem parser103 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell103)=
    ok (some ⟨⟨16783966#u32,1555192431#u32⟩,⟨176777643#u32,584819280#u32⟩⟩) := JFr_EncodedCell.parser cell103 limbs103 encoded103
#print axioms parser103
def cell104 : Array U8 16#usize := ⟨[140#u8,109#u8,164#u8,39#u8,251#u8,148#u8,132#u8,69#u8,203#u8,120#u8,163#u8,70#u8,143#u8,236#u8,156#u8,81#u8],by rfl⟩
def limbs104 : QM31Limbs := ![⟨665087372,by change 665087372<2147483647;omega⟩,⟨1166316795,by change 1166316795<2147483647;omega⟩,⟨1185118411,by change 1185118411<2147483647;omega⟩,⟨1369238671,by change 1369238671<2147483647;omega⟩]
theorem window104 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*104)).take 16=cell104.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*104)).take 16=cell104.val
  rw [JFu_FlatWindow.source chunks lengths 104 (by change 104<116;omega)]
  rfl
#print axioms window104
theorem encoded104 : CandidateParserByteOrder.arrayBytes16 cell104=encodeQM31LE limbs104 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded104
theorem parser104 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell104)=
    ok (some ⟨⟨665087372#u32,1166316795#u32⟩,⟨1185118411#u32,1369238671#u32⟩⟩) := JFr_EncodedCell.parser cell104 limbs104 encoded104
#print axioms parser104
def cell105 : Array U8 16#usize := ⟨[156#u8,34#u8,35#u8,24#u8,23#u8,14#u8,186#u8,21#u8,78#u8,92#u8,116#u8,25#u8,135#u8,207#u8,216#u8,7#u8],by rfl⟩
def limbs105 : QM31Limbs := ![⟨404955804,by change 404955804<2147483647;omega⟩,⟨364514839,by change 364514839<2147483647;omega⟩,⟨427056206,by change 427056206<2147483647;omega⟩,⟨131649415,by change 131649415<2147483647;omega⟩]
theorem window105 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*105)).take 16=cell105.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*105)).take 16=cell105.val
  rw [JFu_FlatWindow.source chunks lengths 105 (by change 105<116;omega)]
  rfl
#print axioms window105
theorem encoded105 : CandidateParserByteOrder.arrayBytes16 cell105=encodeQM31LE limbs105 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded105
theorem parser105 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell105)=
    ok (some ⟨⟨404955804#u32,364514839#u32⟩,⟨427056206#u32,131649415#u32⟩⟩) := JFr_EncodedCell.parser cell105 limbs105 encoded105
#print axioms parser105
def cell106 : Array U8 16#usize := ⟨[74#u8,147#u8,251#u8,55#u8,224#u8,166#u8,244#u8,29#u8,21#u8,208#u8,108#u8,18#u8,157#u8,81#u8,198#u8,14#u8],by rfl⟩
def limbs106 : QM31Limbs := ![⟨939234122,by change 939234122<2147483647;omega⟩,⟨502572768,by change 502572768<2147483647;omega⟩,⟨309121045,by change 309121045<2147483647;omega⟩,⟨247878045,by change 247878045<2147483647;omega⟩]
theorem window106 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*106)).take 16=cell106.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*106)).take 16=cell106.val
  rw [JFu_FlatWindow.source chunks lengths 106 (by change 106<116;omega)]
  rfl
#print axioms window106
theorem encoded106 : CandidateParserByteOrder.arrayBytes16 cell106=encodeQM31LE limbs106 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded106
theorem parser106 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell106)=
    ok (some ⟨⟨939234122#u32,502572768#u32⟩,⟨309121045#u32,247878045#u32⟩⟩) := JFr_EncodedCell.parser cell106 limbs106 encoded106
#print axioms parser106
def cell107 : Array U8 16#usize := ⟨[97#u8,122#u8,87#u8,56#u8,151#u8,53#u8,112#u8,64#u8,126#u8,55#u8,154#u8,35#u8,201#u8,0#u8,160#u8,111#u8],by rfl⟩
def limbs107 : QM31Limbs := ![⟨945257057,by change 945257057<2147483647;omega⟩,⟨1081095575,by change 1081095575<2147483647;omega⟩,⟨597309310,by change 597309310<2147483647;omega⟩,⟨1872756937,by change 1872756937<2147483647;omega⟩]
theorem window107 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*107)).take 16=cell107.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*107)).take 16=cell107.val
  rw [JFu_FlatWindow.source chunks lengths 107 (by change 107<116;omega)]
  rfl
#print axioms window107
theorem encoded107 : CandidateParserByteOrder.arrayBytes16 cell107=encodeQM31LE limbs107 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded107
theorem parser107 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell107)=
    ok (some ⟨⟨945257057#u32,1081095575#u32⟩,⟨597309310#u32,1872756937#u32⟩⟩) := JFr_EncodedCell.parser cell107 limbs107 encoded107
#print axioms parser107
def cell108 : Array U8 16#usize := ⟨[161#u8,137#u8,164#u8,74#u8,224#u8,138#u8,109#u8,51#u8,150#u8,82#u8,81#u8,85#u8,247#u8,102#u8,24#u8,6#u8],by rfl⟩
def limbs108 : QM31Limbs := ![⟨1252297121,by change 1252297121<2147483647;omega⟩,⟨862816992,by change 862816992<2147483647;omega⟩,⟨1431392918,by change 1431392918<2147483647;omega⟩,⟨102262519,by change 102262519<2147483647;omega⟩]
theorem window108 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*108)).take 16=cell108.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*108)).take 16=cell108.val
  rw [JFu_FlatWindow.source chunks lengths 108 (by change 108<116;omega)]
  rfl
#print axioms window108
theorem encoded108 : CandidateParserByteOrder.arrayBytes16 cell108=encodeQM31LE limbs108 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded108
theorem parser108 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell108)=
    ok (some ⟨⟨1252297121#u32,862816992#u32⟩,⟨1431392918#u32,102262519#u32⟩⟩) := JFr_EncodedCell.parser cell108 limbs108 encoded108
#print axioms parser108
def cell109 : Array U8 16#usize := ⟨[253#u8,31#u8,111#u8,45#u8,124#u8,91#u8,222#u8,102#u8,36#u8,209#u8,237#u8,112#u8,30#u8,242#u8,231#u8,91#u8],by rfl⟩
def limbs109 : QM31Limbs := ![⟨762257405,by change 762257405<2147483647;omega⟩,⟨1725848444,by change 1725848444<2147483647;omega⟩,⟨1894633764,by change 1894633764<2147483647;omega⟩,⟨1541927454,by change 1541927454<2147483647;omega⟩]
theorem window109 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*109)).take 16=cell109.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*109)).take 16=cell109.val
  rw [JFu_FlatWindow.source chunks lengths 109 (by change 109<116;omega)]
  rfl
#print axioms window109
theorem encoded109 : CandidateParserByteOrder.arrayBytes16 cell109=encodeQM31LE limbs109 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded109
theorem parser109 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell109)=
    ok (some ⟨⟨762257405#u32,1725848444#u32⟩,⟨1894633764#u32,1541927454#u32⟩⟩) := JFr_EncodedCell.parser cell109 limbs109 encoded109
#print axioms parser109
def cell110 : Array U8 16#usize := ⟨[234#u8,179#u8,173#u8,4#u8,149#u8,91#u8,160#u8,23#u8,156#u8,104#u8,4#u8,76#u8,127#u8,92#u8,2#u8,85#u8],by rfl⟩
def limbs110 : QM31Limbs := ![⟨78492650,by change 78492650<2147483647;omega⟩,⟨396385173,by change 396385173<2147483647;omega⟩,⟨1275357340,by change 1275357340<2147483647;omega⟩,⟨1426218111,by change 1426218111<2147483647;omega⟩]
theorem window110 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*110)).take 16=cell110.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*110)).take 16=cell110.val
  rw [JFu_FlatWindow.source chunks lengths 110 (by change 110<116;omega)]
  rfl
#print axioms window110
theorem encoded110 : CandidateParserByteOrder.arrayBytes16 cell110=encodeQM31LE limbs110 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded110
theorem parser110 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell110)=
    ok (some ⟨⟨78492650#u32,396385173#u32⟩,⟨1275357340#u32,1426218111#u32⟩⟩) := JFr_EncodedCell.parser cell110 limbs110 encoded110
#print axioms parser110
def cell111 : Array U8 16#usize := ⟨[191#u8,62#u8,78#u8,109#u8,232#u8,249#u8,85#u8,9#u8,92#u8,53#u8,120#u8,59#u8,216#u8,192#u8,98#u8,66#u8],by rfl⟩
def limbs111 : QM31Limbs := ![⟨1833844415,by change 1833844415<2147483647;omega⟩,⟨156629480,by change 156629480<2147483647;omega⟩,⟨997733724,by change 997733724<2147483647;omega⟩,⟨1113768152,by change 1113768152<2147483647;omega⟩]
theorem window111 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*111)).take 16=cell111.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*111)).take 16=cell111.val
  rw [JFu_FlatWindow.source chunks lengths 111 (by change 111<116;omega)]
  rfl
#print axioms window111
theorem encoded111 : CandidateParserByteOrder.arrayBytes16 cell111=encodeQM31LE limbs111 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded111
theorem parser111 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell111)=
    ok (some ⟨⟨1833844415#u32,156629480#u32⟩,⟨997733724#u32,1113768152#u32⟩⟩) := JFr_EncodedCell.parser cell111 limbs111 encoded111
#print axioms parser111
def cell112 : Array U8 16#usize := ⟨[96#u8,74#u8,42#u8,64#u8,106#u8,44#u8,151#u8,13#u8,199#u8,28#u8,59#u8,16#u8,212#u8,142#u8,155#u8,59#u8],by rfl⟩
def limbs112 : QM31Limbs := ![⟨1076513376,by change 1076513376<2147483647;omega⟩,⟨228011114,by change 228011114<2147483647;omega⟩,⟨272309447,by change 272309447<2147483647;omega⟩,⟨1000050388,by change 1000050388<2147483647;omega⟩]
theorem window112 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*112)).take 16=cell112.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*112)).take 16=cell112.val
  rw [JFu_FlatWindow.source chunks lengths 112 (by change 112<116;omega)]
  rfl
#print axioms window112
theorem encoded112 : CandidateParserByteOrder.arrayBytes16 cell112=encodeQM31LE limbs112 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded112
theorem parser112 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell112)=
    ok (some ⟨⟨1076513376#u32,228011114#u32⟩,⟨272309447#u32,1000050388#u32⟩⟩) := JFr_EncodedCell.parser cell112 limbs112 encoded112
#print axioms parser112
def cell113 : Array U8 16#usize := ⟨[61#u8,92#u8,104#u8,23#u8,176#u8,15#u8,234#u8,110#u8,79#u8,134#u8,151#u8,66#u8,31#u8,94#u8,79#u8,48#u8],by rfl⟩
def limbs113 : QM31Limbs := ![⟨392715325,by change 392715325<2147483647;omega⟩,⟨1860833200,by change 1860833200<2147483647;omega⟩,⟨1117226575,by change 1117226575<2147483647;omega⟩,⟨810507807,by change 810507807<2147483647;omega⟩]
theorem window113 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*113)).take 16=cell113.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*113)).take 16=cell113.val
  rw [JFu_FlatWindow.source chunks lengths 113 (by change 113<116;omega)]
  rfl
#print axioms window113
theorem encoded113 : CandidateParserByteOrder.arrayBytes16 cell113=encodeQM31LE limbs113 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded113
theorem parser113 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell113)=
    ok (some ⟨⟨392715325#u32,1860833200#u32⟩,⟨1117226575#u32,810507807#u32⟩⟩) := JFr_EncodedCell.parser cell113 limbs113 encoded113
#print axioms parser113
def cell114 : Array U8 16#usize := ⟨[182#u8,159#u8,47#u8,110#u8,51#u8,123#u8,190#u8,94#u8,105#u8,20#u8,26#u8,66#u8,69#u8,9#u8,131#u8,19#u8],by rfl⟩
def limbs114 : QM31Limbs := ![⟨1848614838,by change 1848614838<2147483647;omega⟩,⟨1589541683,by change 1589541683<2147483647;omega⟩,⟨1109005417,by change 1109005417<2147483647;omega⟩,⟨327354693,by change 327354693<2147483647;omega⟩]
theorem window114 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*114)).take 16=cell114.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*114)).take 16=cell114.val
  rw [JFu_FlatWindow.source chunks lengths 114 (by change 114<116;omega)]
  rfl
#print axioms window114
theorem encoded114 : CandidateParserByteOrder.arrayBytes16 cell114=encodeQM31LE limbs114 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded114
theorem parser114 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell114)=
    ok (some ⟨⟨1848614838#u32,1589541683#u32⟩,⟨1109005417#u32,327354693#u32⟩⟩) := JFr_EncodedCell.parser cell114 limbs114 encoded114
#print axioms parser114
def cell115 : Array U8 16#usize := ⟨[184#u8,45#u8,199#u8,1#u8,173#u8,22#u8,151#u8,29#u8,36#u8,107#u8,149#u8,33#u8,36#u8,89#u8,236#u8,96#u8],by rfl⟩
def limbs115 : QM31Limbs := ![⟨29830584,by change 29830584<2147483647;omega⟩,⟨496441005,by change 496441005<2147483647;omega⟩,⟨563440420,by change 563440420<2147483647;omega⟩,⟨1626102052,by change 1626102052<2147483647;omega⟩]
theorem window115 : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*115)).take 16=cell115.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*115)).take 16=cell115.val
  rw [JFu_FlatWindow.source chunks lengths 115 (by change 115<116;omega)]
  rfl
#print axioms window115
theorem encoded115 : CandidateParserByteOrder.arrayBytes16 cell115=encodeQM31LE limbs115 := by
  funext i;fin_cases i <;> rfl
#print axioms encoded115
theorem parser115 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell115)=
    ok (some ⟨⟨29830584#u32,496441005#u32⟩,⟨563440420#u32,1626102052#u32⟩⟩) := JFr_EncodedCell.parser cell115 limbs115 encoded115
#print axioms parser115
end AspisR1.JFu_ClaimsData
