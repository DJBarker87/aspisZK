import NDO_JFu_ClaimsData
set_option autoImplicit false
namespace AspisR1.JFu_ClaimsData
open Aeneas Aeneas.Std Result RetainedFieldByteCodec
open AspisR1PublicPreparation AspisS1ExtractedRoundChildren
open JFu_Q25Source.Input
def cell087 : Array U8 16#usize := ⟨[73#u8,122#u8,76#u8,32#u8,206#u8,13#u8,46#u8,102#u8,111#u8,133#u8,49#u8,65#u8,112#u8,15#u8,59#u8,56#u8],by rfl⟩
def limbs087 : QM31Limbs := ![⟨541882953,by change 541882953<2147483647;omega⟩,⟨1714294222,by change 1714294222<2147483647;omega⟩,⟨1093764463,by change 1093764463<2147483647;omega⟩,⟨943394672,by change 943394672<2147483647;omega⟩]
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
    ok (some ⟨⟨541882953#u32,1714294222#u32⟩,⟨1093764463#u32,943394672#u32⟩⟩) := JFr_EncodedCell.parser cell087 limbs087 encoded087
#print axioms parser087
def cell088 : Array U8 16#usize := ⟨[154#u8,179#u8,114#u8,60#u8,106#u8,98#u8,212#u8,38#u8,156#u8,212#u8,124#u8,123#u8,249#u8,122#u8,128#u8,122#u8],by rfl⟩
def limbs088 : QM31Limbs := ![⟨1014150042,by change 1014150042<2147483647;omega⟩,⟨651453034,by change 651453034<2147483647;omega⟩,⟨2071778460,by change 2071778460<2147483647;omega⟩,⟨2055240441,by change 2055240441<2147483647;omega⟩]
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
    ok (some ⟨⟨1014150042#u32,651453034#u32⟩,⟨2071778460#u32,2055240441#u32⟩⟩) := JFr_EncodedCell.parser cell088 limbs088 encoded088
#print axioms parser088
def cell089 : Array U8 16#usize := ⟨[138#u8,92#u8,250#u8,9#u8,228#u8,235#u8,107#u8,21#u8,237#u8,186#u8,249#u8,26#u8,18#u8,20#u8,165#u8,126#u8],by rfl⟩
def limbs089 : QM31Limbs := ![⟨167402634,by change 167402634<2147483647;omega⟩,⟨359394276,by change 359394276<2147483647;omega⟩,⟨452573933,by change 452573933<2147483647;omega⟩,⟨2124747794,by change 2124747794<2147483647;omega⟩]
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
    ok (some ⟨⟨167402634#u32,359394276#u32⟩,⟨452573933#u32,2124747794#u32⟩⟩) := JFr_EncodedCell.parser cell089 limbs089 encoded089
#print axioms parser089
def cell090 : Array U8 16#usize := ⟨[227#u8,80#u8,70#u8,122#u8,242#u8,71#u8,91#u8,15#u8,11#u8,48#u8,62#u8,105#u8,74#u8,141#u8,224#u8,102#u8],by rfl⟩
def limbs090 : QM31Limbs := ![⟨2051428579,by change 2051428579<2147483647;omega⟩,⟨257640434,by change 257640434<2147483647;omega⟩,⟨1765683211,by change 1765683211<2147483647;omega⟩,⟨1725992266,by change 1725992266<2147483647;omega⟩]
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
    ok (some ⟨⟨2051428579#u32,257640434#u32⟩,⟨1765683211#u32,1725992266#u32⟩⟩) := JFr_EncodedCell.parser cell090 limbs090 encoded090
#print axioms parser090
def cell091 : Array U8 16#usize := ⟨[23#u8,147#u8,157#u8,127#u8,125#u8,172#u8,60#u8,101#u8,27#u8,36#u8,179#u8,57#u8,53#u8,7#u8,149#u8,113#u8],by rfl⟩
def limbs091 : QM31Limbs := ![⟨2141033239,by change 2141033239<2147483647;omega⟩,⟨1698475133,by change 1698475133<2147483647;omega⟩,⟨968041499,by change 968041499<2147483647;omega⟩,⟨1905592117,by change 1905592117<2147483647;omega⟩]
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
    ok (some ⟨⟨2141033239#u32,1698475133#u32⟩,⟨968041499#u32,1905592117#u32⟩⟩) := JFr_EncodedCell.parser cell091 limbs091 encoded091
#print axioms parser091
def cell092 : Array U8 16#usize := ⟨[70#u8,221#u8,96#u8,127#u8,60#u8,7#u8,40#u8,88#u8,219#u8,20#u8,172#u8,51#u8,11#u8,138#u8,27#u8,32#u8],by rfl⟩
def limbs092 : QM31Limbs := ![⟨2137054534,by change 2137054534<2147483647;omega⟩,⟨1479018300,by change 1479018300<2147483647;omega⟩,⟨866915547,by change 866915547<2147483647;omega⟩,⟨538675723,by change 538675723<2147483647;omega⟩]
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
    ok (some ⟨⟨2137054534#u32,1479018300#u32⟩,⟨866915547#u32,538675723#u32⟩⟩) := JFr_EncodedCell.parser cell092 limbs092 encoded092
#print axioms parser092
def cell093 : Array U8 16#usize := ⟨[5#u8,10#u8,27#u8,109#u8,111#u8,166#u8,96#u8,101#u8,31#u8,15#u8,201#u8,50#u8,187#u8,64#u8,245#u8,97#u8],by rfl⟩
def limbs093 : QM31Limbs := ![⟨1830488581,by change 1830488581<2147483647;omega⟩,⟨1700832879,by change 1700832879<2147483647;omega⟩,⟨852037407,by change 852037407<2147483647;omega⟩,⟨1643462843,by change 1643462843<2147483647;omega⟩]
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
    ok (some ⟨⟨1830488581#u32,1700832879#u32⟩,⟨852037407#u32,1643462843#u32⟩⟩) := JFr_EncodedCell.parser cell093 limbs093 encoded093
#print axioms parser093
def cell094 : Array U8 16#usize := ⟨[134#u8,100#u8,10#u8,105#u8,197#u8,64#u8,247#u8,11#u8,241#u8,201#u8,59#u8,123#u8,29#u8,28#u8,165#u8,93#u8],by rfl⟩
def limbs094 : QM31Limbs := ![⟨1762288774,by change 1762288774<2147483647;omega⟩,⟨200753349,by change 200753349<2147483647;omega⟩,⟨2067515889,by change 2067515889<2147483647;omega⟩,⟨1571101725,by change 1571101725<2147483647;omega⟩]
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
    ok (some ⟨⟨1762288774#u32,200753349#u32⟩,⟨2067515889#u32,1571101725#u32⟩⟩) := JFr_EncodedCell.parser cell094 limbs094 encoded094
#print axioms parser094
def cell095 : Array U8 16#usize := ⟨[20#u8,33#u8,248#u8,95#u8,119#u8,206#u8,5#u8,41#u8,110#u8,34#u8,255#u8,124#u8,18#u8,0#u8,237#u8,106#u8],by rfl⟩
def limbs095 : QM31Limbs := ![⟨1610096916,by change 1610096916<2147483647;omega⟩,⟨688246391,by change 688246391<2147483647;omega⟩,⟨2097095278,by change 2097095278<2147483647;omega⟩,⟨1793916946,by change 1793916946<2147483647;omega⟩]
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
    ok (some ⟨⟨1610096916#u32,688246391#u32⟩,⟨2097095278#u32,1793916946#u32⟩⟩) := JFr_EncodedCell.parser cell095 limbs095 encoded095
#print axioms parser095
def cell096 : Array U8 16#usize := ⟨[210#u8,32#u8,219#u8,56#u8,106#u8,103#u8,47#u8,26#u8,29#u8,220#u8,50#u8,104#u8,94#u8,83#u8,94#u8,28#u8],by rfl⟩
def limbs096 : QM31Limbs := ![⟨953884882,by change 953884882<2147483647;omega⟩,⟨439314282,by change 439314282<2147483647;omega⟩,⟨1748163613,by change 1748163613<2147483647;omega⟩,⟨475943774,by change 475943774<2147483647;omega⟩]
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
    ok (some ⟨⟨953884882#u32,439314282#u32⟩,⟨1748163613#u32,475943774#u32⟩⟩) := JFr_EncodedCell.parser cell096 limbs096 encoded096
#print axioms parser096
def cell097 : Array U8 16#usize := ⟨[7#u8,98#u8,251#u8,48#u8,37#u8,234#u8,187#u8,6#u8,207#u8,210#u8,64#u8,93#u8,106#u8,165#u8,244#u8,37#u8],by rfl⟩
def limbs097 : QM31Limbs := ![⟨821780999,by change 821780999<2147483647;omega⟩,⟨112978469,by change 112978469<2147483647;omega⟩,⟨1564529359,by change 1564529359<2147483647;omega⟩,⟨636790122,by change 636790122<2147483647;omega⟩]
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
    ok (some ⟨⟨821780999#u32,112978469#u32⟩,⟨1564529359#u32,636790122#u32⟩⟩) := JFr_EncodedCell.parser cell097 limbs097 encoded097
#print axioms parser097
def cell098 : Array U8 16#usize := ⟨[129#u8,48#u8,146#u8,101#u8,71#u8,67#u8,56#u8,48#u8,14#u8,182#u8,222#u8,72#u8,123#u8,243#u8,91#u8,13#u8],by rfl⟩
def limbs098 : QM31Limbs := ![⟨1704079489,by change 1704079489<2147483647;omega⟩,⟨808993607,by change 808993607<2147483647;omega⟩,⟨1222555150,by change 1222555150<2147483647;omega⟩,⟨224129915,by change 224129915<2147483647;omega⟩]
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
    ok (some ⟨⟨1704079489#u32,808993607#u32⟩,⟨1222555150#u32,224129915#u32⟩⟩) := JFr_EncodedCell.parser cell098 limbs098 encoded098
#print axioms parser098
def cell099 : Array U8 16#usize := ⟨[17#u8,98#u8,90#u8,29#u8,29#u8,48#u8,196#u8,51#u8,103#u8,42#u8,197#u8,54#u8,144#u8,54#u8,55#u8,112#u8],by rfl⟩
def limbs099 : QM31Limbs := ![⟨492462609,by change 492462609<2147483647;omega⟩,⟨868495389,by change 868495389<2147483647;omega⟩,⟨918891111,by change 918891111<2147483647;omega⟩,⟨1882666640,by change 1882666640<2147483647;omega⟩]
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
    ok (some ⟨⟨492462609#u32,868495389#u32⟩,⟨918891111#u32,1882666640#u32⟩⟩) := JFr_EncodedCell.parser cell099 limbs099 encoded099
#print axioms parser099
def cell100 : Array U8 16#usize := ⟨[57#u8,228#u8,66#u8,105#u8,36#u8,92#u8,53#u8,14#u8,149#u8,28#u8,186#u8,45#u8,172#u8,166#u8,212#u8,99#u8],by rfl⟩
def limbs100 : QM31Limbs := ![⟨1765991481,by change 1765991481<2147483647;omega⟩,⟨238378020,by change 238378020<2147483647;omega⟩,⟨767171733,by change 767171733<2147483647;omega⟩,⟨1674880684,by change 1674880684<2147483647;omega⟩]
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
    ok (some ⟨⟨1765991481#u32,238378020#u32⟩,⟨767171733#u32,1674880684#u32⟩⟩) := JFr_EncodedCell.parser cell100 limbs100 encoded100
#print axioms parser100
def cell101 : Array U8 16#usize := ⟨[55#u8,16#u8,178#u8,72#u8,29#u8,2#u8,19#u8,53#u8,52#u8,215#u8,147#u8,69#u8,187#u8,252#u8,20#u8,76#u8],by rfl⟩
def limbs101 : QM31Limbs := ![⟨1219629111,by change 1219629111<2147483647;omega⟩,⟨890438173,by change 890438173<2147483647;omega⟩,⟨1167316788,by change 1167316788<2147483647;omega⟩,⟨1276443835,by change 1276443835<2147483647;omega⟩]
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
    ok (some ⟨⟨1219629111#u32,890438173#u32⟩,⟨1167316788#u32,1276443835#u32⟩⟩) := JFr_EncodedCell.parser cell101 limbs101 encoded101
#print axioms parser101
def cell102 : Array U8 16#usize := ⟨[250#u8,139#u8,87#u8,64#u8,42#u8,167#u8,153#u8,127#u8,171#u8,59#u8,72#u8,24#u8,76#u8,95#u8,84#u8,41#u8],by rfl⟩
def limbs102 : QM31Limbs := ![⟨1079479290,by change 1079479290<2147483647;omega⟩,⟨2140776234,by change 2140776234<2147483647;omega⟩,⟨407387051,by change 407387051<2147483647;omega⟩,⟨693395276,by change 693395276<2147483647;omega⟩]
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
    ok (some ⟨⟨1079479290#u32,2140776234#u32⟩,⟨407387051#u32,693395276#u32⟩⟩) := JFr_EncodedCell.parser cell102 limbs102 encoded102
#print axioms parser102
def cell103 : Array U8 16#usize := ⟨[78#u8,69#u8,166#u8,46#u8,30#u8,203#u8,167#u8,99#u8,145#u8,170#u8,131#u8,40#u8,115#u8,126#u8,162#u8,97#u8],by rfl⟩
def limbs103 : QM31Limbs := ![⟨782648654,by change 782648654<2147483647;omega⟩,⟨1671940894,by change 1671940894<2147483647;omega⟩,⟨679717521,by change 679717521<2147483647;omega⟩,⟨1638039155,by change 1638039155<2147483647;omega⟩]
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
    ok (some ⟨⟨782648654#u32,1671940894#u32⟩,⟨679717521#u32,1638039155#u32⟩⟩) := JFr_EncodedCell.parser cell103 limbs103 encoded103
#print axioms parser103
def cell104 : Array U8 16#usize := ⟨[139#u8,132#u8,89#u8,7#u8,189#u8,244#u8,60#u8,55#u8,174#u8,48#u8,102#u8,30#u8,122#u8,49#u8,7#u8,77#u8],by rfl⟩
def limbs104 : QM31Limbs := ![⟨123307147,by change 123307147<2147483647;omega⟩,⟨926741693,by change 926741693<2147483647;omega⟩,⟨510013614,by change 510013614<2147483647;omega⟩,⟨1292317050,by change 1292317050<2147483647;omega⟩]
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
    ok (some ⟨⟨123307147#u32,926741693#u32⟩,⟨510013614#u32,1292317050#u32⟩⟩) := JFr_EncodedCell.parser cell104 limbs104 encoded104
#print axioms parser104
def cell105 : Array U8 16#usize := ⟨[74#u8,186#u8,77#u8,19#u8,99#u8,233#u8,57#u8,73#u8,230#u8,45#u8,130#u8,116#u8,20#u8,249#u8,41#u8,65#u8],by rfl⟩
def limbs105 : QM31Limbs := ![⟨323861066,by change 323861066<2147483647;omega⟩,⟨1228532067,by change 1228532067<2147483647;omega⟩,⟨1954688486,by change 1954688486<2147483647;omega⟩,⟨1093269780,by change 1093269780<2147483647;omega⟩]
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
    ok (some ⟨⟨323861066#u32,1228532067#u32⟩,⟨1954688486#u32,1093269780#u32⟩⟩) := JFr_EncodedCell.parser cell105 limbs105 encoded105
#print axioms parser105
def cell106 : Array U8 16#usize := ⟨[236#u8,208#u8,108#u8,111#u8,3#u8,129#u8,30#u8,75#u8,232#u8,44#u8,167#u8,78#u8,226#u8,158#u8,36#u8,22#u8],by rfl⟩
def limbs106 : QM31Limbs := ![⟨1869402348,by change 1869402348<2147483647;omega⟩,⟨1260290307,by change 1260290307<2147483647;omega⟩,⟨1319578856,by change 1319578856<2147483647;omega⟩,⟨371498722,by change 371498722<2147483647;omega⟩]
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
    ok (some ⟨⟨1869402348#u32,1260290307#u32⟩,⟨1319578856#u32,371498722#u32⟩⟩) := JFr_EncodedCell.parser cell106 limbs106 encoded106
#print axioms parser106
def cell107 : Array U8 16#usize := ⟨[152#u8,212#u8,7#u8,84#u8,149#u8,115#u8,228#u8,83#u8,116#u8,240#u8,97#u8,16#u8,14#u8,156#u8,250#u8,59#u8],by rfl⟩
def limbs107 : QM31Limbs := ![⟨1409799320,by change 1409799320<2147483647;omega⟩,⟨1407480725,by change 1407480725<2147483647;omega⟩,⟨274854004,by change 274854004<2147483647;omega⟩,⟨1006279694,by change 1006279694<2147483647;omega⟩]
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
    ok (some ⟨⟨1409799320#u32,1407480725#u32⟩,⟨274854004#u32,1006279694#u32⟩⟩) := JFr_EncodedCell.parser cell107 limbs107 encoded107
#print axioms parser107
def cell108 : Array U8 16#usize := ⟨[249#u8,189#u8,169#u8,38#u8,145#u8,138#u8,48#u8,91#u8,54#u8,200#u8,134#u8,52#u8,39#u8,102#u8,29#u8,11#u8],by rfl⟩
def limbs108 : QM31Limbs := ![⟨648658425,by change 648658425<2147483647;omega⟩,⟨1529907857,by change 1529907857<2147483647;omega⟩,⟨881248310,by change 881248310<2147483647;omega⟩,⟨186476071,by change 186476071<2147483647;omega⟩]
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
    ok (some ⟨⟨648658425#u32,1529907857#u32⟩,⟨881248310#u32,186476071#u32⟩⟩) := JFr_EncodedCell.parser cell108 limbs108 encoded108
#print axioms parser108
def cell109 : Array U8 16#usize := ⟨[13#u8,70#u8,213#u8,125#u8,172#u8,130#u8,136#u8,82#u8,21#u8,80#u8,34#u8,106#u8,154#u8,58#u8,148#u8,41#u8],by rfl⟩
def limbs109 : QM31Limbs := ![⟨2111129101,by change 2111129101<2147483647;omega⟩,⟨1384678060,by change 1384678060<2147483647;omega⟩,⟨1780633621,by change 1780633621<2147483647;omega⟩,⟨697580186,by change 697580186<2147483647;omega⟩]
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
    ok (some ⟨⟨2111129101#u32,1384678060#u32⟩,⟨1780633621#u32,697580186#u32⟩⟩) := JFr_EncodedCell.parser cell109 limbs109 encoded109
#print axioms parser109
def cell110 : Array U8 16#usize := ⟨[101#u8,219#u8,79#u8,20#u8,208#u8,221#u8,255#u8,68#u8,139#u8,249#u8,86#u8,114#u8,71#u8,42#u8,174#u8,124#u8],by rfl⟩
def limbs110 : QM31Limbs := ![⟨340777829,by change 340777829<2147483647;omega⟩,⟨1157619152,by change 1157619152<2147483647;omega⟩,⟨1918302603,by change 1918302603<2147483647;omega⟩,⟨2091788871,by change 2091788871<2147483647;omega⟩]
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
    ok (some ⟨⟨340777829#u32,1157619152#u32⟩,⟨1918302603#u32,2091788871#u32⟩⟩) := JFr_EncodedCell.parser cell110 limbs110 encoded110
#print axioms parser110
def cell111 : Array U8 16#usize := ⟨[3#u8,43#u8,14#u8,14#u8,64#u8,3#u8,81#u8,29#u8,123#u8,12#u8,187#u8,17#u8,67#u8,176#u8,206#u8,92#u8],by rfl⟩
def limbs111 : QM31Limbs := ![⟨235809539,by change 235809539<2147483647;omega⟩,⟨491848512,by change 491848512<2147483647;omega⟩,⟨297471099,by change 297471099<2147483647;omega⟩,⟨1557049411,by change 1557049411<2147483647;omega⟩]
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
    ok (some ⟨⟨235809539#u32,491848512#u32⟩,⟨297471099#u32,1557049411#u32⟩⟩) := JFr_EncodedCell.parser cell111 limbs111 encoded111
#print axioms parser111
def cell112 : Array U8 16#usize := ⟨[142#u8,149#u8,163#u8,109#u8,97#u8,201#u8,19#u8,118#u8,32#u8,0#u8,113#u8,38#u8,112#u8,165#u8,92#u8,113#u8],by rfl⟩
def limbs112 : QM31Limbs := ![⟨1839437198,by change 1839437198<2147483647;omega⟩,⟨1981008225,by change 1981008225<2147483647;omega⟩,⟨644939808,by change 644939808<2147483647;omega⟩,⟨1901897072,by change 1901897072<2147483647;omega⟩]
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
    ok (some ⟨⟨1839437198#u32,1981008225#u32⟩,⟨644939808#u32,1901897072#u32⟩⟩) := JFr_EncodedCell.parser cell112 limbs112 encoded112
#print axioms parser112
def cell113 : Array U8 16#usize := ⟨[124#u8,41#u8,57#u8,11#u8,232#u8,44#u8,134#u8,99#u8,184#u8,166#u8,15#u8,122#u8,93#u8,7#u8,58#u8,100#u8],by rfl⟩
def limbs113 : QM31Limbs := ![⟨188295548,by change 188295548<2147483647;omega⟩,⟨1669737704,by change 1669737704<2147483647;omega⟩,⟨2047846072,by change 2047846072<2147483647;omega⟩,⟨1681524573,by change 1681524573<2147483647;omega⟩]
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
    ok (some ⟨⟨188295548#u32,1669737704#u32⟩,⟨2047846072#u32,1681524573#u32⟩⟩) := JFr_EncodedCell.parser cell113 limbs113 encoded113
#print axioms parser113
def cell114 : Array U8 16#usize := ⟨[151#u8,214#u8,230#u8,54#u8,46#u8,173#u8,91#u8,91#u8,134#u8,253#u8,82#u8,80#u8,163#u8,10#u8,91#u8,77#u8],by rfl⟩
def limbs114 : QM31Limbs := ![⟨921097879,by change 921097879<2147483647;omega⟩,⟨1532734766,by change 1532734766<2147483647;omega⟩,⟨1347616134,by change 1347616134<2147483647;omega⟩,⟨1297812131,by change 1297812131<2147483647;omega⟩]
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
    ok (some ⟨⟨921097879#u32,1532734766#u32⟩,⟨1347616134#u32,1297812131#u32⟩⟩) := JFr_EncodedCell.parser cell114 limbs114 encoded114
#print axioms parser114
def cell115 : Array U8 16#usize := ⟨[144#u8,153#u8,219#u8,121#u8,5#u8,57#u8,92#u8,57#u8,133#u8,244#u8,137#u8,41#u8,106#u8,158#u8,250#u8,84#u8],by rfl⟩
def limbs115 : QM31Limbs := ![⟨2044434832,by change 2044434832<2147483647;omega⟩,⟨962345221,by change 962345221<2147483647;omega⟩,⟨696906885,by change 696906885<2147483647;omega⟩,⟨1425710698,by change 1425710698<2147483647;omega⟩]
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
    ok (some ⟨⟨2044434832#u32,962345221#u32⟩,⟨696906885#u32,1425710698#u32⟩⟩) := JFr_EncodedCell.parser cell115 limbs115 encoded115
#print axioms parser115
end AspisR1.JFu_ClaimsData
