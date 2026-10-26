import JFr_Data00
import JFr_EncodedCell
import JFz_Scan48
set_option autoImplicit false
namespace AspisR1.JFr_Bytes00
open Aeneas Aeneas.Std Result RetainedFieldByteCodec
open AspisR1PublicPreparation
open AspisS1ExtractedRoundChildren
def raw : List U8 := [99#u8,86#u8,145#u8,41#u8,100#u8,145#u8,4#u8,76#u8,116#u8,68#u8,92#u8,76#u8,27#u8,166#u8,182#u8,124#u8,100#u8,194#u8,9#u8,67#u8,252#u8,217#u8,69#u8,19#u8,121#u8,112#u8,179#u8,121#u8,236#u8,235#u8,223#u8,34#u8,83#u8,0#u8,50#u8,74#u8,206#u8,93#u8,15#u8,31#u8,177#u8,191#u8,80#u8,71#u8,185#u8,49#u8,25#u8,66#u8,181#u8,34#u8,22#u8,85#u8,167#u8,76#u8,5#u8,50#u8,130#u8,191#u8,97#u8,78#u8,245#u8,122#u8,118#u8,95#u8,100#u8,189#u8,184#u8,28#u8,73#u8,131#u8,141#u8,21#u8,229#u8,171#u8,140#u8,122#u8,212#u8,214#u8,10#u8,28#u8,189#u8,29#u8,186#u8,120#u8,112#u8,227#u8,81#u8,94#u8,155#u8,33#u8,30#u8,63#u8,130#u8,71#u8,23#u8,96#u8,195#u8,108#u8,170#u8,79#u8,38#u8,88#u8,39#u8,30#u8,191#u8,229#u8,232#u8,48#u8,224#u8,199#u8,222#u8,70#u8,128#u8,17#u8,208#u8,68#u8,74#u8,118#u8,79#u8,40#u8,7#u8,111#u8,126#u8,83#u8,135#u8,96#u8,56#u8,27#u8,19#u8,27#u8,59#u8,109#u8,90#u8,136#u8,93#u8,97#u8,127#u8,60#u8,28#u8,83#u8,58#u8,130#u8,103#u8,32#u8,163#u8,29#u8,155#u8,2#u8,64#u8,60#u8,111#u8,88#u8,189#u8,234#u8,229#u8,3#u8,124#u8,152#u8,193#u8,93#u8,16#u8,113#u8,87#u8,51#u8,155#u8,168#u8,114#u8,119#u8,44#u8,3#u8,255#u8,69#u8,254#u8,241#u8,162#u8,65#u8,210#u8,190#u8,190#u8,35#u8,195#u8,190#u8,22#u8,43#u8,151#u8,69#u8,6#u8,40#u8,194#u8,124#u8,92#u8,29#u8,148#u8,1#u8,73#u8,81#u8,62#u8,177#u8,14#u8,3#u8,148#u8,46#u8,206#u8,87#u8,195#u8,221#u8,59#u8,112#u8,198#u8,124#u8,253#u8,79#u8,91#u8,27#u8,190#u8,53#u8,65#u8,151#u8,89#u8,55#u8,251#u8,200#u8,119#u8,73#u8,242#u8,196#u8,49#u8,118#u8,39#u8,159#u8,39#u8,97#u8,37#u8,178#u8,199#u8,44#u8,142#u8,73#u8,38#u8,97#u8,185#u8,220#u8,210#u8,50#u8,16#u8,52#u8,121#u8,5#u8,161#u8,225#u8,57#u8,97#u8,170#u8,112#u8,84#u8,30#u8,199#u8,227#u8,162#u8,38#u8,11#u8,125#u8,191#u8,53#u8,96#u8,162#u8,98#u8,73#u8,19#u8,196#u8,190#u8,90#u8,29#u8,234#u8,3#u8,96#u8,63#u8,57#u8,173#u8,9#u8,137#u8,155#u8,170#u8,118#u8,61#u8,121#u8,125#u8,62#u8,19#u8,191#u8,43#u8,28#u8,138#u8,7#u8,27#u8,105#u8,63#u8,177#u8,233#u8,51#u8,72#u8,218#u8,115#u8,4#u8,101#u8,90#u8,97#u8,20#u8,144#u8,114#u8,156#u8,122#u8,219#u8,166#u8,194#u8,109#u8,155#u8,150#u8,14#u8,99#u8,61#u8,18#u8,139#u8,123#u8,63#u8,48#u8,137#u8,22#u8,90#u8,13#u8,54#u8,97#u8,40#u8,141#u8,189#u8,40#u8,220#u8,131#u8,79#u8,24#u8,181#u8,246#u8,109#u8,103#u8,149#u8,226#u8,248#u8,109#u8,201#u8,78#u8,1#u8,72#u8,12#u8,149#u8,139#u8,78#u8,145#u8,236#u8,144#u8,103#u8,120#u8,97#u8,101#u8,109#u8,203#u8,136#u8,139#u8,69#u8,8#u8,125#u8,199#u8,34#u8,167#u8,117#u8,184#u8,24#u8,223#u8,167#u8,149#u8,46#u8,22#u8,104#u8,205#u8,81#u8,5#u8,1#u8,133#u8,94#u8,221#u8,56#u8,151#u8,23#u8,193#u8,115#u8,107#u8,30#u8,62#u8,62#u8,150#u8,62#u8,70#u8,80#u8,59#u8,95#u8,176#u8,117#u8,60#u8,101#u8,11#u8,33#u8,68#u8,13#u8,61#u8,244#u8,184#u8,23#u8,212#u8,24#u8,224#u8,48#u8,156#u8,246#u8,220#u8,63#u8,33#u8,60#u8,34#u8,7#u8,203#u8,207#u8,107#u8,102#u8,181#u8,85#u8,202#u8,104#u8,210#u8,28#u8,177#u8,75#u8,44#u8,251#u8,0#u8,36#u8,53#u8,48#u8,19#u8,124#u8]
theorem selected : (JFx_NativeBytes.proof.val.drop 176).take 448=raw :=
  JFz_Scan48.selected.trans (by rfl)
#print axioms selected
def cell00 : Array U8 16#usize := ⟨[99#u8,86#u8,145#u8,41#u8,100#u8,145#u8,4#u8,76#u8,116#u8,68#u8,92#u8,76#u8,27#u8,166#u8,182#u8,124#u8],by rfl⟩
def limbs00 : QM31Limbs := ![⟨697390691,by omega⟩,⟨1275367780,by omega⟩,⟨1281115252,by omega⟩,⟨2092344859,by omega⟩]
theorem encoded00 : CandidateParserByteOrder.arrayBytes16 cell00=encodeQM31LE limbs00 := by
  funext i
  fin_cases i <;> rfl
theorem parser00 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell00)=
    ok (some ⟨⟨697390691#u32,1275367780#u32⟩,⟨1281115252#u32,2092344859#u32⟩⟩) :=
  JFr_EncodedCell.parser cell00 limbs00 encoded00
#print axioms encoded00
#print axioms parser00
def cell01 : Array U8 16#usize := ⟨[100#u8,194#u8,9#u8,67#u8,252#u8,217#u8,69#u8,19#u8,121#u8,112#u8,179#u8,121#u8,236#u8,235#u8,223#u8,34#u8],by rfl⟩
def limbs01 : QM31Limbs := ![⟨1124713060,by omega⟩,⟨323344892,by omega⟩,⟨2041802873,by omega⟩,⟨585100268,by omega⟩]
theorem encoded01 : CandidateParserByteOrder.arrayBytes16 cell01=encodeQM31LE limbs01 := by
  funext i
  fin_cases i <;> rfl
theorem parser01 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell01)=
    ok (some ⟨⟨1124713060#u32,323344892#u32⟩,⟨2041802873#u32,585100268#u32⟩⟩) :=
  JFr_EncodedCell.parser cell01 limbs01 encoded01
#print axioms encoded01
#print axioms parser01
def cell02 : Array U8 16#usize := ⟨[83#u8,0#u8,50#u8,74#u8,206#u8,93#u8,15#u8,31#u8,177#u8,191#u8,80#u8,71#u8,185#u8,49#u8,25#u8,66#u8],by rfl⟩
def limbs02 : QM31Limbs := ![⟨1244790867,by omega⟩,⟨521100750,by omega⟩,⟨1196474289,by omega⟩,⟨1108947385,by omega⟩]
theorem encoded02 : CandidateParserByteOrder.arrayBytes16 cell02=encodeQM31LE limbs02 := by
  funext i
  fin_cases i <;> rfl
theorem parser02 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell02)=
    ok (some ⟨⟨1244790867#u32,521100750#u32⟩,⟨1196474289#u32,1108947385#u32⟩⟩) :=
  JFr_EncodedCell.parser cell02 limbs02 encoded02
#print axioms encoded02
#print axioms parser02
def cell03 : Array U8 16#usize := ⟨[181#u8,34#u8,22#u8,85#u8,167#u8,76#u8,5#u8,50#u8,130#u8,191#u8,97#u8,78#u8,245#u8,122#u8,118#u8,95#u8],by rfl⟩
def limbs03 : QM31Limbs := ![⟨1427514037,by omega⟩,⟨839208103,by omega⟩,⟨1315028866,by omega⟩,⟨1601600245,by omega⟩]
theorem encoded03 : CandidateParserByteOrder.arrayBytes16 cell03=encodeQM31LE limbs03 := by
  funext i
  fin_cases i <;> rfl
theorem parser03 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell03)=
    ok (some ⟨⟨1427514037#u32,839208103#u32⟩,⟨1315028866#u32,1601600245#u32⟩⟩) :=
  JFr_EncodedCell.parser cell03 limbs03 encoded03
#print axioms encoded03
#print axioms parser03
def cell04 : Array U8 16#usize := ⟨[100#u8,189#u8,184#u8,28#u8,73#u8,131#u8,141#u8,21#u8,229#u8,171#u8,140#u8,122#u8,212#u8,214#u8,10#u8,28#u8],by rfl⟩
def limbs04 : QM31Limbs := ![⟨481869156,by omega⟩,⟨361595721,by omega⟩,⟨2056039397,by omega⟩,⟨470472404,by omega⟩]
theorem encoded04 : CandidateParserByteOrder.arrayBytes16 cell04=encodeQM31LE limbs04 := by
  funext i
  fin_cases i <;> rfl
theorem parser04 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell04)=
    ok (some ⟨⟨481869156#u32,361595721#u32⟩,⟨2056039397#u32,470472404#u32⟩⟩) :=
  JFr_EncodedCell.parser cell04 limbs04 encoded04
#print axioms encoded04
#print axioms parser04
def cell05 : Array U8 16#usize := ⟨[189#u8,29#u8,186#u8,120#u8,112#u8,227#u8,81#u8,94#u8,155#u8,33#u8,30#u8,63#u8,130#u8,71#u8,23#u8,96#u8],by rfl⟩
def limbs05 : QM31Limbs := ![⟨2025463229,by omega⟩,⟨1582424944,by omega⟩,⟨1058939291,by omega⟩,⟨1612138370,by omega⟩]
theorem encoded05 : CandidateParserByteOrder.arrayBytes16 cell05=encodeQM31LE limbs05 := by
  funext i
  fin_cases i <;> rfl
theorem parser05 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell05)=
    ok (some ⟨⟨2025463229#u32,1582424944#u32⟩,⟨1058939291#u32,1612138370#u32⟩⟩) :=
  JFr_EncodedCell.parser cell05 limbs05 encoded05
#print axioms encoded05
#print axioms parser05
def cell06 : Array U8 16#usize := ⟨[195#u8,108#u8,170#u8,79#u8,38#u8,88#u8,39#u8,30#u8,191#u8,229#u8,232#u8,48#u8,224#u8,199#u8,222#u8,70#u8],by rfl⟩
def limbs06 : QM31Limbs := ![⟨1336569027,by omega⟩,⟨505894950,by omega⟩,⟨820569535,by omega⟩,⟨1189005280,by omega⟩]
theorem encoded06 : CandidateParserByteOrder.arrayBytes16 cell06=encodeQM31LE limbs06 := by
  funext i
  fin_cases i <;> rfl
theorem parser06 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell06)=
    ok (some ⟨⟨1336569027#u32,505894950#u32⟩,⟨820569535#u32,1189005280#u32⟩⟩) :=
  JFr_EncodedCell.parser cell06 limbs06 encoded06
#print axioms encoded06
#print axioms parser06
def cell07 : Array U8 16#usize := ⟨[128#u8,17#u8,208#u8,68#u8,74#u8,118#u8,79#u8,40#u8,7#u8,111#u8,126#u8,83#u8,135#u8,96#u8,56#u8,27#u8],by rfl⟩
def limbs07 : QM31Limbs := ![⟨1154486656,by omega⟩,⟨676296266,by omega⟩,⟨1400794887,by omega⟩,⟨456679559,by omega⟩]
theorem encoded07 : CandidateParserByteOrder.arrayBytes16 cell07=encodeQM31LE limbs07 := by
  funext i
  fin_cases i <;> rfl
theorem parser07 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell07)=
    ok (some ⟨⟨1154486656#u32,676296266#u32⟩,⟨1400794887#u32,456679559#u32⟩⟩) :=
  JFr_EncodedCell.parser cell07 limbs07 encoded07
#print axioms encoded07
#print axioms parser07
def cell08 : Array U8 16#usize := ⟨[19#u8,27#u8,59#u8,109#u8,90#u8,136#u8,93#u8,97#u8,127#u8,60#u8,28#u8,83#u8,58#u8,130#u8,103#u8,32#u8],by rfl⟩
def limbs08 : QM31Limbs := ![⟨1832590099,by omega⟩,⟨1633519706,by omega⟩,⟨1394359423,by omega⟩,⟨543654458,by omega⟩]
theorem encoded08 : CandidateParserByteOrder.arrayBytes16 cell08=encodeQM31LE limbs08 := by
  funext i
  fin_cases i <;> rfl
theorem parser08 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell08)=
    ok (some ⟨⟨1832590099#u32,1633519706#u32⟩,⟨1394359423#u32,543654458#u32⟩⟩) :=
  JFr_EncodedCell.parser cell08 limbs08 encoded08
#print axioms encoded08
#print axioms parser08
def cell09 : Array U8 16#usize := ⟨[163#u8,29#u8,155#u8,2#u8,64#u8,60#u8,111#u8,88#u8,189#u8,234#u8,229#u8,3#u8,124#u8,152#u8,193#u8,93#u8],by rfl⟩
def limbs09 : QM31Limbs := ![⟨43720099,by omega⟩,⟨1483684928,by omega⟩,⟨65399485,by omega⟩,⟨1572968572,by omega⟩]
theorem encoded09 : CandidateParserByteOrder.arrayBytes16 cell09=encodeQM31LE limbs09 := by
  funext i
  fin_cases i <;> rfl
theorem parser09 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell09)=
    ok (some ⟨⟨43720099#u32,1483684928#u32⟩,⟨65399485#u32,1572968572#u32⟩⟩) :=
  JFr_EncodedCell.parser cell09 limbs09 encoded09
#print axioms encoded09
#print axioms parser09
def cell10 : Array U8 16#usize := ⟨[16#u8,113#u8,87#u8,51#u8,155#u8,168#u8,114#u8,119#u8,44#u8,3#u8,255#u8,69#u8,254#u8,241#u8,162#u8,65#u8],by rfl⟩
def limbs10 : QM31Limbs := ![⟨861368592,by omega⟩,⟨2004002971,by omega⟩,⟨1174340396,by omega⟩,⟨1101197822,by omega⟩]
theorem encoded10 : CandidateParserByteOrder.arrayBytes16 cell10=encodeQM31LE limbs10 := by
  funext i
  fin_cases i <;> rfl
theorem parser10 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell10)=
    ok (some ⟨⟨861368592#u32,2004002971#u32⟩,⟨1174340396#u32,1101197822#u32⟩⟩) :=
  JFr_EncodedCell.parser cell10 limbs10 encoded10
#print axioms encoded10
#print axioms parser10
def cell11 : Array U8 16#usize := ⟨[210#u8,190#u8,190#u8,35#u8,195#u8,190#u8,22#u8,43#u8,151#u8,69#u8,6#u8,40#u8,194#u8,124#u8,92#u8,29#u8],by rfl⟩
def limbs11 : QM31Limbs := ![⟨599703250,by omega⟩,⟨722910915,by omega⟩,⟨671499671,by omega⟩,⟨492600514,by omega⟩]
theorem encoded11 : CandidateParserByteOrder.arrayBytes16 cell11=encodeQM31LE limbs11 := by
  funext i
  fin_cases i <;> rfl
theorem parser11 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell11)=
    ok (some ⟨⟨599703250#u32,722910915#u32⟩,⟨671499671#u32,492600514#u32⟩⟩) :=
  JFr_EncodedCell.parser cell11 limbs11 encoded11
#print axioms encoded11
#print axioms parser11
def cell12 : Array U8 16#usize := ⟨[148#u8,1#u8,73#u8,81#u8,62#u8,177#u8,14#u8,3#u8,148#u8,46#u8,206#u8,87#u8,195#u8,221#u8,59#u8,112#u8],by rfl⟩
def limbs12 : QM31Limbs := ![⟨1363739028,by omega⟩,⟨51294526,by omega⟩,⟨1473130132,by omega⟩,⟨1882971587,by omega⟩]
theorem encoded12 : CandidateParserByteOrder.arrayBytes16 cell12=encodeQM31LE limbs12 := by
  funext i
  fin_cases i <;> rfl
theorem parser12 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell12)=
    ok (some ⟨⟨1363739028#u32,51294526#u32⟩,⟨1473130132#u32,1882971587#u32⟩⟩) :=
  JFr_EncodedCell.parser cell12 limbs12 encoded12
#print axioms encoded12
#print axioms parser12
def cell13 : Array U8 16#usize := ⟨[198#u8,124#u8,253#u8,79#u8,91#u8,27#u8,190#u8,53#u8,65#u8,151#u8,89#u8,55#u8,251#u8,200#u8,119#u8,73#u8],by rfl⟩
def limbs13 : QM31Limbs := ![⟨1342012614,by omega⟩,⟨901651291,by omega⟩,⟨928618305,by omega⟩,⟨1232587003,by omega⟩]
theorem encoded13 : CandidateParserByteOrder.arrayBytes16 cell13=encodeQM31LE limbs13 := by
  funext i
  fin_cases i <;> rfl
theorem parser13 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell13)=
    ok (some ⟨⟨1342012614#u32,901651291#u32⟩,⟨928618305#u32,1232587003#u32⟩⟩) :=
  JFr_EncodedCell.parser cell13 limbs13 encoded13
#print axioms encoded13
#print axioms parser13
def cell14 : Array U8 16#usize := ⟨[242#u8,196#u8,49#u8,118#u8,39#u8,159#u8,39#u8,97#u8,37#u8,178#u8,199#u8,44#u8,142#u8,73#u8,38#u8,97#u8],by rfl⟩
def limbs14 : QM31Limbs := ![⟨1982973170,by omega⟩,⟨1629986599,by omega⟩,⟨751284773,by omega⟩,⟨1629899150,by omega⟩]
theorem encoded14 : CandidateParserByteOrder.arrayBytes16 cell14=encodeQM31LE limbs14 := by
  funext i
  fin_cases i <;> rfl
theorem parser14 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell14)=
    ok (some ⟨⟨1982973170#u32,1629986599#u32⟩,⟨751284773#u32,1629899150#u32⟩⟩) :=
  JFr_EncodedCell.parser cell14 limbs14 encoded14
#print axioms encoded14
#print axioms parser14
def cell15 : Array U8 16#usize := ⟨[185#u8,220#u8,210#u8,50#u8,16#u8,52#u8,121#u8,5#u8,161#u8,225#u8,57#u8,97#u8,170#u8,112#u8,84#u8,30#u8],by rfl⟩
def limbs15 : QM31Limbs := ![⟨852679865,by omega⟩,⟨91829264,by omega⟩,⟨1631183265,by omega⟩,⟨508850346,by omega⟩]
theorem encoded15 : CandidateParserByteOrder.arrayBytes16 cell15=encodeQM31LE limbs15 := by
  funext i
  fin_cases i <;> rfl
theorem parser15 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell15)=
    ok (some ⟨⟨852679865#u32,91829264#u32⟩,⟨1631183265#u32,508850346#u32⟩⟩) :=
  JFr_EncodedCell.parser cell15 limbs15 encoded15
#print axioms encoded15
#print axioms parser15
def cell16 : Array U8 16#usize := ⟨[199#u8,227#u8,162#u8,38#u8,11#u8,125#u8,191#u8,53#u8,96#u8,162#u8,98#u8,73#u8,19#u8,196#u8,190#u8,90#u8],by rfl⟩
def limbs16 : QM31Limbs := ![⟨648209351,by omega⟩,⟨901741835,by omega⟩,⟨1231200864,by omega⟩,⟨1522451475,by omega⟩]
theorem encoded16 : CandidateParserByteOrder.arrayBytes16 cell16=encodeQM31LE limbs16 := by
  funext i
  fin_cases i <;> rfl
theorem parser16 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell16)=
    ok (some ⟨⟨648209351#u32,901741835#u32⟩,⟨1231200864#u32,1522451475#u32⟩⟩) :=
  JFr_EncodedCell.parser cell16 limbs16 encoded16
#print axioms encoded16
#print axioms parser16
def cell17 : Array U8 16#usize := ⟨[29#u8,234#u8,3#u8,96#u8,63#u8,57#u8,173#u8,9#u8,137#u8,155#u8,170#u8,118#u8,61#u8,121#u8,125#u8,62#u8],by rfl⟩
def limbs17 : QM31Limbs := ![⟨1610869277,by omega⟩,⟨162347327,by omega⟩,⟨1990892425,by omega⟩,⟨1048410429,by omega⟩]
theorem encoded17 : CandidateParserByteOrder.arrayBytes16 cell17=encodeQM31LE limbs17 := by
  funext i
  fin_cases i <;> rfl
theorem parser17 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell17)=
    ok (some ⟨⟨1610869277#u32,162347327#u32⟩,⟨1990892425#u32,1048410429#u32⟩⟩) :=
  JFr_EncodedCell.parser cell17 limbs17 encoded17
#print axioms encoded17
#print axioms parser17
def cell18 : Array U8 16#usize := ⟨[19#u8,191#u8,43#u8,28#u8,138#u8,7#u8,27#u8,105#u8,63#u8,177#u8,233#u8,51#u8,72#u8,218#u8,115#u8,4#u8],by rfl⟩
def limbs18 : QM31Limbs := ![⟨472629011,by omega⟩,⟨1763379082,by omega⟩,⟨870953279,by omega⟩,⟨74701384,by omega⟩]
theorem encoded18 : CandidateParserByteOrder.arrayBytes16 cell18=encodeQM31LE limbs18 := by
  funext i
  fin_cases i <;> rfl
theorem parser18 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell18)=
    ok (some ⟨⟨472629011#u32,1763379082#u32⟩,⟨870953279#u32,74701384#u32⟩⟩) :=
  JFr_EncodedCell.parser cell18 limbs18 encoded18
#print axioms encoded18
#print axioms parser18
def cell19 : Array U8 16#usize := ⟨[101#u8,90#u8,97#u8,20#u8,144#u8,114#u8,156#u8,122#u8,219#u8,166#u8,194#u8,109#u8,155#u8,150#u8,14#u8,99#u8],by rfl⟩
def limbs19 : QM31Limbs := ![⟨341924453,by omega⟩,⟨2057073296,by omega⟩,⟨1841473243,by omega⟩,⟨1661900443,by omega⟩]
theorem encoded19 : CandidateParserByteOrder.arrayBytes16 cell19=encodeQM31LE limbs19 := by
  funext i
  fin_cases i <;> rfl
theorem parser19 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell19)=
    ok (some ⟨⟨341924453#u32,2057073296#u32⟩,⟨1841473243#u32,1661900443#u32⟩⟩) :=
  JFr_EncodedCell.parser cell19 limbs19 encoded19
#print axioms encoded19
#print axioms parser19
def cell20 : Array U8 16#usize := ⟨[61#u8,18#u8,139#u8,123#u8,63#u8,48#u8,137#u8,22#u8,90#u8,13#u8,54#u8,97#u8,40#u8,141#u8,189#u8,40#u8],by rfl⟩
def limbs20 : QM31Limbs := ![⟨2072711741,by omega⟩,⟨378089535,by omega⟩,⟨1630932314,by omega⟩,⟨683511080,by omega⟩]
theorem encoded20 : CandidateParserByteOrder.arrayBytes16 cell20=encodeQM31LE limbs20 := by
  funext i
  fin_cases i <;> rfl
theorem parser20 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell20)=
    ok (some ⟨⟨2072711741#u32,378089535#u32⟩,⟨1630932314#u32,683511080#u32⟩⟩) :=
  JFr_EncodedCell.parser cell20 limbs20 encoded20
#print axioms encoded20
#print axioms parser20
def cell21 : Array U8 16#usize := ⟨[220#u8,131#u8,79#u8,24#u8,181#u8,246#u8,109#u8,103#u8,149#u8,226#u8,248#u8,109#u8,201#u8,78#u8,1#u8,72#u8],by rfl⟩
def limbs21 : QM31Limbs := ![⟨407864284,by omega⟩,⟨1735259829,by omega⟩,⟨1845027477,by omega⟩,⟨1208045257,by omega⟩]
theorem encoded21 : CandidateParserByteOrder.arrayBytes16 cell21=encodeQM31LE limbs21 := by
  funext i
  fin_cases i <;> rfl
theorem parser21 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell21)=
    ok (some ⟨⟨407864284#u32,1735259829#u32⟩,⟨1845027477#u32,1208045257#u32⟩⟩) :=
  JFr_EncodedCell.parser cell21 limbs21 encoded21
#print axioms encoded21
#print axioms parser21
def cell22 : Array U8 16#usize := ⟨[12#u8,149#u8,139#u8,78#u8,145#u8,236#u8,144#u8,103#u8,120#u8,97#u8,101#u8,109#u8,203#u8,136#u8,139#u8,69#u8],by rfl⟩
def limbs22 : QM31Limbs := ![⟨1317770508,by omega⟩,⟨1737550993,by omega⟩,⟨1835360632,by omega⟩,⟨1166772427,by omega⟩]
theorem encoded22 : CandidateParserByteOrder.arrayBytes16 cell22=encodeQM31LE limbs22 := by
  funext i
  fin_cases i <;> rfl
theorem parser22 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell22)=
    ok (some ⟨⟨1317770508#u32,1737550993#u32⟩,⟨1835360632#u32,1166772427#u32⟩⟩) :=
  JFr_EncodedCell.parser cell22 limbs22 encoded22
#print axioms encoded22
#print axioms parser22
def cell23 : Array U8 16#usize := ⟨[8#u8,125#u8,199#u8,34#u8,167#u8,117#u8,184#u8,24#u8,223#u8,167#u8,149#u8,46#u8,22#u8,104#u8,205#u8,81#u8],by rfl⟩
def limbs23 : QM31Limbs := ![⟨583499016,by omega⟩,⟨414741927,by omega⟩,⟨781559775,by omega⟩,⟨1372416022,by omega⟩]
theorem encoded23 : CandidateParserByteOrder.arrayBytes16 cell23=encodeQM31LE limbs23 := by
  funext i
  fin_cases i <;> rfl
theorem parser23 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell23)=
    ok (some ⟨⟨583499016#u32,414741927#u32⟩,⟨781559775#u32,1372416022#u32⟩⟩) :=
  JFr_EncodedCell.parser cell23 limbs23 encoded23
#print axioms encoded23
#print axioms parser23
def cell24 : Array U8 16#usize := ⟨[5#u8,1#u8,133#u8,94#u8,221#u8,56#u8,151#u8,23#u8,193#u8,115#u8,107#u8,30#u8,62#u8,62#u8,150#u8,62#u8],by rfl⟩
def limbs24 : QM31Limbs := ![⟨1585774853,by omega⟩,⟨395786461,by omega⟩,⟨510358465,by omega⟩,⟨1050033726,by omega⟩]
theorem encoded24 : CandidateParserByteOrder.arrayBytes16 cell24=encodeQM31LE limbs24 := by
  funext i
  fin_cases i <;> rfl
theorem parser24 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell24)=
    ok (some ⟨⟨1585774853#u32,395786461#u32⟩,⟨510358465#u32,1050033726#u32⟩⟩) :=
  JFr_EncodedCell.parser cell24 limbs24 encoded24
#print axioms encoded24
#print axioms parser24
def cell25 : Array U8 16#usize := ⟨[70#u8,80#u8,59#u8,95#u8,176#u8,117#u8,60#u8,101#u8,11#u8,33#u8,68#u8,13#u8,61#u8,244#u8,184#u8,23#u8],by rfl⟩
def limbs25 : QM31Limbs := ![⟨1597722694,by omega⟩,⟨1698461104,by omega⟩,⟨222568715,by omega⟩,⟨397997117,by omega⟩]
theorem encoded25 : CandidateParserByteOrder.arrayBytes16 cell25=encodeQM31LE limbs25 := by
  funext i
  fin_cases i <;> rfl
theorem parser25 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell25)=
    ok (some ⟨⟨1597722694#u32,1698461104#u32⟩,⟨222568715#u32,397997117#u32⟩⟩) :=
  JFr_EncodedCell.parser cell25 limbs25 encoded25
#print axioms encoded25
#print axioms parser25
def cell26 : Array U8 16#usize := ⟨[212#u8,24#u8,224#u8,48#u8,156#u8,246#u8,220#u8,63#u8,33#u8,60#u8,34#u8,7#u8,203#u8,207#u8,107#u8,102#u8],by rfl⟩
def limbs26 : QM31Limbs := ![⟨819992788,by omega⟩,⟨1071445660,by omega⟩,⟨119684129,by omega⟩,⟨1718341579,by omega⟩]
theorem encoded26 : CandidateParserByteOrder.arrayBytes16 cell26=encodeQM31LE limbs26 := by
  funext i
  fin_cases i <;> rfl
theorem parser26 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell26)=
    ok (some ⟨⟨819992788#u32,1071445660#u32⟩,⟨119684129#u32,1718341579#u32⟩⟩) :=
  JFr_EncodedCell.parser cell26 limbs26 encoded26
#print axioms encoded26
#print axioms parser26
def cell27 : Array U8 16#usize := ⟨[181#u8,85#u8,202#u8,104#u8,210#u8,28#u8,177#u8,75#u8,44#u8,251#u8,0#u8,36#u8,53#u8,48#u8,19#u8,124#u8],by rfl⟩
def limbs27 : QM31Limbs := ![⟨1758090677,by omega⟩,⟨1269898450,by omega⟩,⟨604044076,by omega⟩,⟨2081632309,by omega⟩]
theorem encoded27 : CandidateParserByteOrder.arrayBytes16 cell27=encodeQM31LE limbs27 := by
  funext i
  fin_cases i <;> rfl
theorem parser27 : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell27)=
    ok (some ⟨⟨1758090677#u32,1269898450#u32⟩,⟨604044076#u32,2081632309#u32⟩⟩) :=
  JFr_EncodedCell.parser cell27 limbs27 encoded27
#print axioms encoded27
#print axioms parser27
end AspisR1.JFr_Bytes00
