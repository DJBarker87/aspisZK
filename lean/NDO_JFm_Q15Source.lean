import JFm_BlockSplit
import NDO_JFm_Q14Source
import NDO_JFw_NativeRow15
import RPz7_ExtractedDigest32SamplerTransport
import NDO_JFm_Q15Hashes
set_option autoImplicit false
namespace AspisR1.JFm_Q15Source
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
abbrev frame : Slice U8 := JFw_NativeRow15.record
def absorbed : State := JFp_SHADigest.output JFm_Q15Absorb.result
def block : State := JFp_SHADigest.output JFm_Q15Read.result
def ratchet : State := JFp_SHADigest.output JFm_Q15Ratchet.result
def record : r1_wire.ValidatedRecord := ⟨15#u8,JFw_NativeRow15.record⟩
theorem realFrame : JFw_NativeRow15.record=frame := by
  apply Subtype.ext
  rfl
#print axioms realFrame
namespace Input
def p00 : List U8 := [99#u8,86#u8,145#u8,41#u8,100#u8,145#u8,4#u8,76#u8,116#u8,68#u8,92#u8,76#u8,27#u8,166#u8,182#u8,124#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p01 : List U8 := [100#u8,194#u8,9#u8,67#u8,252#u8,217#u8,69#u8,19#u8,121#u8,112#u8,179#u8,121#u8,236#u8,235#u8,223#u8,34#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p02 : List U8 := [83#u8,0#u8,50#u8,74#u8,206#u8,93#u8,15#u8,31#u8,177#u8,191#u8,80#u8,71#u8,185#u8,49#u8,25#u8,66#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p03 : List U8 := [181#u8,34#u8,22#u8,85#u8,167#u8,76#u8,5#u8,50#u8,130#u8,191#u8,97#u8,78#u8,245#u8,122#u8,118#u8,95#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p04 : List U8 := [100#u8,189#u8,184#u8,28#u8,73#u8,131#u8,141#u8,21#u8,229#u8,171#u8,140#u8,122#u8,212#u8,214#u8,10#u8,28#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p05 : List U8 := [189#u8,29#u8,186#u8,120#u8,112#u8,227#u8,81#u8,94#u8,155#u8,33#u8,30#u8,63#u8,130#u8,71#u8,23#u8,96#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p06 : List U8 := [195#u8,108#u8,170#u8,79#u8,38#u8,88#u8,39#u8,30#u8,191#u8,229#u8,232#u8,48#u8,224#u8,199#u8,222#u8,70#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p07 : List U8 := [128#u8,17#u8,208#u8,68#u8,74#u8,118#u8,79#u8,40#u8,7#u8,111#u8,126#u8,83#u8,135#u8,96#u8,56#u8,27#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p08 : List U8 := [19#u8,27#u8,59#u8,109#u8,90#u8,136#u8,93#u8,97#u8,127#u8,60#u8,28#u8,83#u8,58#u8,130#u8,103#u8,32#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p09 : List U8 := [163#u8,29#u8,155#u8,2#u8,64#u8,60#u8,111#u8,88#u8,189#u8,234#u8,229#u8,3#u8,124#u8,152#u8,193#u8,93#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p10 : List U8 := [16#u8,113#u8,87#u8,51#u8,155#u8,168#u8,114#u8,119#u8,44#u8,3#u8,255#u8,69#u8,254#u8,241#u8,162#u8,65#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p11 : List U8 := [210#u8,190#u8,190#u8,35#u8,195#u8,190#u8,22#u8,43#u8,151#u8,69#u8,6#u8,40#u8,194#u8,124#u8,92#u8,29#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p12 : List U8 := [148#u8,1#u8,73#u8,81#u8,62#u8,177#u8,14#u8,3#u8,148#u8,46#u8,206#u8,87#u8,195#u8,221#u8,59#u8,112#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p13 : List U8 := [198#u8,124#u8,253#u8,79#u8,91#u8,27#u8,190#u8,53#u8,65#u8,151#u8,89#u8,55#u8,251#u8,200#u8,119#u8,73#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p14 : List U8 := [242#u8,196#u8,49#u8,118#u8,39#u8,159#u8,39#u8,97#u8,37#u8,178#u8,199#u8,44#u8,142#u8,73#u8,38#u8,97#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p15 : List U8 := [185#u8,220#u8,210#u8,50#u8,16#u8,52#u8,121#u8,5#u8,161#u8,225#u8,57#u8,97#u8,170#u8,112#u8,84#u8,30#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p16 : List U8 := [199#u8,227#u8,162#u8,38#u8,11#u8,125#u8,191#u8,53#u8,96#u8,162#u8,98#u8,73#u8,19#u8,196#u8,190#u8,90#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p17 : List U8 := [29#u8,234#u8,3#u8,96#u8,63#u8,57#u8,173#u8,9#u8,137#u8,155#u8,170#u8,118#u8,61#u8,121#u8,125#u8,62#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p18 : List U8 := [19#u8,191#u8,43#u8,28#u8,138#u8,7#u8,27#u8,105#u8,63#u8,177#u8,233#u8,51#u8,72#u8,218#u8,115#u8,4#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p19 : List U8 := [101#u8,90#u8,97#u8,20#u8,144#u8,114#u8,156#u8,122#u8,219#u8,166#u8,194#u8,109#u8,155#u8,150#u8,14#u8,99#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p20 : List U8 := [61#u8,18#u8,139#u8,123#u8,63#u8,48#u8,137#u8,22#u8,90#u8,13#u8,54#u8,97#u8,40#u8,141#u8,189#u8,40#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p21 : List U8 := [220#u8,131#u8,79#u8,24#u8,181#u8,246#u8,109#u8,103#u8,149#u8,226#u8,248#u8,109#u8,201#u8,78#u8,1#u8,72#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p22 : List U8 := [12#u8,149#u8,139#u8,78#u8,145#u8,236#u8,144#u8,103#u8,120#u8,97#u8,101#u8,109#u8,203#u8,136#u8,139#u8,69#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p23 : List U8 := [8#u8,125#u8,199#u8,34#u8,167#u8,117#u8,184#u8,24#u8,223#u8,167#u8,149#u8,46#u8,22#u8,104#u8,205#u8,81#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p24 : List U8 := [5#u8,1#u8,133#u8,94#u8,221#u8,56#u8,151#u8,23#u8,193#u8,115#u8,107#u8,30#u8,62#u8,62#u8,150#u8,62#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p25 : List U8 := [70#u8,80#u8,59#u8,95#u8,176#u8,117#u8,60#u8,101#u8,11#u8,33#u8,68#u8,13#u8,61#u8,244#u8,184#u8,23#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p26 : List U8 := [212#u8,24#u8,224#u8,48#u8,156#u8,246#u8,220#u8,63#u8,33#u8,60#u8,34#u8,7#u8,203#u8,207#u8,107#u8,102#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p27 : List U8 := [181#u8,85#u8,202#u8,104#u8,210#u8,28#u8,177#u8,75#u8,44#u8,251#u8,0#u8,36#u8,53#u8,48#u8,19#u8,124#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
theorem blocks_b00 : JFw_Blocks.blocks 2 JFz_Scan48.b00=[p00,p01] := by rfl
#print axioms blocks_b00
theorem blocks_b01 : JFw_Blocks.blocks 2 JFz_Scan48.b01=[p02,p03] := by rfl
#print axioms blocks_b01
theorem blocks_b02 : JFw_Blocks.blocks 2 JFz_Scan48.b02=[p04,p05] := by rfl
#print axioms blocks_b02
theorem blocks_b03 : JFw_Blocks.blocks 2 JFz_Scan48.b03=[p06,p07] := by rfl
#print axioms blocks_b03
theorem blocks_b04 : JFw_Blocks.blocks 2 JFz_Scan48.b04=[p08,p09] := by rfl
#print axioms blocks_b04
theorem blocks_b05 : JFw_Blocks.blocks 2 JFz_Scan48.b05=[p10,p11] := by rfl
#print axioms blocks_b05
theorem blocks_b06 : JFw_Blocks.blocks 2 JFz_Scan48.b06=[p12,p13] := by rfl
#print axioms blocks_b06
theorem blocks_b07 : JFw_Blocks.blocks 2 JFz_Scan48.b07=[p14,p15] := by rfl
#print axioms blocks_b07
theorem blocks_b08 : JFw_Blocks.blocks 2 JFz_Scan48.b08=[p16,p17] := by rfl
#print axioms blocks_b08
theorem blocks_b09 : JFw_Blocks.blocks 2 JFz_Scan48.b09=[p18,p19] := by rfl
#print axioms blocks_b09
theorem blocks_b10 : JFw_Blocks.blocks 2 JFz_Scan48.b10=[p20,p21] := by rfl
#print axioms blocks_b10
theorem blocks_b11 : JFw_Blocks.blocks 2 JFz_Scan48.b11=[p22,p23] := by rfl
#print axioms blocks_b11
theorem blocks_b12 : JFw_Blocks.blocks 2 JFz_Scan48.b12=[p24,p25] := by rfl
#print axioms blocks_b12
theorem blocks_b13 : JFw_Blocks.blocks 2 JFz_Scan48.b13=[p26,p27] := by rfl
#print axioms blocks_b13
theorem blocks_j00 : JFw_Blocks.blocks 4 JFz_Scan48.j00=[p02,p03,p04,p05] := by
  rw [JFz_Scan48.j00,JFm_BlockSplit.append 2 2 _ _ JFz_Scan48.b01_length,blocks_b01,blocks_b02]
  rfl
#print axioms blocks_j00
theorem blocks_j01 : JFw_Blocks.blocks 6 JFz_Scan48.j01=[p00,p01,p02,p03,p04,p05] := by
  rw [JFz_Scan48.j01,JFm_BlockSplit.append 2 4 _ _ JFz_Scan48.b00_length,blocks_b00,blocks_j00]
  rfl
#print axioms blocks_j01
theorem blocks_j02 : JFw_Blocks.blocks 4 JFz_Scan48.j02=[p06,p07,p08,p09] := by
  rw [JFz_Scan48.j02,JFm_BlockSplit.append 2 2 _ _ JFz_Scan48.b03_length,blocks_b03,blocks_b04]
  rfl
#print axioms blocks_j02
theorem blocks_j03 : JFw_Blocks.blocks 4 JFz_Scan48.j03=[p10,p11,p12,p13] := by
  rw [JFz_Scan48.j03,JFm_BlockSplit.append 2 2 _ _ JFz_Scan48.b05_length,blocks_b05,blocks_b06]
  rfl
#print axioms blocks_j03
theorem blocks_j04 : JFw_Blocks.blocks 8 JFz_Scan48.j04=[p06,p07,p08,p09,p10,p11,p12,p13] := by
  rw [JFz_Scan48.j04,JFm_BlockSplit.append 4 4 _ _ JFz_Scan48.j02_length,blocks_j02,blocks_j03]
  rfl
#print axioms blocks_j04
theorem blocks_j05 : JFw_Blocks.blocks 14 JFz_Scan48.j05=[p00,p01,p02,p03,p04,p05,p06,p07,p08,p09,p10,p11,p12,p13] := by
  rw [JFz_Scan48.j05,JFm_BlockSplit.append 6 8 _ _ JFz_Scan48.j01_length,blocks_j01,blocks_j04]
  rfl
#print axioms blocks_j05
theorem blocks_j06 : JFw_Blocks.blocks 4 JFz_Scan48.j06=[p16,p17,p18,p19] := by
  rw [JFz_Scan48.j06,JFm_BlockSplit.append 2 2 _ _ JFz_Scan48.b08_length,blocks_b08,blocks_b09]
  rfl
#print axioms blocks_j06
theorem blocks_j07 : JFw_Blocks.blocks 6 JFz_Scan48.j07=[p14,p15,p16,p17,p18,p19] := by
  rw [JFz_Scan48.j07,JFm_BlockSplit.append 2 4 _ _ JFz_Scan48.b07_length,blocks_b07,blocks_j06]
  rfl
#print axioms blocks_j07
theorem blocks_j08 : JFw_Blocks.blocks 4 JFz_Scan48.j08=[p20,p21,p22,p23] := by
  rw [JFz_Scan48.j08,JFm_BlockSplit.append 2 2 _ _ JFz_Scan48.b10_length,blocks_b10,blocks_b11]
  rfl
#print axioms blocks_j08
theorem blocks_j09 : JFw_Blocks.blocks 4 JFz_Scan48.j09=[p24,p25,p26,p27] := by
  rw [JFz_Scan48.j09,JFm_BlockSplit.append 2 2 _ _ JFz_Scan48.b12_length,blocks_b12,blocks_b13]
  rfl
#print axioms blocks_j09
theorem blocks_j10 : JFw_Blocks.blocks 8 JFz_Scan48.j10=[p20,p21,p22,p23,p24,p25,p26,p27] := by
  rw [JFz_Scan48.j10,JFm_BlockSplit.append 4 4 _ _ JFz_Scan48.j08_length,blocks_j08,blocks_j09]
  rfl
#print axioms blocks_j10
theorem blocks_j11 : JFw_Blocks.blocks 14 JFz_Scan48.j11=[p14,p15,p16,p17,p18,p19,p20,p21,p22,p23,p24,p25,p26,p27] := by
  rw [JFz_Scan48.j11,JFm_BlockSplit.append 6 8 _ _ JFz_Scan48.j07_length,blocks_j07,blocks_j10]
  rfl
#print axioms blocks_j11
theorem blocks_j12 : JFw_Blocks.blocks 28 JFz_Scan48.j12=[p00,p01,p02,p03,p04,p05,p06,p07,p08,p09,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20,p21,p22,p23,p24,p25,p26,p27] := by
  rw [JFz_Scan48.j12,JFm_BlockSplit.append 14 14 _ _ JFz_Scan48.j05_length,blocks_j05,blocks_j11]
  rfl
#print axioms blocks_j12
def sourcePayload : List U8 := [p00,p01,p02,p03,p04,p05,p06,p07,p08,p09,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20,p21,p22,p23,p24,p25,p26,p27].flatten
theorem payloadBytes : JFw_NativeRow15.payload.val=sourcePayload := by
  change (JFw_Blocks.blocks 28 ((JFx_NativeBytes.proof.val.drop 176).take 448)).flatten=_
  rw [JFz_Scan48.selected]
  unfold JFz_Scan48.data
  rw [blocks_j12]
  rfl
#print axioms payloadBytes
theorem frameBytes : JFw_NativeRow15.record.val=[2#u8,128#u8,3#u8,0#u8,0#u8] ++ sourcePayload := by
  change _::_::_::_::_::JFw_NativeRow15.payload.val=_
  rw [payloadBytes]
  rfl
#print axioms frameBytes
def n00 : List Nat := [113,194,101,184,219,75,14,211,138,202,69,134,112,236,151,108,191,103,97,136,10,66,191,250,205,48,185,88,133,64,18,34,0,175,2,128,3,0,0]
def n01 : List Nat := [99,86,145,41,100,145,4,76,116,68,92,76,27,166,182,124,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast01 : (p00).map (fun x=>x.val)=n01 := by rfl
#print axioms cast01
def n02 : List Nat := [100,194,9,67,252,217,69,19,121,112,179,121,236,235,223,34,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast02 : (p01).map (fun x=>x.val)=n02 := by rfl
#print axioms cast02
def n03 : List Nat := [83,0,50,74,206,93,15,31,177,191,80,71,185,49,25,66,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast03 : (p02).map (fun x=>x.val)=n03 := by rfl
#print axioms cast03
def n04 : List Nat := [181,34,22,85,167,76,5,50,130,191,97,78,245,122,118,95,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast04 : (p03).map (fun x=>x.val)=n04 := by rfl
#print axioms cast04
def n05 : List Nat := [100,189,184,28,73,131,141,21,229,171,140,122,212,214,10,28,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast05 : (p04).map (fun x=>x.val)=n05 := by rfl
#print axioms cast05
def n06 : List Nat := [189,29,186,120,112,227,81,94,155,33,30,63,130,71,23,96,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast06 : (p05).map (fun x=>x.val)=n06 := by rfl
#print axioms cast06
def n07 : List Nat := [195,108,170,79,38,88,39,30,191,229,232,48,224,199,222,70,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast07 : (p06).map (fun x=>x.val)=n07 := by rfl
#print axioms cast07
def n08 : List Nat := [128,17,208,68,74,118,79,40,7,111,126,83,135,96,56,27,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast08 : (p07).map (fun x=>x.val)=n08 := by rfl
#print axioms cast08
def n09 : List Nat := [19,27,59,109,90,136,93,97,127,60,28,83,58,130,103,32,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast09 : (p08).map (fun x=>x.val)=n09 := by rfl
#print axioms cast09
def n10 : List Nat := [163,29,155,2,64,60,111,88,189,234,229,3,124,152,193,93,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast10 : (p09).map (fun x=>x.val)=n10 := by rfl
#print axioms cast10
def n11 : List Nat := [16,113,87,51,155,168,114,119,44,3,255,69,254,241,162,65,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast11 : (p10).map (fun x=>x.val)=n11 := by rfl
#print axioms cast11
def n12 : List Nat := [210,190,190,35,195,190,22,43,151,69,6,40,194,124,92,29,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast12 : (p11).map (fun x=>x.val)=n12 := by rfl
#print axioms cast12
def n13 : List Nat := [148,1,73,81,62,177,14,3,148,46,206,87,195,221,59,112,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast13 : (p12).map (fun x=>x.val)=n13 := by rfl
#print axioms cast13
def n14 : List Nat := [198,124,253,79,91,27,190,53,65,151,89,55,251,200,119,73,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast14 : (p13).map (fun x=>x.val)=n14 := by rfl
#print axioms cast14
def n15 : List Nat := [242,196,49,118,39,159,39,97,37,178,199,44,142,73,38,97,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast15 : (p14).map (fun x=>x.val)=n15 := by rfl
#print axioms cast15
def n16 : List Nat := [185,220,210,50,16,52,121,5,161,225,57,97,170,112,84,30,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast16 : (p15).map (fun x=>x.val)=n16 := by rfl
#print axioms cast16
def n17 : List Nat := [199,227,162,38,11,125,191,53,96,162,98,73,19,196,190,90,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast17 : (p16).map (fun x=>x.val)=n17 := by rfl
#print axioms cast17
def n18 : List Nat := [29,234,3,96,63,57,173,9,137,155,170,118,61,121,125,62,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast18 : (p17).map (fun x=>x.val)=n18 := by rfl
#print axioms cast18
def n19 : List Nat := [19,191,43,28,138,7,27,105,63,177,233,51,72,218,115,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast19 : (p18).map (fun x=>x.val)=n19 := by rfl
#print axioms cast19
def n20 : List Nat := [101,90,97,20,144,114,156,122,219,166,194,109,155,150,14,99,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast20 : (p19).map (fun x=>x.val)=n20 := by rfl
#print axioms cast20
def n21 : List Nat := [61,18,139,123,63,48,137,22,90,13,54,97,40,141,189,40,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast21 : (p20).map (fun x=>x.val)=n21 := by rfl
#print axioms cast21
def n22 : List Nat := [220,131,79,24,181,246,109,103,149,226,248,109,201,78,1,72,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast22 : (p21).map (fun x=>x.val)=n22 := by rfl
#print axioms cast22
def n23 : List Nat := [12,149,139,78,145,236,144,103,120,97,101,109,203,136,139,69,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast23 : (p22).map (fun x=>x.val)=n23 := by rfl
#print axioms cast23
def n24 : List Nat := [8,125,199,34,167,117,184,24,223,167,149,46,22,104,205,81,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast24 : (p23).map (fun x=>x.val)=n24 := by rfl
#print axioms cast24
def n25 : List Nat := [5,1,133,94,221,56,151,23,193,115,107,30,62,62,150,62,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast25 : (p24).map (fun x=>x.val)=n25 := by rfl
#print axioms cast25
def n26 : List Nat := [70,80,59,95,176,117,60,101,11,33,68,13,61,244,184,23,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast26 : (p25).map (fun x=>x.val)=n26 := by rfl
#print axioms cast26
def n27 : List Nat := [212,24,224,48,156,246,220,63,33,60,34,7,203,207,107,102,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast27 : (p26).map (fun x=>x.val)=n27 := by rfl
#print axioms cast27
def n28 : List Nat := [181,85,202,104,210,28,177,75,44,251,0,36,53,48,19,124,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast28 : (p27).map (fun x=>x.val)=n28 := by rfl
#print axioms cast28
def numeric : List Nat := n00 ++ n01 ++ n02 ++ n03 ++ n04 ++ n05 ++ n06 ++ n07 ++ n08 ++ n09 ++ n10 ++ n11 ++ n12 ++ n13 ++ n14 ++ n15 ++ n16 ++ n17 ++ n18 ++ n19 ++ n20 ++ n21 ++ n22 ++ n23 ++ n24 ++ n25 ++ n26 ++ n27 ++ n28
theorem payloadNat : sourcePayload.map (fun x=>x.val)=n01 ++ n02 ++ n03 ++ n04 ++ n05 ++ n06 ++ n07 ++ n08 ++ n09 ++ n10 ++ n11 ++ n12 ++ n13 ++ n14 ++ n15 ++ n16 ++ n17 ++ n18 ++ n19 ++ n20 ++ n21 ++ n22 ++ n23 ++ n24 ++ n25 ++ n26 ++ n27 ++ n28 := by
  simp only [sourcePayload,List.flatten_cons,List.flatten_nil,List.map_append,List.map_nil,List.append_nil,List.append_assoc,cast01,cast02,cast03,cast04,cast05,cast06,cast07,cast08,cast09,cast10,cast11,cast12,cast13,cast14,cast15,cast16,cast17,cast18,cast19,cast20,cast21,cast22,cast23,cast24,cast25,cast26,cast27,cast28]
#print axioms payloadNat
theorem prefixCast : ((encodeState JFm_Q14Source.ratchet).val.map (fun x=>x.val)) ++ [0,175] ++ [2,128,3,0,0]=n00 := by rfl
#print axioms prefixCast
def rest00 : List Nat := n00 ++ n01 ++ n02 ++ n03 ++ n04 ++ n05 ++ n06 ++ n07 ++ n08 ++ n09 ++ n10 ++ n11 ++ n12 ++ n13 ++ n14 ++ n15 ++ n16 ++ n17 ++ n18 ++ n19 ++ n20 ++ n21 ++ n22 ++ n23 ++ n24 ++ n25 ++ n26 ++ n27 ++ n28
def rest01 : List Nat := (n01.drop 25) ++ n02 ++ n03 ++ n04 ++ n05 ++ n06 ++ n07 ++ n08 ++ n09 ++ n10 ++ n11 ++ n12 ++ n13 ++ n14 ++ n15 ++ n16 ++ n17 ++ n18 ++ n19 ++ n20 ++ n21 ++ n22 ++ n23 ++ n24 ++ n25 ++ n26 ++ n27 ++ n28
def rest02 : List Nat := (n03.drop 25) ++ n04 ++ n05 ++ n06 ++ n07 ++ n08 ++ n09 ++ n10 ++ n11 ++ n12 ++ n13 ++ n14 ++ n15 ++ n16 ++ n17 ++ n18 ++ n19 ++ n20 ++ n21 ++ n22 ++ n23 ++ n24 ++ n25 ++ n26 ++ n27 ++ n28
def rest03 : List Nat := (n05.drop 25) ++ n06 ++ n07 ++ n08 ++ n09 ++ n10 ++ n11 ++ n12 ++ n13 ++ n14 ++ n15 ++ n16 ++ n17 ++ n18 ++ n19 ++ n20 ++ n21 ++ n22 ++ n23 ++ n24 ++ n25 ++ n26 ++ n27 ++ n28
def rest04 : List Nat := (n07.drop 25) ++ n08 ++ n09 ++ n10 ++ n11 ++ n12 ++ n13 ++ n14 ++ n15 ++ n16 ++ n17 ++ n18 ++ n19 ++ n20 ++ n21 ++ n22 ++ n23 ++ n24 ++ n25 ++ n26 ++ n27 ++ n28
def rest05 : List Nat := (n09.drop 25) ++ n10 ++ n11 ++ n12 ++ n13 ++ n14 ++ n15 ++ n16 ++ n17 ++ n18 ++ n19 ++ n20 ++ n21 ++ n22 ++ n23 ++ n24 ++ n25 ++ n26 ++ n27 ++ n28
def rest06 : List Nat := (n11.drop 25) ++ n12 ++ n13 ++ n14 ++ n15 ++ n16 ++ n17 ++ n18 ++ n19 ++ n20 ++ n21 ++ n22 ++ n23 ++ n24 ++ n25 ++ n26 ++ n27 ++ n28
def rest07 : List Nat := (n13.drop 25) ++ n14 ++ n15 ++ n16 ++ n17 ++ n18 ++ n19 ++ n20 ++ n21 ++ n22 ++ n23 ++ n24 ++ n25 ++ n26 ++ n27 ++ n28
def rest08 : List Nat := (n15.drop 25) ++ n16 ++ n17 ++ n18 ++ n19 ++ n20 ++ n21 ++ n22 ++ n23 ++ n24 ++ n25 ++ n26 ++ n27 ++ n28
def rest09 : List Nat := (n17.drop 25) ++ n18 ++ n19 ++ n20 ++ n21 ++ n22 ++ n23 ++ n24 ++ n25 ++ n26 ++ n27 ++ n28
def rest10 : List Nat := (n19.drop 25) ++ n20 ++ n21 ++ n22 ++ n23 ++ n24 ++ n25 ++ n26 ++ n27 ++ n28
def rest11 : List Nat := (n21.drop 25) ++ n22 ++ n23 ++ n24 ++ n25 ++ n26 ++ n27 ++ n28
def rest12 : List Nat := (n23.drop 25) ++ n24 ++ n25 ++ n26 ++ n27 ++ n28
def rest13 : List Nat := (n25.drop 25) ++ n26 ++ n27 ++ n28
def rest14 : List Nat := (n27.drop 25) ++ n28
theorem step00 : rest00=JFm_Q15Absorb.B00.input ++ rest01 := by
  simp only [rest00,rest01,n00,n01]
  rfl
#print axioms step00
theorem step01 : rest01=JFm_Q15Absorb.B01.input ++ rest02 := by
  simp only [rest01,rest02,n01,n02,n03]
  rfl
#print axioms step01
theorem step02 : rest02=JFm_Q15Absorb.B02.input ++ rest03 := by
  simp only [rest02,rest03,n03,n04,n05]
  rfl
#print axioms step02
theorem step03 : rest03=JFm_Q15Absorb.B03.input ++ rest04 := by
  simp only [rest03,rest04,n05,n06,n07]
  rfl
#print axioms step03
theorem step04 : rest04=JFm_Q15Absorb.B04.input ++ rest05 := by
  simp only [rest04,rest05,n07,n08,n09]
  rfl
#print axioms step04
theorem step05 : rest05=JFm_Q15Absorb.B05.input ++ rest06 := by
  simp only [rest05,rest06,n09,n10,n11]
  rfl
#print axioms step05
theorem step06 : rest06=JFm_Q15Absorb.B06.input ++ rest07 := by
  simp only [rest06,rest07,n11,n12,n13]
  rfl
#print axioms step06
theorem step07 : rest07=JFm_Q15Absorb.B07.input ++ rest08 := by
  simp only [rest07,rest08,n13,n14,n15]
  rfl
#print axioms step07
theorem step08 : rest08=JFm_Q15Absorb.B08.input ++ rest09 := by
  simp only [rest08,rest09,n15,n16,n17]
  rfl
#print axioms step08
theorem step09 : rest09=JFm_Q15Absorb.B09.input ++ rest10 := by
  simp only [rest09,rest10,n17,n18,n19]
  rfl
#print axioms step09
theorem step10 : rest10=JFm_Q15Absorb.B10.input ++ rest11 := by
  simp only [rest10,rest11,n19,n20,n21]
  rfl
#print axioms step10
theorem step11 : rest11=JFm_Q15Absorb.B11.input ++ rest12 := by
  simp only [rest11,rest12,n21,n22,n23]
  rfl
#print axioms step11
theorem step12 : rest12=JFm_Q15Absorb.B12.input ++ rest13 := by
  simp only [rest12,rest13,n23,n24,n25]
  rfl
#print axioms step12
theorem step13 : rest13=JFm_Q15Absorb.B13.input ++ rest14 := by
  simp only [rest13,rest14,n25,n26,n27]
  rfl
#print axioms step13
theorem last : rest14=JFm_Q15Absorb.tail := by
  simp only [rest14,n26,n27,n28]
  rfl
#print axioms last
theorem regroup : numeric=JFm_Q15Absorb.message := by
  change rest00=JFm_Q15Absorb.message
  rw [step00,step01,step02,step03,step04,step05,step06,step07,step08,step09,step10,step11,step12,step13,last]
  simp only [JFm_Q15Absorb.message,JFm_Q15Absorb.head,List.flatten_cons,List.flatten_nil,List.append_nil,List.append_assoc]
#print axioms regroup
theorem native : (flatten (TranscriptStep.absorbParts (encodeState JFm_Q14Source.ratchet) 175#u8 frame)).map Fin.val=numeric := by
  simp only [flatten,TranscriptStep.absorbParts,Array.to_slice,Array.make,List.flatMap_cons,List.flatMap_nil,
    List.map_append,List.append_nil,List.map_map,Function.comp_def,decodeByte,frameBytes,payloadNat,List.map_cons,List.map_nil]
  change ((encodeState JFm_Q14Source.ratchet).val.map (fun x=>x.val)) ++ ([0,175] ++ ([2,128,3,0,0] ++ (n01 ++ n02 ++ n03 ++ n04 ++ n05 ++ n06 ++ n07 ++ n08 ++ n09 ++ n10 ++ n11 ++ n12 ++ n13 ++ n14 ++ n15 ++ n16 ++ n17 ++ n18 ++ n19 ++ n20 ++ n21 ++ n22 ++ n23 ++ n24 ++ n25 ++ n26 ++ n27 ++ n28)))=numeric
  have joined := congrArg (fun lead => lead ++ (n01 ++ n02 ++ n03 ++ n04 ++ n05 ++ n06 ++ n07 ++ n08 ++ n09 ++ n10 ++ n11 ++ n12 ++ n13 ++ n14 ++ n15 ++ n16 ++ n17 ++ n18 ++ n19 ++ n20 ++ n21 ++ n22 ++ n23 ++ n24 ++ n25 ++ n26 ++ n27 ++ n28)) prefixCast
  simpa only [numeric,List.append_assoc] using joined
#print axioms native
end Input
theorem absorbInput : (flatten (TranscriptStep.absorbParts (encodeState JFm_Q14Source.ratchet) 175#u8 frame)).map Fin.val=JFm_Q15Absorb.message := Input.native.trans Input.regroup
#print axioms absorbInput
theorem absorbHash : MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest (TranscriptStep.absorbParts (encodeState JFm_Q14Source.ratchet) 175#u8 frame)=encodeState absorbed := by
  unfold MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest
  rw [absorbInput,JFm_Q15Absorb.checked]
  rfl
#print axioms absorbHash
theorem readInput : (flatten (TranscriptStep.readParts (encodeState absorbed) 1#u8)).map Fin.val=JFm_Q15Read.message := by rfl
#print axioms readInput
theorem readHash : MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest (TranscriptStep.readParts (encodeState absorbed) 1#u8)=encodeState block := by
  unfold MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest
  rw [readInput,JFm_Q15Read.checked]
  rfl
#print axioms readHash
theorem ratchetInput : (flatten (TranscriptStep.readParts (encodeState absorbed) 2#u8)).map Fin.val=JFm_Q15Ratchet.message := by rfl
#print axioms ratchetInput
theorem ratchetHash : MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest (TranscriptStep.readParts (encodeState absorbed) 2#u8)=encodeState ratchet := by
  unfold MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest
  rw [ratchetInput,JFm_Q15Ratchet.checked]
  rfl
#print axioms ratchetHash
theorem source {Hash : Type} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Hash) (hash : Hash) :
    let D0 := AspisR1CurrentCaller.InstalledPreparation.retainedDigest
      (F3V_OracleDictionary.current JFp_SHADigest.digest D)
    r1_wire.SemanticTranscript.sample_block_validated D0
      (⟨encodeState JFm_Q14Source.ratchet,hash,15#u8⟩ : r1_wire.SemanticTranscript Hash)
      15#u8 JFw_NativeRow15.record=ok (.Ok (encodeState block),
        (⟨encodeState ratchet,hash,16#u8⟩ : r1_wire.SemanticTranscript Hash)) := by
  dsimp only
  rw [realFrame,TranscriptStep.step_of_add _ _ 15#u8 175#u8 16#u8 frame rfl (by rfl) (by rfl)]
  change (do let a ← ok (MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest
      (TranscriptStep.absorbParts (encodeState JFm_Q14Source.ratchet) 175#u8 frame))
             let b ← ok (MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest
               (TranscriptStep.readParts a 1#u8))
             let s ← ok (MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest
               (TranscriptStep.readParts a 2#u8))
             ok ((core.result.Result.Ok b : core.result.Result (Array U8 32#usize) r1_wire.Error),(⟨s,hash,16#u8⟩ : r1_wire.SemanticTranscript Hash)))=_
  rw [absorbHash,bind_tc_ok,readHash,bind_tc_ok,ratchetHash,bind_tc_ok]
#print axioms source
theorem word00 : AspisV8R19.SamplerWords.word block ⟨0,by omega⟩=156665283 := by rfl
#print axioms word00
theorem word01 : AspisV8R19.SamplerWords.word block ⟨1,by omega⟩=3043570950 := by rfl
#print axioms word01
theorem word02 : AspisV8R19.SamplerWords.word block ⟨2,by omega⟩=1083557867 := by rfl
#print axioms word02
theorem word03 : AspisV8R19.SamplerWords.word block ⟨3,by omega⟩=2368627987 := by rfl
#print axioms word03
theorem word04 : AspisV8R19.SamplerWords.word block ⟨4,by omega⟩=4173604451 := by rfl
#print axioms word04
theorem word05 : AspisV8R19.SamplerWords.word block ⟨5,by omega⟩=831839808 := by rfl
#print axioms word05
theorem word06 : AspisV8R19.SamplerWords.word block ⟨6,by omega⟩=919693547 := by rfl
#print axioms word06
theorem word07 : AspisV8R19.SamplerWords.word block ⟨7,by omega⟩=4272799259 := by rfl
#print axioms word07
theorem rank : SourceSamplerByteRank.rank (encodeState block)=115194440147853783317142501306617332878256303242782219222485803510414257325507 := by
  unfold SourceSamplerByteRank.rank
  rw [state_roundtrip,←SamplerBlockRank.word_numeral_eq_rank]
  change SamplerPass.numeral (2^32) ([AspisV8R19.SamplerWords.word block ⟨0,by omega⟩,AspisV8R19.SamplerWords.word block ⟨1,by omega⟩,AspisV8R19.SamplerWords.word block ⟨2,by omega⟩,AspisV8R19.SamplerWords.word block ⟨3,by omega⟩,AspisV8R19.SamplerWords.word block ⟨4,by omega⟩,AspisV8R19.SamplerWords.word block ⟨5,by omega⟩,AspisV8R19.SamplerWords.word block ⟨6,by omega⟩,AspisV8R19.SamplerWords.word block ⟨7,by omega⟩].reverse)=115194440147853783317142501306617332878256303242782219222485803510414257325507
  rw [word00,word01,word02,word03,word04,word05,word06,word07]
  rfl
#print axioms rank
theorem digits : SamplerNatModel.qm31Digits 115194440147853783317142501306617332878256303242782219222485803510414257325507=[705343446,1948609717,871005084,203308705] := by rfl
#print axioms digits
theorem semantic {Hash : Type} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Hash) (hash : Hash) :
    let D0 := AspisR1CurrentCaller.InstalledPreparation.retainedDigest
      (F3V_OracleDictionary.current JFp_SHADigest.digest D)
    ∃ q : AspisR1PublicPreparation.aspis_core.field.QM31,
    r1_wire.SemanticTranscript.semantic_validated D0
      (⟨encodeState JFm_Q14Source.ratchet,hash,15#u8⟩ : r1_wire.SemanticTranscript Hash)
      record=ok (.Ok q,(⟨encodeState ratchet,hash,16#u8⟩ : r1_wire.SemanticTranscript Hash)) ∧
    ExtractedQM31SamplerCorrect.coordinates (AspisR1PublicPreparation.SamplerTransport.toOld q)=[705343446,1948609717,871005084,203308705] := by
  obtain ⟨q,call,canon,coords⟩ := AspisR1PublicPreparation.SamplerTransport.sample_total (encodeState block)
  refine ⟨q,?_,by simpa only [rank,digits] using coords⟩
  simp only [r1_wire.SemanticTranscript.semantic_validated,record,r1_wire.ValidatedRecord.impl.row,
    r1_wire.ValidatedRecord.impl.framed,bind_tc_ok]
  rw [if_neg (by change ¬(15:Nat)>24;omega)]
  rw [source,bind_tc_ok]
  change (do let v ← AspisR1PublicPreparation.sampler.qm31_sample (encodeState block)
             ok ((core.result.Result.Ok v : core.result.Result aspis_core.field.QM31 r1_wire.Error),
               (⟨encodeState ratchet,hash,16#u8⟩ : r1_wire.SemanticTranscript Hash)))=_
  rw [call,bind_tc_ok]
#print axioms semantic
end AspisR1.JFm_Q15Source
