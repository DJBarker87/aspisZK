import JFm_BlockSplit
import NDO_JFm_Q23Source
import NDO_JFw_NativeRow24
import RPz7_ExtractedDigest32SamplerTransport
import NDO_JFm_Q24Hashes
set_option autoImplicit false
namespace AspisR1.JFm_Q24Source
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
abbrev frame : Slice U8 := JFw_NativeRow24.record
def absorbed : State := JFp_SHADigest.output JFm_Q24Absorb.result
def block : State := JFp_SHADigest.output JFm_Q24Read.result
def ratchet : State := JFp_SHADigest.output JFm_Q24Ratchet.result
def record : r1_wire.ValidatedRecord := ⟨24#u8,JFw_NativeRow24.record⟩
theorem realFrame : JFw_NativeRow24.record=frame := by
  apply Subtype.ext
  rfl
#print axioms realFrame
namespace Input
attribute [local irreducible] JFx_NativeBytes.proof
def p00 : List U8 := [19#u8,42#u8,227#u8,37#u8,22#u8,134#u8,62#u8,17#u8,71#u8,226#u8,20#u8,16#u8,180#u8,15#u8,119#u8,14#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p01 : List U8 := [95#u8,111#u8,87#u8,51#u8,222#u8,210#u8,144#u8,80#u8,60#u8,24#u8,182#u8,35#u8,254#u8,56#u8,4#u8,67#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p02 : List U8 := [226#u8,204#u8,108#u8,21#u8,168#u8,177#u8,182#u8,1#u8,228#u8,161#u8,99#u8,14#u8,204#u8,6#u8,180#u8,17#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p03 : List U8 := [127#u8,174#u8,2#u8,68#u8,130#u8,15#u8,35#u8,24#u8,77#u8,120#u8,253#u8,99#u8,134#u8,111#u8,113#u8,116#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p04 : List U8 := [214#u8,75#u8,52#u8,14#u8,53#u8,60#u8,130#u8,112#u8,71#u8,68#u8,247#u8,100#u8,47#u8,14#u8,17#u8,125#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p05 : List U8 := [228#u8,111#u8,159#u8,65#u8,152#u8,168#u8,219#u8,10#u8,153#u8,166#u8,250#u8,101#u8,30#u8,213#u8,54#u8,82#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p06 : List U8 := [29#u8,29#u8,173#u8,102#u8,156#u8,168#u8,102#u8,82#u8,137#u8,114#u8,56#u8,23#u8,96#u8,147#u8,131#u8,121#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p07 : List U8 := [0#u8,14#u8,93#u8,113#u8,204#u8,30#u8,164#u8,53#u8,46#u8,186#u8,22#u8,85#u8,237#u8,46#u8,19#u8,15#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p08 : List U8 := [81#u8,174#u8,82#u8,29#u8,31#u8,60#u8,92#u8,95#u8,39#u8,217#u8,159#u8,55#u8,187#u8,59#u8,186#u8,39#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p09 : List U8 := [200#u8,185#u8,104#u8,44#u8,221#u8,168#u8,161#u8,13#u8,113#u8,225#u8,122#u8,44#u8,119#u8,153#u8,136#u8,44#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p10 : List U8 := [220#u8,15#u8,103#u8,33#u8,165#u8,87#u8,74#u8,126#u8,139#u8,175#u8,59#u8,38#u8,34#u8,6#u8,223#u8,16#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p11 : List U8 := [172#u8,40#u8,4#u8,71#u8,240#u8,226#u8,125#u8,103#u8,14#u8,34#u8,153#u8,90#u8,18#u8,34#u8,76#u8,94#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p12 : List U8 := [100#u8,143#u8,212#u8,124#u8,234#u8,7#u8,203#u8,70#u8,205#u8,236#u8,233#u8,69#u8,254#u8,218#u8,124#u8,35#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p13 : List U8 := [116#u8,112#u8,30#u8,71#u8,86#u8,42#u8,152#u8,113#u8,76#u8,14#u8,76#u8,11#u8,242#u8,138#u8,225#u8,52#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p14 : List U8 := [233#u8,177#u8,141#u8,32#u8,10#u8,28#u8,183#u8,79#u8,5#u8,231#u8,243#u8,43#u8,184#u8,191#u8,152#u8,78#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p15 : List U8 := [93#u8,208#u8,65#u8,13#u8,70#u8,131#u8,220#u8,113#u8,208#u8,128#u8,253#u8,17#u8,226#u8,226#u8,25#u8,99#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p16 : List U8 := [101#u8,75#u8,216#u8,126#u8,74#u8,124#u8,169#u8,76#u8,46#u8,136#u8,250#u8,93#u8,219#u8,157#u8,245#u8,105#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p17 : List U8 := [121#u8,81#u8,59#u8,100#u8,21#u8,28#u8,248#u8,59#u8,161#u8,164#u8,187#u8,2#u8,112#u8,72#u8,150#u8,126#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p18 : List U8 := [171#u8,31#u8,72#u8,118#u8,152#u8,228#u8,24#u8,98#u8,146#u8,102#u8,70#u8,69#u8,65#u8,56#u8,161#u8,104#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p19 : List U8 := [142#u8,72#u8,45#u8,38#u8,187#u8,226#u8,201#u8,50#u8,217#u8,58#u8,239#u8,15#u8,155#u8,25#u8,228#u8,54#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p20 : List U8 := [227#u8,244#u8,20#u8,54#u8,103#u8,33#u8,107#u8,125#u8,52#u8,192#u8,9#u8,104#u8,188#u8,152#u8,158#u8,95#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p21 : List U8 := [150#u8,132#u8,150#u8,64#u8,104#u8,45#u8,10#u8,89#u8,224#u8,148#u8,99#u8,16#u8,114#u8,50#u8,128#u8,125#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p22 : List U8 := [13#u8,183#u8,167#u8,14#u8,232#u8,122#u8,254#u8,29#u8,148#u8,54#u8,63#u8,100#u8,77#u8,11#u8,102#u8,36#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p23 : List U8 := [247#u8,150#u8,160#u8,26#u8,122#u8,218#u8,49#u8,19#u8,76#u8,63#u8,120#u8,86#u8,80#u8,28#u8,157#u8,6#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p24 : List U8 := [111#u8,94#u8,225#u8,16#u8,218#u8,75#u8,111#u8,105#u8,152#u8,134#u8,116#u8,52#u8,171#u8,70#u8,86#u8,126#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p25 : List U8 := [112#u8,91#u8,121#u8,52#u8,53#u8,239#u8,29#u8,100#u8,144#u8,231#u8,27#u8,20#u8,169#u8,155#u8,15#u8,8#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p26 : List U8 := [76#u8,101#u8,219#u8,73#u8,38#u8,167#u8,221#u8,91#u8,117#u8,103#u8,238#u8,70#u8,222#u8,253#u8,164#u8,4#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p27 : List U8 := [147#u8,230#u8,83#u8,88#u8,148#u8,124#u8,32#u8,116#u8,75#u8,100#u8,7#u8,109#u8,178#u8,207#u8,144#u8,40#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
theorem blocks_b00 : JFw_Blocks.blocks 2 JFz_Scan57.b00=[p00,p01] := by rfl
#print axioms blocks_b00
theorem blocks_b01 : JFw_Blocks.blocks 2 JFz_Scan57.b01=[p02,p03] := by rfl
#print axioms blocks_b01
theorem blocks_b02 : JFw_Blocks.blocks 2 JFz_Scan57.b02=[p04,p05] := by rfl
#print axioms blocks_b02
theorem blocks_b03 : JFw_Blocks.blocks 2 JFz_Scan57.b03=[p06,p07] := by rfl
#print axioms blocks_b03
theorem blocks_b04 : JFw_Blocks.blocks 2 JFz_Scan57.b04=[p08,p09] := by rfl
#print axioms blocks_b04
theorem blocks_b05 : JFw_Blocks.blocks 2 JFz_Scan57.b05=[p10,p11] := by rfl
#print axioms blocks_b05
theorem blocks_b06 : JFw_Blocks.blocks 2 JFz_Scan57.b06=[p12,p13] := by rfl
#print axioms blocks_b06
theorem blocks_b07 : JFw_Blocks.blocks 2 JFz_Scan57.b07=[p14,p15] := by rfl
#print axioms blocks_b07
theorem blocks_b08 : JFw_Blocks.blocks 2 JFz_Scan57.b08=[p16,p17] := by rfl
#print axioms blocks_b08
theorem blocks_b09 : JFw_Blocks.blocks 2 JFz_Scan57.b09=[p18,p19] := by rfl
#print axioms blocks_b09
theorem blocks_b10 : JFw_Blocks.blocks 2 JFz_Scan57.b10=[p20,p21] := by rfl
#print axioms blocks_b10
theorem blocks_b11 : JFw_Blocks.blocks 2 JFz_Scan57.b11=[p22,p23] := by rfl
#print axioms blocks_b11
theorem blocks_b12 : JFw_Blocks.blocks 2 JFz_Scan57.b12=[p24,p25] := by rfl
#print axioms blocks_b12
theorem blocks_b13 : JFw_Blocks.blocks 2 JFz_Scan57.b13=[p26,p27] := by rfl
#print axioms blocks_b13
theorem blocks_j00 : JFw_Blocks.blocks 4 JFz_Scan57.j00=[p02,p03,p04,p05] := by
  rw [JFz_Scan57.j00,JFm_BlockSplit.append 2 2 _ _ JFz_Scan57.b01_length,blocks_b01,blocks_b02]
  rfl
#print axioms blocks_j00
theorem blocks_j01 : JFw_Blocks.blocks 6 JFz_Scan57.j01=[p00,p01,p02,p03,p04,p05] := by
  rw [JFz_Scan57.j01,JFm_BlockSplit.append 2 4 _ _ JFz_Scan57.b00_length,blocks_b00,blocks_j00]
  rfl
#print axioms blocks_j01
theorem blocks_j02 : JFw_Blocks.blocks 4 JFz_Scan57.j02=[p06,p07,p08,p09] := by
  rw [JFz_Scan57.j02,JFm_BlockSplit.append 2 2 _ _ JFz_Scan57.b03_length,blocks_b03,blocks_b04]
  rfl
#print axioms blocks_j02
theorem blocks_j03 : JFw_Blocks.blocks 4 JFz_Scan57.j03=[p10,p11,p12,p13] := by
  rw [JFz_Scan57.j03,JFm_BlockSplit.append 2 2 _ _ JFz_Scan57.b05_length,blocks_b05,blocks_b06]
  rfl
#print axioms blocks_j03
theorem blocks_j04 : JFw_Blocks.blocks 8 JFz_Scan57.j04=[p06,p07,p08,p09,p10,p11,p12,p13] := by
  rw [JFz_Scan57.j04,JFm_BlockSplit.append 4 4 _ _ JFz_Scan57.j02_length,blocks_j02,blocks_j03]
  rfl
#print axioms blocks_j04
theorem blocks_j05 : JFw_Blocks.blocks 14 JFz_Scan57.j05=[p00,p01,p02,p03,p04,p05,p06,p07,p08,p09,p10,p11,p12,p13] := by
  rw [JFz_Scan57.j05,JFm_BlockSplit.append 6 8 _ _ JFz_Scan57.j01_length,blocks_j01,blocks_j04]
  rfl
#print axioms blocks_j05
theorem blocks_j06 : JFw_Blocks.blocks 4 JFz_Scan57.j06=[p16,p17,p18,p19] := by
  rw [JFz_Scan57.j06,JFm_BlockSplit.append 2 2 _ _ JFz_Scan57.b08_length,blocks_b08,blocks_b09]
  rfl
#print axioms blocks_j06
theorem blocks_j07 : JFw_Blocks.blocks 6 JFz_Scan57.j07=[p14,p15,p16,p17,p18,p19] := by
  rw [JFz_Scan57.j07,JFm_BlockSplit.append 2 4 _ _ JFz_Scan57.b07_length,blocks_b07,blocks_j06]
  rfl
#print axioms blocks_j07
theorem blocks_j08 : JFw_Blocks.blocks 4 JFz_Scan57.j08=[p20,p21,p22,p23] := by
  rw [JFz_Scan57.j08,JFm_BlockSplit.append 2 2 _ _ JFz_Scan57.b10_length,blocks_b10,blocks_b11]
  rfl
#print axioms blocks_j08
theorem blocks_j09 : JFw_Blocks.blocks 4 JFz_Scan57.j09=[p24,p25,p26,p27] := by
  rw [JFz_Scan57.j09,JFm_BlockSplit.append 2 2 _ _ JFz_Scan57.b12_length,blocks_b12,blocks_b13]
  rfl
#print axioms blocks_j09
theorem blocks_j10 : JFw_Blocks.blocks 8 JFz_Scan57.j10=[p20,p21,p22,p23,p24,p25,p26,p27] := by
  rw [JFz_Scan57.j10,JFm_BlockSplit.append 4 4 _ _ JFz_Scan57.j08_length,blocks_j08,blocks_j09]
  rfl
#print axioms blocks_j10
theorem blocks_j11 : JFw_Blocks.blocks 14 JFz_Scan57.j11=[p14,p15,p16,p17,p18,p19,p20,p21,p22,p23,p24,p25,p26,p27] := by
  rw [JFz_Scan57.j11,JFm_BlockSplit.append 6 8 _ _ JFz_Scan57.j07_length,blocks_j07,blocks_j10]
  rfl
#print axioms blocks_j11
theorem blocks_j12 : JFw_Blocks.blocks 28 JFz_Scan57.j12=[p00,p01,p02,p03,p04,p05,p06,p07,p08,p09,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20,p21,p22,p23,p24,p25,p26,p27] := by
  rw [JFz_Scan57.j12,JFm_BlockSplit.append 14 14 _ _ JFz_Scan57.j05_length,blocks_j05,blocks_j11]
  rfl
#print axioms blocks_j12
def sourcePayload : List U8 := [p00,p01,p02,p03,p04,p05,p06,p07,p08,p09,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20,p21,p22,p23,p24,p25,p26,p27].flatten
theorem payloadBytes : JFw_NativeRow24.payload.val=sourcePayload := by
  dsimp only [JFw_NativeRow24.payload,JFw_Frames.expandedPayload,JFw_Frames.window]
  rw [JFz_Scan57.selected]
  unfold JFz_Scan57.data
  rw [blocks_j12]
  rfl
#print axioms payloadBytes
theorem frameBytes : JFw_NativeRow24.record.val=[2#u8,128#u8,3#u8,0#u8,0#u8] ++ sourcePayload := by
  change _::_::_::_::_::JFw_NativeRow24.payload.val=_
  rw [payloadBytes]
  rfl
#print axioms frameBytes
def n00 : List Nat := [3,253,214,116,27,224,68,62,190,150,217,230,127,25,159,104,140,34,16,174,112,161,55,69,178,37,195,201,151,50,83,169,0,184,2,128,3,0,0]
def n01 : List Nat := [19,42,227,37,22,134,62,17,71,226,20,16,180,15,119,14,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast01 : (p00).map (fun x=>x.val)=n01 := by rfl
#print axioms cast01
def n02 : List Nat := [95,111,87,51,222,210,144,80,60,24,182,35,254,56,4,67,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast02 : (p01).map (fun x=>x.val)=n02 := by rfl
#print axioms cast02
def n03 : List Nat := [226,204,108,21,168,177,182,1,228,161,99,14,204,6,180,17,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast03 : (p02).map (fun x=>x.val)=n03 := by rfl
#print axioms cast03
def n04 : List Nat := [127,174,2,68,130,15,35,24,77,120,253,99,134,111,113,116,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast04 : (p03).map (fun x=>x.val)=n04 := by rfl
#print axioms cast04
def n05 : List Nat := [214,75,52,14,53,60,130,112,71,68,247,100,47,14,17,125,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast05 : (p04).map (fun x=>x.val)=n05 := by rfl
#print axioms cast05
def n06 : List Nat := [228,111,159,65,152,168,219,10,153,166,250,101,30,213,54,82,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast06 : (p05).map (fun x=>x.val)=n06 := by rfl
#print axioms cast06
def n07 : List Nat := [29,29,173,102,156,168,102,82,137,114,56,23,96,147,131,121,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast07 : (p06).map (fun x=>x.val)=n07 := by rfl
#print axioms cast07
def n08 : List Nat := [0,14,93,113,204,30,164,53,46,186,22,85,237,46,19,15,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast08 : (p07).map (fun x=>x.val)=n08 := by rfl
#print axioms cast08
def n09 : List Nat := [81,174,82,29,31,60,92,95,39,217,159,55,187,59,186,39,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast09 : (p08).map (fun x=>x.val)=n09 := by rfl
#print axioms cast09
def n10 : List Nat := [200,185,104,44,221,168,161,13,113,225,122,44,119,153,136,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast10 : (p09).map (fun x=>x.val)=n10 := by rfl
#print axioms cast10
def n11 : List Nat := [220,15,103,33,165,87,74,126,139,175,59,38,34,6,223,16,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast11 : (p10).map (fun x=>x.val)=n11 := by rfl
#print axioms cast11
def n12 : List Nat := [172,40,4,71,240,226,125,103,14,34,153,90,18,34,76,94,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast12 : (p11).map (fun x=>x.val)=n12 := by rfl
#print axioms cast12
def n13 : List Nat := [100,143,212,124,234,7,203,70,205,236,233,69,254,218,124,35,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast13 : (p12).map (fun x=>x.val)=n13 := by rfl
#print axioms cast13
def n14 : List Nat := [116,112,30,71,86,42,152,113,76,14,76,11,242,138,225,52,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast14 : (p13).map (fun x=>x.val)=n14 := by rfl
#print axioms cast14
def n15 : List Nat := [233,177,141,32,10,28,183,79,5,231,243,43,184,191,152,78,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast15 : (p14).map (fun x=>x.val)=n15 := by rfl
#print axioms cast15
def n16 : List Nat := [93,208,65,13,70,131,220,113,208,128,253,17,226,226,25,99,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast16 : (p15).map (fun x=>x.val)=n16 := by rfl
#print axioms cast16
def n17 : List Nat := [101,75,216,126,74,124,169,76,46,136,250,93,219,157,245,105,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast17 : (p16).map (fun x=>x.val)=n17 := by rfl
#print axioms cast17
def n18 : List Nat := [121,81,59,100,21,28,248,59,161,164,187,2,112,72,150,126,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast18 : (p17).map (fun x=>x.val)=n18 := by rfl
#print axioms cast18
def n19 : List Nat := [171,31,72,118,152,228,24,98,146,102,70,69,65,56,161,104,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast19 : (p18).map (fun x=>x.val)=n19 := by rfl
#print axioms cast19
def n20 : List Nat := [142,72,45,38,187,226,201,50,217,58,239,15,155,25,228,54,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast20 : (p19).map (fun x=>x.val)=n20 := by rfl
#print axioms cast20
def n21 : List Nat := [227,244,20,54,103,33,107,125,52,192,9,104,188,152,158,95,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast21 : (p20).map (fun x=>x.val)=n21 := by rfl
#print axioms cast21
def n22 : List Nat := [150,132,150,64,104,45,10,89,224,148,99,16,114,50,128,125,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast22 : (p21).map (fun x=>x.val)=n22 := by rfl
#print axioms cast22
def n23 : List Nat := [13,183,167,14,232,122,254,29,148,54,63,100,77,11,102,36,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast23 : (p22).map (fun x=>x.val)=n23 := by rfl
#print axioms cast23
def n24 : List Nat := [247,150,160,26,122,218,49,19,76,63,120,86,80,28,157,6,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast24 : (p23).map (fun x=>x.val)=n24 := by rfl
#print axioms cast24
def n25 : List Nat := [111,94,225,16,218,75,111,105,152,134,116,52,171,70,86,126,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast25 : (p24).map (fun x=>x.val)=n25 := by rfl
#print axioms cast25
def n26 : List Nat := [112,91,121,52,53,239,29,100,144,231,27,20,169,155,15,8,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast26 : (p25).map (fun x=>x.val)=n26 := by rfl
#print axioms cast26
def n27 : List Nat := [76,101,219,73,38,167,221,91,117,103,238,70,222,253,164,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast27 : (p26).map (fun x=>x.val)=n27 := by rfl
#print axioms cast27
def n28 : List Nat := [147,230,83,88,148,124,32,116,75,100,7,109,178,207,144,40,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast28 : (p27).map (fun x=>x.val)=n28 := by rfl
#print axioms cast28
def numeric : List Nat := n00 ++ n01 ++ n02 ++ n03 ++ n04 ++ n05 ++ n06 ++ n07 ++ n08 ++ n09 ++ n10 ++ n11 ++ n12 ++ n13 ++ n14 ++ n15 ++ n16 ++ n17 ++ n18 ++ n19 ++ n20 ++ n21 ++ n22 ++ n23 ++ n24 ++ n25 ++ n26 ++ n27 ++ n28
theorem payloadNat : sourcePayload.map (fun x=>x.val)=n01 ++ n02 ++ n03 ++ n04 ++ n05 ++ n06 ++ n07 ++ n08 ++ n09 ++ n10 ++ n11 ++ n12 ++ n13 ++ n14 ++ n15 ++ n16 ++ n17 ++ n18 ++ n19 ++ n20 ++ n21 ++ n22 ++ n23 ++ n24 ++ n25 ++ n26 ++ n27 ++ n28 := by
  simp only [sourcePayload,List.flatten_cons,List.flatten_nil,List.map_append,List.map_nil,List.append_nil,List.append_assoc,cast01,cast02,cast03,cast04,cast05,cast06,cast07,cast08,cast09,cast10,cast11,cast12,cast13,cast14,cast15,cast16,cast17,cast18,cast19,cast20,cast21,cast22,cast23,cast24,cast25,cast26,cast27,cast28]
#print axioms payloadNat
theorem prefixCast : ((encodeState JFm_Q23Source.ratchet).val.map (fun x=>x.val)) ++ [0,184] ++ [2,128,3,0,0]=n00 := by rfl
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
theorem step00 : rest00=JFm_Q24Absorb.B00.input ++ rest01 := by
  simp only [rest00,rest01,n00,n01]
  rfl
#print axioms step00
theorem step01 : rest01=JFm_Q24Absorb.B01.input ++ rest02 := by
  simp only [rest01,rest02,n01,n02,n03]
  rfl
#print axioms step01
theorem step02 : rest02=JFm_Q24Absorb.B02.input ++ rest03 := by
  simp only [rest02,rest03,n03,n04,n05]
  rfl
#print axioms step02
theorem step03 : rest03=JFm_Q24Absorb.B03.input ++ rest04 := by
  simp only [rest03,rest04,n05,n06,n07]
  rfl
#print axioms step03
theorem step04 : rest04=JFm_Q24Absorb.B04.input ++ rest05 := by
  simp only [rest04,rest05,n07,n08,n09]
  rfl
#print axioms step04
theorem step05 : rest05=JFm_Q24Absorb.B05.input ++ rest06 := by
  simp only [rest05,rest06,n09,n10,n11]
  rfl
#print axioms step05
theorem step06 : rest06=JFm_Q24Absorb.B06.input ++ rest07 := by
  simp only [rest06,rest07,n11,n12,n13]
  rfl
#print axioms step06
theorem step07 : rest07=JFm_Q24Absorb.B07.input ++ rest08 := by
  simp only [rest07,rest08,n13,n14,n15]
  rfl
#print axioms step07
theorem step08 : rest08=JFm_Q24Absorb.B08.input ++ rest09 := by
  simp only [rest08,rest09,n15,n16,n17]
  rfl
#print axioms step08
theorem step09 : rest09=JFm_Q24Absorb.B09.input ++ rest10 := by
  simp only [rest09,rest10,n17,n18,n19]
  rfl
#print axioms step09
theorem step10 : rest10=JFm_Q24Absorb.B10.input ++ rest11 := by
  simp only [rest10,rest11,n19,n20,n21]
  rfl
#print axioms step10
theorem step11 : rest11=JFm_Q24Absorb.B11.input ++ rest12 := by
  simp only [rest11,rest12,n21,n22,n23]
  rfl
#print axioms step11
theorem step12 : rest12=JFm_Q24Absorb.B12.input ++ rest13 := by
  simp only [rest12,rest13,n23,n24,n25]
  rfl
#print axioms step12
theorem step13 : rest13=JFm_Q24Absorb.B13.input ++ rest14 := by
  simp only [rest13,rest14,n25,n26,n27]
  rfl
#print axioms step13
theorem last : rest14=JFm_Q24Absorb.tail := by
  simp only [rest14,n26,n27,n28]
  rfl
#print axioms last
theorem regroup : numeric=JFm_Q24Absorb.message := by
  change rest00=JFm_Q24Absorb.message
  rw [step00,step01,step02,step03,step04,step05,step06,step07,step08,step09,step10,step11,step12,step13,last]
  simp only [JFm_Q24Absorb.message,JFm_Q24Absorb.head,List.flatten_cons,List.flatten_nil,List.append_nil,List.append_assoc]
#print axioms regroup
theorem native : (flatten (TranscriptStep.absorbParts (encodeState JFm_Q23Source.ratchet) 184#u8 frame)).map Fin.val=numeric := by
  simp only [flatten,TranscriptStep.absorbParts,Array.to_slice,Array.make,List.flatMap_cons,List.flatMap_nil,
    List.map_append,List.append_nil,List.map_map,Function.comp_def,decodeByte,frameBytes,payloadNat,List.map_cons,List.map_nil]
  change ((encodeState JFm_Q23Source.ratchet).val.map (fun x=>x.val)) ++ ([0,184] ++ ([2,128,3,0,0] ++ (n01 ++ n02 ++ n03 ++ n04 ++ n05 ++ n06 ++ n07 ++ n08 ++ n09 ++ n10 ++ n11 ++ n12 ++ n13 ++ n14 ++ n15 ++ n16 ++ n17 ++ n18 ++ n19 ++ n20 ++ n21 ++ n22 ++ n23 ++ n24 ++ n25 ++ n26 ++ n27 ++ n28)))=numeric
  have joined := congrArg (fun lead => lead ++ (n01 ++ n02 ++ n03 ++ n04 ++ n05 ++ n06 ++ n07 ++ n08 ++ n09 ++ n10 ++ n11 ++ n12 ++ n13 ++ n14 ++ n15 ++ n16 ++ n17 ++ n18 ++ n19 ++ n20 ++ n21 ++ n22 ++ n23 ++ n24 ++ n25 ++ n26 ++ n27 ++ n28)) prefixCast
  simpa only [numeric,List.append_assoc] using joined
#print axioms native
end Input
theorem absorbInput : (flatten (TranscriptStep.absorbParts (encodeState JFm_Q23Source.ratchet) 184#u8 frame)).map Fin.val=JFm_Q24Absorb.message := Input.native.trans Input.regroup
#print axioms absorbInput
theorem absorbHash : MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest (TranscriptStep.absorbParts (encodeState JFm_Q23Source.ratchet) 184#u8 frame)=encodeState absorbed := by
  unfold MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest
  rw [absorbInput,JFm_Q24Absorb.checked]
  rfl
#print axioms absorbHash
theorem readInput : (flatten (TranscriptStep.readParts (encodeState absorbed) 1#u8)).map Fin.val=JFm_Q24Read.message := by rfl
#print axioms readInput
theorem readHash : MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest (TranscriptStep.readParts (encodeState absorbed) 1#u8)=encodeState block := by
  unfold MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest
  rw [readInput,JFm_Q24Read.checked]
  rfl
#print axioms readHash
theorem ratchetInput : (flatten (TranscriptStep.readParts (encodeState absorbed) 2#u8)).map Fin.val=JFm_Q24Ratchet.message := by rfl
#print axioms ratchetInput
theorem ratchetHash : MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest (TranscriptStep.readParts (encodeState absorbed) 2#u8)=encodeState ratchet := by
  unfold MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest
  rw [ratchetInput,JFm_Q24Ratchet.checked]
  rfl
#print axioms ratchetHash
theorem source {Hash : Type} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Hash) (hash : Hash) :
    let D0 := AspisR1CurrentCaller.InstalledPreparation.retainedDigest
      (F3V_OracleDictionary.current JFp_SHADigest.digest D)
    r1_wire.SemanticTranscript.sample_block_validated D0
      (⟨encodeState JFm_Q23Source.ratchet,hash,24#u8⟩ : r1_wire.SemanticTranscript Hash)
      24#u8 JFw_NativeRow24.record=ok (.Ok (encodeState block),
        (⟨encodeState ratchet,hash,25#u8⟩ : r1_wire.SemanticTranscript Hash)) := by
  dsimp only
  rw [realFrame,TranscriptStep.step_of_add _ _ 24#u8 184#u8 25#u8 frame rfl (by rfl) (by rfl)]
  change (do let a ← ok (MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest
      (TranscriptStep.absorbParts (encodeState JFm_Q23Source.ratchet) 184#u8 frame))
             let b ← ok (MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest
               (TranscriptStep.readParts a 1#u8))
             let s ← ok (MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest
               (TranscriptStep.readParts a 2#u8))
             ok ((core.result.Result.Ok b : core.result.Result (Array U8 32#usize) r1_wire.Error),(⟨s,hash,25#u8⟩ : r1_wire.SemanticTranscript Hash)))=_
  rw [absorbHash,bind_tc_ok,readHash,bind_tc_ok,ratchetHash,bind_tc_ok]
#print axioms source
theorem word00 : AspisV8R19.SamplerWords.word block ⟨0,by omega⟩=2198364885 := by rfl
#print axioms word00
theorem word01 : AspisV8R19.SamplerWords.word block ⟨1,by omega⟩=561361098 := by rfl
#print axioms word01
theorem word02 : AspisV8R19.SamplerWords.word block ⟨2,by omega⟩=2539328077 := by rfl
#print axioms word02
theorem word03 : AspisV8R19.SamplerWords.word block ⟨3,by omega⟩=2122204957 := by rfl
#print axioms word03
theorem word04 : AspisV8R19.SamplerWords.word block ⟨4,by omega⟩=3144614666 := by rfl
#print axioms word04
theorem word05 : AspisV8R19.SamplerWords.word block ⟨5,by omega⟩=4055890264 := by rfl
#print axioms word05
theorem word06 : AspisV8R19.SamplerWords.word block ⟨6,by omega⟩=4201789723 := by rfl
#print axioms word06
theorem word07 : AspisV8R19.SamplerWords.word block ⟨7,by omega⟩=61629898 := by rfl
#print axioms word07
theorem rank : SourceSamplerByteRank.rank (encodeState block)=1661538789556995449080980011085016034480427377661052819194403701570272781013 := by
  unfold SourceSamplerByteRank.rank
  rw [state_roundtrip,←SamplerBlockRank.word_numeral_eq_rank]
  change SamplerPass.numeral (2^32) ([AspisV8R19.SamplerWords.word block ⟨0,by omega⟩,AspisV8R19.SamplerWords.word block ⟨1,by omega⟩,AspisV8R19.SamplerWords.word block ⟨2,by omega⟩,AspisV8R19.SamplerWords.word block ⟨3,by omega⟩,AspisV8R19.SamplerWords.word block ⟨4,by omega⟩,AspisV8R19.SamplerWords.word block ⟨5,by omega⟩,AspisV8R19.SamplerWords.word block ⟨6,by omega⟩,AspisV8R19.SamplerWords.word block ⟨7,by omega⟩].reverse)=1661538789556995449080980011085016034480427377661052819194403701570272781013
  rw [word00,word01,word02,word03,word04,word05,word06,word07]
  rfl
#print axioms rank
theorem digits : SamplerNatModel.qm31Digits 1661538789556995449080980011085016034480427377661052819194403701570272781013=[2030227143,1410410828,1902035786,62756635] := by rfl
#print axioms digits
theorem semantic {Hash : Type} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Hash) (hash : Hash) :
    let D0 := AspisR1CurrentCaller.InstalledPreparation.retainedDigest
      (F3V_OracleDictionary.current JFp_SHADigest.digest D)
    ∃ q : AspisR1PublicPreparation.aspis_core.field.QM31,
    r1_wire.SemanticTranscript.semantic_validated D0
      (⟨encodeState JFm_Q23Source.ratchet,hash,24#u8⟩ : r1_wire.SemanticTranscript Hash)
      record=ok (.Ok q,(⟨encodeState ratchet,hash,25#u8⟩ : r1_wire.SemanticTranscript Hash)) ∧
    ExtractedQM31SamplerCorrect.coordinates (AspisR1PublicPreparation.SamplerTransport.toOld q)=[2030227143,1410410828,1902035786,62756635] := by
  obtain ⟨q,call,canon,coords⟩ := AspisR1PublicPreparation.SamplerTransport.sample_total (encodeState block)
  refine ⟨q,?_,by simpa only [rank,digits] using coords⟩
  simp only [r1_wire.SemanticTranscript.semantic_validated,record,r1_wire.ValidatedRecord.impl.row,
    r1_wire.ValidatedRecord.impl.framed,bind_tc_ok]
  rw [if_neg (by change ¬(24:Nat)>24;omega)]
  rw [source,bind_tc_ok]
  change (do let v ← AspisR1PublicPreparation.sampler.qm31_sample (encodeState block)
             ok ((core.result.Result.Ok v : core.result.Result aspis_core.field.QM31 r1_wire.Error),
               (⟨encodeState ratchet,hash,25#u8⟩ : r1_wire.SemanticTranscript Hash)))=_
  rw [call,bind_tc_ok]
#print axioms semantic
end AspisR1.JFm_Q24Source
