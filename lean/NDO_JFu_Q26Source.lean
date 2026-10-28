import JFm_BlockSplit
import NDO_JFu_Q25Source
import NDO_JFw_NativeRow26
import RPz7_ExtractedDigest32SamplerTransport
import NDO_JFu_Q26Reads
set_option autoImplicit false
namespace AspisR1.JFu_Q26Source
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
abbrev frame : Slice U8 := JFw_NativeRow26.record
def absorbed : State := JFp_SHADigest.output JFu_Q26Absorb.result
def block : State := JFp_SHADigest.output JFu_Q26Read.result
def ratchet : State := JFp_SHADigest.output JFu_Q26Ratchet.result
def record : r1_wire.ValidatedRecord := ⟨26#u8,JFw_NativeRow26.record⟩
theorem realFrame : JFw_NativeRow26.record=frame := by
  apply Subtype.ext
  rfl
#print axioms realFrame
namespace Input
attribute [local irreducible] JFx_NativeBytes.proof
def p00 : List U8 := [131#u8,211#u8,253#u8,58#u8,3#u8,204#u8,2#u8,71#u8,226#u8,38#u8,90#u8,29#u8,226#u8,132#u8,203#u8,25#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p01 : List U8 := [170#u8,170#u8,175#u8,125#u8,58#u8,8#u8,72#u8,36#u8,11#u8,203#u8,72#u8,19#u8,213#u8,115#u8,71#u8,120#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p02 : List U8 := [92#u8,225#u8,10#u8,81#u8,218#u8,1#u8,95#u8,0#u8,248#u8,200#u8,240#u8,46#u8,5#u8,48#u8,230#u8,40#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p03 : List U8 := [40#u8,171#u8,211#u8,20#u8,197#u8,210#u8,201#u8,83#u8,78#u8,89#u8,250#u8,127#u8,202#u8,169#u8,245#u8,85#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p04 : List U8 := [15#u8,126#u8,33#u8,76#u8,85#u8,208#u8,214#u8,68#u8,155#u8,15#u8,48#u8,63#u8,247#u8,11#u8,203#u8,118#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p05 : List U8 := [158#u8,213#u8,193#u8,32#u8,18#u8,210#u8,221#u8,19#u8,224#u8,225#u8,53#u8,16#u8,79#u8,40#u8,235#u8,79#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p06 : List U8 := [223#u8,249#u8,248#u8,92#u8,210#u8,229#u8,185#u8,28#u8,77#u8,224#u8,10#u8,39#u8,196#u8,120#u8,113#u8,22#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p07 : List U8 := [36#u8,12#u8,98#u8,52#u8,209#u8,213#u8,123#u8,68#u8,248#u8,185#u8,8#u8,64#u8,185#u8,39#u8,244#u8,27#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p08 : List U8 := [30#u8,150#u8,43#u8,111#u8,239#u8,72#u8,196#u8,12#u8,74#u8,207#u8,38#u8,62#u8,25#u8,175#u8,110#u8,34#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p09 : List U8 := [5#u8,35#u8,78#u8,88#u8,9#u8,202#u8,31#u8,127#u8,134#u8,154#u8,13#u8,28#u8,243#u8,210#u8,241#u8,116#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p10 : List U8 := [48#u8,124#u8,105#u8,72#u8,191#u8,241#u8,38#u8,27#u8,228#u8,122#u8,13#u8,78#u8,126#u8,49#u8,250#u8,59#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p11 : List U8 := [67#u8,141#u8,217#u8,76#u8,38#u8,136#u8,132#u8,18#u8,55#u8,58#u8,228#u8,63#u8,230#u8,70#u8,199#u8,108#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p12 : List U8 := [195#u8,48#u8,79#u8,41#u8,11#u8,56#u8,116#u8,24#u8,76#u8,47#u8,107#u8,72#u8,142#u8,149#u8,6#u8,121#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p13 : List U8 := [179#u8,228#u8,57#u8,54#u8,131#u8,130#u8,40#u8,118#u8,33#u8,252#u8,79#u8,11#u8,212#u8,153#u8,152#u8,15#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p14 : List U8 := [160#u8,1#u8,242#u8,4#u8,106#u8,52#u8,176#u8,106#u8,56#u8,126#u8,19#u8,62#u8,87#u8,211#u8,240#u8,59#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p15 : List U8 := [34#u8,104#u8,97#u8,72#u8,75#u8,135#u8,131#u8,15#u8,21#u8,157#u8,31#u8,93#u8,47#u8,160#u8,207#u8,65#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p16 : List U8 := [26#u8,9#u8,28#u8,57#u8,98#u8,155#u8,203#u8,126#u8,208#u8,128#u8,23#u8,31#u8,220#u8,65#u8,144#u8,24#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p17 : List U8 := [208#u8,135#u8,145#u8,126#u8,29#u8,43#u8,148#u8,63#u8,160#u8,132#u8,220#u8,83#u8,82#u8,203#u8,87#u8,105#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p18 : List U8 := [61#u8,23#u8,156#u8,4#u8,211#u8,35#u8,222#u8,117#u8,182#u8,69#u8,140#u8,7#u8,162#u8,200#u8,165#u8,105#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p19 : List U8 := [235#u8,113#u8,240#u8,5#u8,57#u8,119#u8,245#u8,122#u8,194#u8,187#u8,100#u8,75#u8,162#u8,33#u8,211#u8,8#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p20 : List U8 := [143#u8,29#u8,71#u8,31#u8,156#u8,249#u8,48#u8,73#u8,252#u8,84#u8,85#u8,104#u8,136#u8,5#u8,85#u8,87#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p21 : List U8 := [99#u8,223#u8,121#u8,0#u8,171#u8,91#u8,189#u8,93#u8,207#u8,51#u8,182#u8,124#u8,220#u8,21#u8,163#u8,112#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p22 : List U8 := [50#u8,76#u8,184#u8,114#u8,70#u8,100#u8,80#u8,69#u8,154#u8,224#u8,31#u8,91#u8,97#u8,84#u8,233#u8,87#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p23 : List U8 := [129#u8,173#u8,173#u8,38#u8,45#u8,251#u8,178#u8,117#u8,54#u8,151#u8,157#u8,105#u8,14#u8,251#u8,2#u8,2#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p24 : List U8 := [103#u8,123#u8,145#u8,36#u8,5#u8,72#u8,101#u8,122#u8,59#u8,28#u8,17#u8,63#u8,80#u8,79#u8,71#u8,57#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p25 : List U8 := [153#u8,224#u8,245#u8,47#u8,152#u8,65#u8,45#u8,90#u8,25#u8,66#u8,194#u8,67#u8,245#u8,183#u8,24#u8,22#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p26 : List U8 := [110#u8,96#u8,214#u8,78#u8,228#u8,174#u8,129#u8,21#u8,124#u8,153#u8,68#u8,111#u8,119#u8,101#u8,196#u8,50#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p27 : List U8 := [227#u8,192#u8,61#u8,33#u8,60#u8,130#u8,195#u8,20#u8,128#u8,242#u8,20#u8,122#u8,109#u8,77#u8,139#u8,67#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p28 : List U8 := [20#u8,219#u8,131#u8,59#u8,7#u8,248#u8,46#u8,12#u8,21#u8,184#u8,131#u8,5#u8,120#u8,4#u8,47#u8,103#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
theorem blocks_b00 : JFw_Blocks.blocks 2 JFz_Scan59.b00=[p00,p01] := by rfl
#print axioms blocks_b00
theorem blocks_b01 : JFw_Blocks.blocks 2 JFz_Scan59.b01=[p02,p03] := by rfl
#print axioms blocks_b01
theorem blocks_b02 : JFw_Blocks.blocks 2 JFz_Scan59.b02=[p04,p05] := by rfl
#print axioms blocks_b02
theorem blocks_b03 : JFw_Blocks.blocks 2 JFz_Scan59.b03=[p06,p07] := by rfl
#print axioms blocks_b03
theorem blocks_b04 : JFw_Blocks.blocks 2 JFz_Scan59.b04=[p08,p09] := by rfl
#print axioms blocks_b04
theorem blocks_b05 : JFw_Blocks.blocks 2 JFz_Scan59.b05=[p10,p11] := by rfl
#print axioms blocks_b05
theorem blocks_b06 : JFw_Blocks.blocks 2 JFz_Scan59.b06=[p12,p13] := by rfl
#print axioms blocks_b06
theorem blocks_b07 : JFw_Blocks.blocks 2 JFz_Scan59.b07=[p14,p15] := by rfl
#print axioms blocks_b07
theorem blocks_b08 : JFw_Blocks.blocks 2 JFz_Scan59.b08=[p16,p17] := by rfl
#print axioms blocks_b08
theorem blocks_b09 : JFw_Blocks.blocks 2 JFz_Scan59.b09=[p18,p19] := by rfl
#print axioms blocks_b09
theorem blocks_b10 : JFw_Blocks.blocks 2 JFz_Scan59.b10=[p20,p21] := by rfl
#print axioms blocks_b10
theorem blocks_b11 : JFw_Blocks.blocks 2 JFz_Scan59.b11=[p22,p23] := by rfl
#print axioms blocks_b11
theorem blocks_b12 : JFw_Blocks.blocks 2 JFz_Scan59.b12=[p24,p25] := by rfl
#print axioms blocks_b12
theorem blocks_b13 : JFw_Blocks.blocks 2 JFz_Scan59.b13=[p26,p27] := by rfl
#print axioms blocks_b13
theorem blocks_b14 : JFw_Blocks.blocks 1 JFz_Scan59.b14=[p28] := by rfl
#print axioms blocks_b14
theorem blocks_j00 : JFw_Blocks.blocks 4 JFz_Scan59.j00=[p02,p03,p04,p05] := by
  rw [JFz_Scan59.j00,JFm_BlockSplit.append 2 2 _ _ JFz_Scan59.b01_length,blocks_b01,blocks_b02]
  rfl
#print axioms blocks_j00
theorem blocks_j01 : JFw_Blocks.blocks 6 JFz_Scan59.j01=[p00,p01,p02,p03,p04,p05] := by
  rw [JFz_Scan59.j01,JFm_BlockSplit.append 2 4 _ _ JFz_Scan59.b00_length,blocks_b00,blocks_j00]
  rfl
#print axioms blocks_j01
theorem blocks_j02 : JFw_Blocks.blocks 4 JFz_Scan59.j02=[p06,p07,p08,p09] := by
  rw [JFz_Scan59.j02,JFm_BlockSplit.append 2 2 _ _ JFz_Scan59.b03_length,blocks_b03,blocks_b04]
  rfl
#print axioms blocks_j02
theorem blocks_j03 : JFw_Blocks.blocks 4 JFz_Scan59.j03=[p10,p11,p12,p13] := by
  rw [JFz_Scan59.j03,JFm_BlockSplit.append 2 2 _ _ JFz_Scan59.b05_length,blocks_b05,blocks_b06]
  rfl
#print axioms blocks_j03
theorem blocks_j04 : JFw_Blocks.blocks 8 JFz_Scan59.j04=[p06,p07,p08,p09,p10,p11,p12,p13] := by
  rw [JFz_Scan59.j04,JFm_BlockSplit.append 4 4 _ _ JFz_Scan59.j02_length,blocks_j02,blocks_j03]
  rfl
#print axioms blocks_j04
theorem blocks_j05 : JFw_Blocks.blocks 14 JFz_Scan59.j05=[p00,p01,p02,p03,p04,p05,p06,p07,p08,p09,p10,p11,p12,p13] := by
  rw [JFz_Scan59.j05,JFm_BlockSplit.append 6 8 _ _ JFz_Scan59.j01_length,blocks_j01,blocks_j04]
  rfl
#print axioms blocks_j05
theorem blocks_j06 : JFw_Blocks.blocks 4 JFz_Scan59.j06=[p14,p15,p16,p17] := by
  rw [JFz_Scan59.j06,JFm_BlockSplit.append 2 2 _ _ JFz_Scan59.b07_length,blocks_b07,blocks_b08]
  rfl
#print axioms blocks_j06
theorem blocks_j07 : JFw_Blocks.blocks 4 JFz_Scan59.j07=[p18,p19,p20,p21] := by
  rw [JFz_Scan59.j07,JFm_BlockSplit.append 2 2 _ _ JFz_Scan59.b09_length,blocks_b09,blocks_b10]
  rfl
#print axioms blocks_j07
theorem blocks_j08 : JFw_Blocks.blocks 8 JFz_Scan59.j08=[p14,p15,p16,p17,p18,p19,p20,p21] := by
  rw [JFz_Scan59.j08,JFm_BlockSplit.append 4 4 _ _ JFz_Scan59.j06_length,blocks_j06,blocks_j07]
  rfl
#print axioms blocks_j08
theorem blocks_j09 : JFw_Blocks.blocks 4 JFz_Scan59.j09=[p22,p23,p24,p25] := by
  rw [JFz_Scan59.j09,JFm_BlockSplit.append 2 2 _ _ JFz_Scan59.b11_length,blocks_b11,blocks_b12]
  rfl
#print axioms blocks_j09
theorem blocks_j10 : JFw_Blocks.blocks 3 JFz_Scan59.j10=[p26,p27,p28] := by
  rw [JFz_Scan59.j10,JFm_BlockSplit.append 2 1 _ _ JFz_Scan59.b13_length,blocks_b13,blocks_b14]
  rfl
#print axioms blocks_j10
theorem blocks_j11 : JFw_Blocks.blocks 7 JFz_Scan59.j11=[p22,p23,p24,p25,p26,p27,p28] := by
  rw [JFz_Scan59.j11,JFm_BlockSplit.append 4 3 _ _ JFz_Scan59.j09_length,blocks_j09,blocks_j10]
  rfl
#print axioms blocks_j11
theorem blocks_j12 : JFw_Blocks.blocks 15 JFz_Scan59.j12=[p14,p15,p16,p17,p18,p19,p20,p21,p22,p23,p24,p25,p26,p27,p28] := by
  rw [JFz_Scan59.j12,JFm_BlockSplit.append 8 7 _ _ JFz_Scan59.j08_length,blocks_j08,blocks_j11]
  rfl
#print axioms blocks_j12
theorem blocks_j13 : JFw_Blocks.blocks 29 JFz_Scan59.j13=[p00,p01,p02,p03,p04,p05,p06,p07,p08,p09,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20,p21,p22,p23,p24,p25,p26,p27,p28] := by
  rw [JFz_Scan59.j13,JFm_BlockSplit.append 14 15 _ _ JFz_Scan59.j05_length,blocks_j05,blocks_j12]
  rfl
#print axioms blocks_j13
def sourcePayload : List U8 := [p00,p01,p02,p03,p04,p05,p06,p07,p08,p09,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20,p21,p22,p23,p24,p25,p26,p27,p28].flatten
theorem payloadBytes : JFw_NativeRow26.payload.val=sourcePayload := by
  dsimp only [JFw_NativeRow26.payload,JFw_Frames.expandedPayload,JFw_Frames.window]
  rw [JFz_Scan59.selected]
  unfold JFz_Scan59.data
  rw [blocks_j13]
  rfl
#print axioms payloadBytes
theorem frameBytes : JFw_NativeRow26.record.val=[5#u8,160#u8,3#u8,0#u8,0#u8] ++ sourcePayload := by
  change _::_::_::_::_::JFw_NativeRow26.payload.val=_
  rw [payloadBytes]
  rfl
#print axioms frameBytes
def n00 : List Nat := [53,135,184,254,190,191,56,224,102,157,110,177,100,244,208,72,64,175,160,164,120,123,45,80,129,178,141,102,105,9,49,225,0,186,5,160,3,0,0]
def n01 : List Nat := [131,211,253,58,3,204,2,71,226,38,90,29,226,132,203,25,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast01 : (p00).map (fun x=>x.val)=n01 := by rfl
#print axioms cast01
def n02 : List Nat := [170,170,175,125,58,8,72,36,11,203,72,19,213,115,71,120,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast02 : (p01).map (fun x=>x.val)=n02 := by rfl
#print axioms cast02
def n03 : List Nat := [92,225,10,81,218,1,95,0,248,200,240,46,5,48,230,40,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast03 : (p02).map (fun x=>x.val)=n03 := by rfl
#print axioms cast03
def n04 : List Nat := [40,171,211,20,197,210,201,83,78,89,250,127,202,169,245,85,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast04 : (p03).map (fun x=>x.val)=n04 := by rfl
#print axioms cast04
def n05 : List Nat := [15,126,33,76,85,208,214,68,155,15,48,63,247,11,203,118,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast05 : (p04).map (fun x=>x.val)=n05 := by rfl
#print axioms cast05
def n06 : List Nat := [158,213,193,32,18,210,221,19,224,225,53,16,79,40,235,79,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast06 : (p05).map (fun x=>x.val)=n06 := by rfl
#print axioms cast06
def n07 : List Nat := [223,249,248,92,210,229,185,28,77,224,10,39,196,120,113,22,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast07 : (p06).map (fun x=>x.val)=n07 := by rfl
#print axioms cast07
def n08 : List Nat := [36,12,98,52,209,213,123,68,248,185,8,64,185,39,244,27,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast08 : (p07).map (fun x=>x.val)=n08 := by rfl
#print axioms cast08
def n09 : List Nat := [30,150,43,111,239,72,196,12,74,207,38,62,25,175,110,34,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast09 : (p08).map (fun x=>x.val)=n09 := by rfl
#print axioms cast09
def n10 : List Nat := [5,35,78,88,9,202,31,127,134,154,13,28,243,210,241,116,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast10 : (p09).map (fun x=>x.val)=n10 := by rfl
#print axioms cast10
def n11 : List Nat := [48,124,105,72,191,241,38,27,228,122,13,78,126,49,250,59,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast11 : (p10).map (fun x=>x.val)=n11 := by rfl
#print axioms cast11
def n12 : List Nat := [67,141,217,76,38,136,132,18,55,58,228,63,230,70,199,108,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast12 : (p11).map (fun x=>x.val)=n12 := by rfl
#print axioms cast12
def n13 : List Nat := [195,48,79,41,11,56,116,24,76,47,107,72,142,149,6,121,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast13 : (p12).map (fun x=>x.val)=n13 := by rfl
#print axioms cast13
def n14 : List Nat := [179,228,57,54,131,130,40,118,33,252,79,11,212,153,152,15,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast14 : (p13).map (fun x=>x.val)=n14 := by rfl
#print axioms cast14
def n15 : List Nat := [160,1,242,4,106,52,176,106,56,126,19,62,87,211,240,59,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast15 : (p14).map (fun x=>x.val)=n15 := by rfl
#print axioms cast15
def n16 : List Nat := [34,104,97,72,75,135,131,15,21,157,31,93,47,160,207,65,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast16 : (p15).map (fun x=>x.val)=n16 := by rfl
#print axioms cast16
def n17 : List Nat := [26,9,28,57,98,155,203,126,208,128,23,31,220,65,144,24,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast17 : (p16).map (fun x=>x.val)=n17 := by rfl
#print axioms cast17
def n18 : List Nat := [208,135,145,126,29,43,148,63,160,132,220,83,82,203,87,105,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast18 : (p17).map (fun x=>x.val)=n18 := by rfl
#print axioms cast18
def n19 : List Nat := [61,23,156,4,211,35,222,117,182,69,140,7,162,200,165,105,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast19 : (p18).map (fun x=>x.val)=n19 := by rfl
#print axioms cast19
def n20 : List Nat := [235,113,240,5,57,119,245,122,194,187,100,75,162,33,211,8,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast20 : (p19).map (fun x=>x.val)=n20 := by rfl
#print axioms cast20
def n21 : List Nat := [143,29,71,31,156,249,48,73,252,84,85,104,136,5,85,87,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast21 : (p20).map (fun x=>x.val)=n21 := by rfl
#print axioms cast21
def n22 : List Nat := [99,223,121,0,171,91,189,93,207,51,182,124,220,21,163,112,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast22 : (p21).map (fun x=>x.val)=n22 := by rfl
#print axioms cast22
def n23 : List Nat := [50,76,184,114,70,100,80,69,154,224,31,91,97,84,233,87,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast23 : (p22).map (fun x=>x.val)=n23 := by rfl
#print axioms cast23
def n24 : List Nat := [129,173,173,38,45,251,178,117,54,151,157,105,14,251,2,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast24 : (p23).map (fun x=>x.val)=n24 := by rfl
#print axioms cast24
def n25 : List Nat := [103,123,145,36,5,72,101,122,59,28,17,63,80,79,71,57,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast25 : (p24).map (fun x=>x.val)=n25 := by rfl
#print axioms cast25
def n26 : List Nat := [153,224,245,47,152,65,45,90,25,66,194,67,245,183,24,22,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast26 : (p25).map (fun x=>x.val)=n26 := by rfl
#print axioms cast26
def n27 : List Nat := [110,96,214,78,228,174,129,21,124,153,68,111,119,101,196,50,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast27 : (p26).map (fun x=>x.val)=n27 := by rfl
#print axioms cast27
def n28 : List Nat := [227,192,61,33,60,130,195,20,128,242,20,122,109,77,139,67,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast28 : (p27).map (fun x=>x.val)=n28 := by rfl
#print axioms cast28
def n29 : List Nat := [20,219,131,59,7,248,46,12,21,184,131,5,120,4,47,103,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast29 : (p28).map (fun x=>x.val)=n29 := by rfl
#print axioms cast29
def numeric : List Nat := n00 ++ n01 ++ n02 ++ n03 ++ n04 ++ n05 ++ n06 ++ n07 ++ n08 ++ n09 ++ n10 ++ n11 ++ n12 ++ n13 ++ n14 ++ n15 ++ n16 ++ n17 ++ n18 ++ n19 ++ n20 ++ n21 ++ n22 ++ n23 ++ n24 ++ n25 ++ n26 ++ n27 ++ n28 ++ n29
theorem payloadNat : sourcePayload.map (fun x=>x.val)=n01 ++ n02 ++ n03 ++ n04 ++ n05 ++ n06 ++ n07 ++ n08 ++ n09 ++ n10 ++ n11 ++ n12 ++ n13 ++ n14 ++ n15 ++ n16 ++ n17 ++ n18 ++ n19 ++ n20 ++ n21 ++ n22 ++ n23 ++ n24 ++ n25 ++ n26 ++ n27 ++ n28 ++ n29 := by
  simp only [sourcePayload,List.flatten_cons,List.flatten_nil,List.map_append,List.map_nil,List.append_nil,List.append_assoc,cast01,cast02,cast03,cast04,cast05,cast06,cast07,cast08,cast09,cast10,cast11,cast12,cast13,cast14,cast15,cast16,cast17,cast18,cast19,cast20,cast21,cast22,cast23,cast24,cast25,cast26,cast27,cast28,cast29]
#print axioms payloadNat
theorem prefixCast : ((encodeState JFu_Q25Source.ratchet).val.map (fun x=>x.val)) ++ [0,186] ++ [5,160,3,0,0]=n00 := by rfl
#print axioms prefixCast
def rest00 : List Nat := n00 ++ n01 ++ n02 ++ n03 ++ n04 ++ n05 ++ n06 ++ n07 ++ n08 ++ n09 ++ n10 ++ n11 ++ n12 ++ n13 ++ n14 ++ n15 ++ n16 ++ n17 ++ n18 ++ n19 ++ n20 ++ n21 ++ n22 ++ n23 ++ n24 ++ n25 ++ n26 ++ n27 ++ n28 ++ n29
def rest01 : List Nat := (n01.drop 25) ++ n02 ++ n03 ++ n04 ++ n05 ++ n06 ++ n07 ++ n08 ++ n09 ++ n10 ++ n11 ++ n12 ++ n13 ++ n14 ++ n15 ++ n16 ++ n17 ++ n18 ++ n19 ++ n20 ++ n21 ++ n22 ++ n23 ++ n24 ++ n25 ++ n26 ++ n27 ++ n28 ++ n29
def rest02 : List Nat := (n03.drop 25) ++ n04 ++ n05 ++ n06 ++ n07 ++ n08 ++ n09 ++ n10 ++ n11 ++ n12 ++ n13 ++ n14 ++ n15 ++ n16 ++ n17 ++ n18 ++ n19 ++ n20 ++ n21 ++ n22 ++ n23 ++ n24 ++ n25 ++ n26 ++ n27 ++ n28 ++ n29
def rest03 : List Nat := (n05.drop 25) ++ n06 ++ n07 ++ n08 ++ n09 ++ n10 ++ n11 ++ n12 ++ n13 ++ n14 ++ n15 ++ n16 ++ n17 ++ n18 ++ n19 ++ n20 ++ n21 ++ n22 ++ n23 ++ n24 ++ n25 ++ n26 ++ n27 ++ n28 ++ n29
def rest04 : List Nat := (n07.drop 25) ++ n08 ++ n09 ++ n10 ++ n11 ++ n12 ++ n13 ++ n14 ++ n15 ++ n16 ++ n17 ++ n18 ++ n19 ++ n20 ++ n21 ++ n22 ++ n23 ++ n24 ++ n25 ++ n26 ++ n27 ++ n28 ++ n29
def rest05 : List Nat := (n09.drop 25) ++ n10 ++ n11 ++ n12 ++ n13 ++ n14 ++ n15 ++ n16 ++ n17 ++ n18 ++ n19 ++ n20 ++ n21 ++ n22 ++ n23 ++ n24 ++ n25 ++ n26 ++ n27 ++ n28 ++ n29
def rest06 : List Nat := (n11.drop 25) ++ n12 ++ n13 ++ n14 ++ n15 ++ n16 ++ n17 ++ n18 ++ n19 ++ n20 ++ n21 ++ n22 ++ n23 ++ n24 ++ n25 ++ n26 ++ n27 ++ n28 ++ n29
def rest07 : List Nat := (n13.drop 25) ++ n14 ++ n15 ++ n16 ++ n17 ++ n18 ++ n19 ++ n20 ++ n21 ++ n22 ++ n23 ++ n24 ++ n25 ++ n26 ++ n27 ++ n28 ++ n29
def rest08 : List Nat := (n15.drop 25) ++ n16 ++ n17 ++ n18 ++ n19 ++ n20 ++ n21 ++ n22 ++ n23 ++ n24 ++ n25 ++ n26 ++ n27 ++ n28 ++ n29
def rest09 : List Nat := (n17.drop 25) ++ n18 ++ n19 ++ n20 ++ n21 ++ n22 ++ n23 ++ n24 ++ n25 ++ n26 ++ n27 ++ n28 ++ n29
def rest10 : List Nat := (n19.drop 25) ++ n20 ++ n21 ++ n22 ++ n23 ++ n24 ++ n25 ++ n26 ++ n27 ++ n28 ++ n29
def rest11 : List Nat := (n21.drop 25) ++ n22 ++ n23 ++ n24 ++ n25 ++ n26 ++ n27 ++ n28 ++ n29
def rest12 : List Nat := (n23.drop 25) ++ n24 ++ n25 ++ n26 ++ n27 ++ n28 ++ n29
def rest13 : List Nat := (n25.drop 25) ++ n26 ++ n27 ++ n28 ++ n29
def rest14 : List Nat := (n27.drop 25) ++ n28 ++ n29
def rest15 : List Nat := (n29.drop 25)
theorem step00 : rest00=JFu_Q26Absorb.B00.input ++ rest01 := by
  simp only [rest00,rest01,n00,n01]
  rfl
#print axioms step00
theorem step01 : rest01=JFu_Q26Absorb.B01.input ++ rest02 := by
  simp only [rest01,rest02,n01,n02,n03]
  rfl
#print axioms step01
theorem step02 : rest02=JFu_Q26Absorb.B02.input ++ rest03 := by
  simp only [rest02,rest03,n03,n04,n05]
  rfl
#print axioms step02
theorem step03 : rest03=JFu_Q26Absorb.B03.input ++ rest04 := by
  simp only [rest03,rest04,n05,n06,n07]
  rfl
#print axioms step03
theorem step04 : rest04=JFu_Q26Absorb.B04.input ++ rest05 := by
  simp only [rest04,rest05,n07,n08,n09]
  rfl
#print axioms step04
theorem step05 : rest05=JFu_Q26Absorb.B05.input ++ rest06 := by
  simp only [rest05,rest06,n09,n10,n11]
  rfl
#print axioms step05
theorem step06 : rest06=JFu_Q26Absorb.B06.input ++ rest07 := by
  simp only [rest06,rest07,n11,n12,n13]
  rfl
#print axioms step06
theorem step07 : rest07=JFu_Q26Absorb.B07.input ++ rest08 := by
  simp only [rest07,rest08,n13,n14,n15]
  rfl
#print axioms step07
theorem step08 : rest08=JFu_Q26Absorb.B08.input ++ rest09 := by
  simp only [rest08,rest09,n15,n16,n17]
  rfl
#print axioms step08
theorem step09 : rest09=JFu_Q26Absorb.B09.input ++ rest10 := by
  simp only [rest09,rest10,n17,n18,n19]
  rfl
#print axioms step09
theorem step10 : rest10=JFu_Q26Absorb.B10.input ++ rest11 := by
  simp only [rest10,rest11,n19,n20,n21]
  rfl
#print axioms step10
theorem step11 : rest11=JFu_Q26Absorb.B11.input ++ rest12 := by
  simp only [rest11,rest12,n21,n22,n23]
  rfl
#print axioms step11
theorem step12 : rest12=JFu_Q26Absorb.B12.input ++ rest13 := by
  simp only [rest12,rest13,n23,n24,n25]
  rfl
#print axioms step12
theorem step13 : rest13=JFu_Q26Absorb.B13.input ++ rest14 := by
  simp only [rest13,rest14,n25,n26,n27]
  rfl
#print axioms step13
theorem step14 : rest14=JFu_Q26Absorb.B14.input ++ rest15 := by
  simp only [rest14,rest15,n27,n28,n29]
  rfl
#print axioms step14
theorem last : rest15=JFu_Q26Absorb.tail := by
  simp only [rest15,n27,n28,n29]
  rfl
#print axioms last
theorem regroup : numeric=JFu_Q26Absorb.message := by
  change rest00=JFu_Q26Absorb.message
  rw [step00,step01,step02,step03,step04,step05,step06,step07,step08,step09,step10,step11,step12,step13,step14,last]
  simp only [JFu_Q26Absorb.message,JFu_Q26Absorb.head,List.flatten_cons,List.flatten_nil,List.append_nil,List.append_assoc]
#print axioms regroup
theorem native : (flatten (TranscriptStep.absorbParts (encodeState JFu_Q25Source.ratchet) 186#u8 frame)).map Fin.val=numeric := by
  simp only [flatten,TranscriptStep.absorbParts,Array.to_slice,Array.make,List.flatMap_cons,List.flatMap_nil,
    List.map_append,List.append_nil,List.map_map,Function.comp_def,decodeByte,frameBytes,payloadNat,List.map_cons,List.map_nil]
  change ((encodeState JFu_Q25Source.ratchet).val.map (fun x=>x.val)) ++ ([0,186] ++ ([5,160,3,0,0] ++ (n01 ++ n02 ++ n03 ++ n04 ++ n05 ++ n06 ++ n07 ++ n08 ++ n09 ++ n10 ++ n11 ++ n12 ++ n13 ++ n14 ++ n15 ++ n16 ++ n17 ++ n18 ++ n19 ++ n20 ++ n21 ++ n22 ++ n23 ++ n24 ++ n25 ++ n26 ++ n27 ++ n28 ++ n29)))=numeric
  have joined := congrArg (fun lead => lead ++ (n01 ++ n02 ++ n03 ++ n04 ++ n05 ++ n06 ++ n07 ++ n08 ++ n09 ++ n10 ++ n11 ++ n12 ++ n13 ++ n14 ++ n15 ++ n16 ++ n17 ++ n18 ++ n19 ++ n20 ++ n21 ++ n22 ++ n23 ++ n24 ++ n25 ++ n26 ++ n27 ++ n28 ++ n29)) prefixCast
  simpa only [numeric,List.append_assoc] using joined
#print axioms native
end Input
theorem absorbInput : (flatten (TranscriptStep.absorbParts (encodeState JFu_Q25Source.ratchet) 186#u8 frame)).map Fin.val=JFu_Q26Absorb.message := Input.native.trans Input.regroup
#print axioms absorbInput
theorem absorbHash : MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest (TranscriptStep.absorbParts (encodeState JFu_Q25Source.ratchet) 186#u8 frame)=encodeState absorbed := by
  unfold MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest
  rw [absorbInput,JFu_Q26Absorb.checked]
  rfl
#print axioms absorbHash
theorem readInput : (flatten (TranscriptStep.readParts (encodeState absorbed) 1#u8)).map Fin.val=JFu_Q26Read.message := by rfl
#print axioms readInput
theorem readHash : MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest (TranscriptStep.readParts (encodeState absorbed) 1#u8)=encodeState block := by
  unfold MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest
  rw [readInput,JFu_Q26Read.checked]
  rfl
#print axioms readHash
theorem ratchetInput : (flatten (TranscriptStep.readParts (encodeState absorbed) 2#u8)).map Fin.val=JFu_Q26Ratchet.message := by rfl
#print axioms ratchetInput
theorem ratchetHash : MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest (TranscriptStep.readParts (encodeState absorbed) 2#u8)=encodeState ratchet := by
  unfold MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest
  rw [ratchetInput,JFu_Q26Ratchet.checked]
  rfl
#print axioms ratchetHash
theorem source {Hash : Type} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Hash) (hash : Hash) :
    let D0 := AspisR1CurrentCaller.InstalledPreparation.retainedDigest
      (F3V_OracleDictionary.current JFp_SHADigest.digest D)
    r1_wire.SemanticTranscript.sample_block_validated D0
      (⟨encodeState JFu_Q25Source.ratchet,hash,26#u8⟩ : r1_wire.SemanticTranscript Hash)
      26#u8 JFw_NativeRow26.record=ok (.Ok (encodeState block),
        (⟨encodeState ratchet,hash,27#u8⟩ : r1_wire.SemanticTranscript Hash)) := by
  dsimp only
  rw [realFrame,TranscriptStep.step_of_add _ _ 26#u8 186#u8 27#u8 frame rfl (by rfl) (by rfl)]
  change (do let a ← ok (MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest
      (TranscriptStep.absorbParts (encodeState JFu_Q25Source.ratchet) 186#u8 frame))
             let b ← ok (MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest
               (TranscriptStep.readParts a 1#u8))
             let s ← ok (MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest
               (TranscriptStep.readParts a 2#u8))
             ok ((core.result.Result.Ok b : core.result.Result (Array U8 32#usize) r1_wire.Error),(⟨s,hash,27#u8⟩ : r1_wire.SemanticTranscript Hash)))=_
  rw [absorbHash,bind_tc_ok,readHash,bind_tc_ok,ratchetHash,bind_tc_ok]
#print axioms source
theorem word00 : AspisV8R19.SamplerWords.word block ⟨0,by omega⟩=1574570651 := by rfl
#print axioms word00
theorem word01 : AspisV8R19.SamplerWords.word block ⟨1,by omega⟩=1703847754 := by rfl
#print axioms word01
theorem word02 : AspisV8R19.SamplerWords.word block ⟨2,by omega⟩=765166492 := by rfl
#print axioms word02
theorem word03 : AspisV8R19.SamplerWords.word block ⟨3,by omega⟩=2103955475 := by rfl
#print axioms word03
theorem word04 : AspisV8R19.SamplerWords.word block ⟨4,by omega⟩=1299622512 := by rfl
#print axioms word04
theorem word05 : AspisV8R19.SamplerWords.word block ⟨5,by omega⟩=1735857516 := by rfl
#print axioms word05
theorem word06 : AspisV8R19.SamplerWords.word block ⟨6,by omega⟩=620583603 := by rfl
#print axioms word06
theorem word07 : AspisV8R19.SamplerWords.word block ⟨7,by omega⟩=2780420629 := by rfl
#print axioms word07
theorem rank : SourceSamplerByteRank.rank (encodeState block)=74959991873980901949521270482685010187829376068170642026138967491895254190747 := by
  unfold SourceSamplerByteRank.rank
  rw [state_roundtrip,←SamplerBlockRank.word_numeral_eq_rank]
  change SamplerPass.numeral (2^32) ([AspisV8R19.SamplerWords.word block ⟨0,by omega⟩,AspisV8R19.SamplerWords.word block ⟨1,by omega⟩,AspisV8R19.SamplerWords.word block ⟨2,by omega⟩,AspisV8R19.SamplerWords.word block ⟨3,by omega⟩,AspisV8R19.SamplerWords.word block ⟨4,by omega⟩,AspisV8R19.SamplerWords.word block ⟨5,by omega⟩,AspisV8R19.SamplerWords.word block ⟨6,by omega⟩,AspisV8R19.SamplerWords.word block ⟨7,by omega⟩].reverse)=74959991873980901949521270482685010187829376068170642026138967491895254190747
  rw [word00,word01,word02,word03,word04,word05,word06,word07]
  rfl
#print axioms rank
theorem digits : SamplerNatModel.qm31Digits 74959991873980901949521270482685010187829376068170642026138967491895254190747=[758445278,139479390,789205686,1156709222] := by rfl
#print axioms digits
end AspisR1.JFu_Q26Source
