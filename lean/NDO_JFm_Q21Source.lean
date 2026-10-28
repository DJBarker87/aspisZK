import JFm_BlockSplit
import NDO_JFm_Q20Source
import NDO_JFw_NativeRow21
import RPz7_ExtractedDigest32SamplerTransport
import NDO_JFm_Q21Hashes
set_option autoImplicit false
namespace AspisR1.JFm_Q21Source
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
abbrev frame : Slice U8 := JFw_NativeRow21.record
def absorbed : State := JFp_SHADigest.output JFm_Q21Absorb.result
def block : State := JFp_SHADigest.output JFm_Q21Read.result
def ratchet : State := JFp_SHADigest.output JFm_Q21Ratchet.result
def record : r1_wire.ValidatedRecord := ⟨21#u8,JFw_NativeRow21.record⟩
theorem realFrame : JFw_NativeRow21.record=frame := by
  apply Subtype.ext
  rfl
#print axioms realFrame
namespace Input
attribute [local irreducible] JFx_NativeBytes.proof
def p00 : List U8 := [167#u8,10#u8,165#u8,99#u8,159#u8,127#u8,7#u8,32#u8,171#u8,73#u8,176#u8,21#u8,119#u8,7#u8,210#u8,76#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p01 : List U8 := [239#u8,22#u8,213#u8,17#u8,163#u8,229#u8,89#u8,81#u8,168#u8,57#u8,203#u8,126#u8,226#u8,164#u8,148#u8,41#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p02 : List U8 := [52#u8,150#u8,66#u8,96#u8,32#u8,15#u8,166#u8,13#u8,67#u8,194#u8,145#u8,81#u8,68#u8,120#u8,212#u8,127#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p03 : List U8 := [98#u8,20#u8,129#u8,6#u8,254#u8,241#u8,210#u8,95#u8,228#u8,206#u8,218#u8,82#u8,249#u8,45#u8,164#u8,49#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p04 : List U8 := [123#u8,8#u8,57#u8,101#u8,22#u8,220#u8,167#u8,57#u8,41#u8,103#u8,240#u8,93#u8,250#u8,247#u8,184#u8,115#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p05 : List U8 := [190#u8,54#u8,131#u8,19#u8,172#u8,190#u8,86#u8,60#u8,86#u8,70#u8,37#u8,99#u8,142#u8,124#u8,18#u8,39#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p06 : List U8 := [14#u8,96#u8,18#u8,70#u8,190#u8,6#u8,171#u8,118#u8,79#u8,253#u8,250#u8,78#u8,227#u8,138#u8,101#u8,9#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p07 : List U8 := [253#u8,42#u8,39#u8,46#u8,22#u8,141#u8,166#u8,71#u8,204#u8,251#u8,245#u8,90#u8,32#u8,26#u8,58#u8,96#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p08 : List U8 := [3#u8,188#u8,72#u8,63#u8,187#u8,216#u8,60#u8,54#u8,249#u8,97#u8,79#u8,88#u8,2#u8,53#u8,255#u8,52#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p09 : List U8 := [166#u8,74#u8,82#u8,91#u8,241#u8,203#u8,85#u8,10#u8,34#u8,222#u8,167#u8,59#u8,0#u8,168#u8,204#u8,53#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p10 : List U8 := [54#u8,70#u8,90#u8,13#u8,179#u8,137#u8,74#u8,26#u8,68#u8,160#u8,23#u8,7#u8,226#u8,147#u8,87#u8,79#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p11 : List U8 := [33#u8,61#u8,115#u8,46#u8,113#u8,187#u8,92#u8,120#u8,203#u8,92#u8,80#u8,92#u8,128#u8,128#u8,115#u8,75#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p12 : List U8 := [209#u8,247#u8,94#u8,98#u8,84#u8,132#u8,25#u8,100#u8,238#u8,146#u8,33#u8,87#u8,190#u8,198#u8,165#u8,34#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p13 : List U8 := [103#u8,93#u8,50#u8,5#u8,252#u8,252#u8,227#u8,60#u8,16#u8,75#u8,77#u8,125#u8,161#u8,140#u8,196#u8,69#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p14 : List U8 := [231#u8,29#u8,24#u8,12#u8,254#u8,222#u8,171#u8,35#u8,34#u8,121#u8,71#u8,68#u8,152#u8,131#u8,69#u8,34#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p15 : List U8 := [164#u8,178#u8,207#u8,92#u8,165#u8,18#u8,44#u8,54#u8,152#u8,217#u8,239#u8,2#u8,120#u8,5#u8,101#u8,70#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p16 : List U8 := [201#u8,153#u8,195#u8,46#u8,112#u8,47#u8,81#u8,52#u8,228#u8,10#u8,200#u8,118#u8,144#u8,186#u8,188#u8,49#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p17 : List U8 := [212#u8,140#u8,16#u8,13#u8,26#u8,90#u8,215#u8,12#u8,234#u8,122#u8,14#u8,39#u8,102#u8,157#u8,100#u8,90#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p18 : List U8 := [2#u8,159#u8,32#u8,122#u8,40#u8,205#u8,74#u8,4#u8,34#u8,88#u8,205#u8,42#u8,253#u8,171#u8,57#u8,85#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p19 : List U8 := [140#u8,231#u8,107#u8,76#u8,95#u8,237#u8,178#u8,122#u8,142#u8,249#u8,130#u8,68#u8,24#u8,144#u8,82#u8,78#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p20 : List U8 := [138#u8,176#u8,177#u8,24#u8,17#u8,193#u8,241#u8,52#u8,249#u8,196#u8,11#u8,106#u8,145#u8,180#u8,134#u8,38#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p21 : List U8 := [128#u8,43#u8,28#u8,12#u8,253#u8,246#u8,251#u8,26#u8,14#u8,61#u8,201#u8,9#u8,110#u8,111#u8,68#u8,69#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p22 : List U8 := [145#u8,111#u8,35#u8,73#u8,167#u8,207#u8,3#u8,124#u8,165#u8,11#u8,130#u8,6#u8,231#u8,138#u8,105#u8,114#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p23 : List U8 := [244#u8,199#u8,15#u8,52#u8,7#u8,23#u8,92#u8,51#u8,85#u8,179#u8,213#u8,117#u8,241#u8,146#u8,129#u8,29#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p24 : List U8 := [55#u8,241#u8,139#u8,25#u8,56#u8,124#u8,89#u8,72#u8,27#u8,61#u8,25#u8,1#u8,54#u8,70#u8,88#u8,93#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p25 : List U8 := [139#u8,186#u8,214#u8,17#u8,129#u8,52#u8,195#u8,70#u8,193#u8,67#u8,101#u8,14#u8,255#u8,156#u8,228#u8,15#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p26 : List U8 := [197#u8,17#u8,253#u8,73#u8,92#u8,1#u8,213#u8,81#u8,48#u8,17#u8,65#u8,96#u8,158#u8,28#u8,254#u8,94#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p27 : List U8 := [193#u8,160#u8,180#u8,40#u8,6#u8,56#u8,24#u8,114#u8,191#u8,234#u8,200#u8,95#u8,99#u8,114#u8,189#u8,34#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
theorem blocks_b00 : JFw_Blocks.blocks 2 JFz_Scan54.b00=[p00,p01] := by rfl
#print axioms blocks_b00
theorem blocks_b01 : JFw_Blocks.blocks 2 JFz_Scan54.b01=[p02,p03] := by rfl
#print axioms blocks_b01
theorem blocks_b02 : JFw_Blocks.blocks 2 JFz_Scan54.b02=[p04,p05] := by rfl
#print axioms blocks_b02
theorem blocks_b03 : JFw_Blocks.blocks 2 JFz_Scan54.b03=[p06,p07] := by rfl
#print axioms blocks_b03
theorem blocks_b04 : JFw_Blocks.blocks 2 JFz_Scan54.b04=[p08,p09] := by rfl
#print axioms blocks_b04
theorem blocks_b05 : JFw_Blocks.blocks 2 JFz_Scan54.b05=[p10,p11] := by rfl
#print axioms blocks_b05
theorem blocks_b06 : JFw_Blocks.blocks 2 JFz_Scan54.b06=[p12,p13] := by rfl
#print axioms blocks_b06
theorem blocks_b07 : JFw_Blocks.blocks 2 JFz_Scan54.b07=[p14,p15] := by rfl
#print axioms blocks_b07
theorem blocks_b08 : JFw_Blocks.blocks 2 JFz_Scan54.b08=[p16,p17] := by rfl
#print axioms blocks_b08
theorem blocks_b09 : JFw_Blocks.blocks 2 JFz_Scan54.b09=[p18,p19] := by rfl
#print axioms blocks_b09
theorem blocks_b10 : JFw_Blocks.blocks 2 JFz_Scan54.b10=[p20,p21] := by rfl
#print axioms blocks_b10
theorem blocks_b11 : JFw_Blocks.blocks 2 JFz_Scan54.b11=[p22,p23] := by rfl
#print axioms blocks_b11
theorem blocks_b12 : JFw_Blocks.blocks 2 JFz_Scan54.b12=[p24,p25] := by rfl
#print axioms blocks_b12
theorem blocks_b13 : JFw_Blocks.blocks 2 JFz_Scan54.b13=[p26,p27] := by rfl
#print axioms blocks_b13
theorem blocks_j00 : JFw_Blocks.blocks 4 JFz_Scan54.j00=[p02,p03,p04,p05] := by
  rw [JFz_Scan54.j00,JFm_BlockSplit.append 2 2 _ _ JFz_Scan54.b01_length,blocks_b01,blocks_b02]
  rfl
#print axioms blocks_j00
theorem blocks_j01 : JFw_Blocks.blocks 6 JFz_Scan54.j01=[p00,p01,p02,p03,p04,p05] := by
  rw [JFz_Scan54.j01,JFm_BlockSplit.append 2 4 _ _ JFz_Scan54.b00_length,blocks_b00,blocks_j00]
  rfl
#print axioms blocks_j01
theorem blocks_j02 : JFw_Blocks.blocks 4 JFz_Scan54.j02=[p06,p07,p08,p09] := by
  rw [JFz_Scan54.j02,JFm_BlockSplit.append 2 2 _ _ JFz_Scan54.b03_length,blocks_b03,blocks_b04]
  rfl
#print axioms blocks_j02
theorem blocks_j03 : JFw_Blocks.blocks 4 JFz_Scan54.j03=[p10,p11,p12,p13] := by
  rw [JFz_Scan54.j03,JFm_BlockSplit.append 2 2 _ _ JFz_Scan54.b05_length,blocks_b05,blocks_b06]
  rfl
#print axioms blocks_j03
theorem blocks_j04 : JFw_Blocks.blocks 8 JFz_Scan54.j04=[p06,p07,p08,p09,p10,p11,p12,p13] := by
  rw [JFz_Scan54.j04,JFm_BlockSplit.append 4 4 _ _ JFz_Scan54.j02_length,blocks_j02,blocks_j03]
  rfl
#print axioms blocks_j04
theorem blocks_j05 : JFw_Blocks.blocks 14 JFz_Scan54.j05=[p00,p01,p02,p03,p04,p05,p06,p07,p08,p09,p10,p11,p12,p13] := by
  rw [JFz_Scan54.j05,JFm_BlockSplit.append 6 8 _ _ JFz_Scan54.j01_length,blocks_j01,blocks_j04]
  rfl
#print axioms blocks_j05
theorem blocks_j06 : JFw_Blocks.blocks 4 JFz_Scan54.j06=[p16,p17,p18,p19] := by
  rw [JFz_Scan54.j06,JFm_BlockSplit.append 2 2 _ _ JFz_Scan54.b08_length,blocks_b08,blocks_b09]
  rfl
#print axioms blocks_j06
theorem blocks_j07 : JFw_Blocks.blocks 6 JFz_Scan54.j07=[p14,p15,p16,p17,p18,p19] := by
  rw [JFz_Scan54.j07,JFm_BlockSplit.append 2 4 _ _ JFz_Scan54.b07_length,blocks_b07,blocks_j06]
  rfl
#print axioms blocks_j07
theorem blocks_j08 : JFw_Blocks.blocks 4 JFz_Scan54.j08=[p20,p21,p22,p23] := by
  rw [JFz_Scan54.j08,JFm_BlockSplit.append 2 2 _ _ JFz_Scan54.b10_length,blocks_b10,blocks_b11]
  rfl
#print axioms blocks_j08
theorem blocks_j09 : JFw_Blocks.blocks 4 JFz_Scan54.j09=[p24,p25,p26,p27] := by
  rw [JFz_Scan54.j09,JFm_BlockSplit.append 2 2 _ _ JFz_Scan54.b12_length,blocks_b12,blocks_b13]
  rfl
#print axioms blocks_j09
theorem blocks_j10 : JFw_Blocks.blocks 8 JFz_Scan54.j10=[p20,p21,p22,p23,p24,p25,p26,p27] := by
  rw [JFz_Scan54.j10,JFm_BlockSplit.append 4 4 _ _ JFz_Scan54.j08_length,blocks_j08,blocks_j09]
  rfl
#print axioms blocks_j10
theorem blocks_j11 : JFw_Blocks.blocks 14 JFz_Scan54.j11=[p14,p15,p16,p17,p18,p19,p20,p21,p22,p23,p24,p25,p26,p27] := by
  rw [JFz_Scan54.j11,JFm_BlockSplit.append 6 8 _ _ JFz_Scan54.j07_length,blocks_j07,blocks_j10]
  rfl
#print axioms blocks_j11
theorem blocks_j12 : JFw_Blocks.blocks 28 JFz_Scan54.j12=[p00,p01,p02,p03,p04,p05,p06,p07,p08,p09,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20,p21,p22,p23,p24,p25,p26,p27] := by
  rw [JFz_Scan54.j12,JFm_BlockSplit.append 14 14 _ _ JFz_Scan54.j05_length,blocks_j05,blocks_j11]
  rfl
#print axioms blocks_j12
def sourcePayload : List U8 := [p00,p01,p02,p03,p04,p05,p06,p07,p08,p09,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20,p21,p22,p23,p24,p25,p26,p27].flatten
theorem payloadBytes : JFw_NativeRow21.payload.val=sourcePayload := by
  dsimp only [JFw_NativeRow21.payload,JFw_Frames.expandedPayload,JFw_Frames.window]
  rw [JFz_Scan54.selected]
  unfold JFz_Scan54.data
  rw [blocks_j12]
  rfl
#print axioms payloadBytes
theorem frameBytes : JFw_NativeRow21.record.val=[2#u8,128#u8,3#u8,0#u8,0#u8] ++ sourcePayload := by
  change _::_::_::_::_::JFw_NativeRow21.payload.val=_
  rw [payloadBytes]
  rfl
#print axioms frameBytes
def n00 : List Nat := [228,89,26,234,126,233,173,58,121,34,21,47,126,144,172,151,69,38,154,165,182,134,100,249,153,252,230,16,8,187,157,20,0,181,2,128,3,0,0]
def n01 : List Nat := [167,10,165,99,159,127,7,32,171,73,176,21,119,7,210,76,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast01 : (p00).map (fun x=>x.val)=n01 := by rfl
#print axioms cast01
def n02 : List Nat := [239,22,213,17,163,229,89,81,168,57,203,126,226,164,148,41,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast02 : (p01).map (fun x=>x.val)=n02 := by rfl
#print axioms cast02
def n03 : List Nat := [52,150,66,96,32,15,166,13,67,194,145,81,68,120,212,127,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast03 : (p02).map (fun x=>x.val)=n03 := by rfl
#print axioms cast03
def n04 : List Nat := [98,20,129,6,254,241,210,95,228,206,218,82,249,45,164,49,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast04 : (p03).map (fun x=>x.val)=n04 := by rfl
#print axioms cast04
def n05 : List Nat := [123,8,57,101,22,220,167,57,41,103,240,93,250,247,184,115,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast05 : (p04).map (fun x=>x.val)=n05 := by rfl
#print axioms cast05
def n06 : List Nat := [190,54,131,19,172,190,86,60,86,70,37,99,142,124,18,39,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast06 : (p05).map (fun x=>x.val)=n06 := by rfl
#print axioms cast06
def n07 : List Nat := [14,96,18,70,190,6,171,118,79,253,250,78,227,138,101,9,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast07 : (p06).map (fun x=>x.val)=n07 := by rfl
#print axioms cast07
def n08 : List Nat := [253,42,39,46,22,141,166,71,204,251,245,90,32,26,58,96,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast08 : (p07).map (fun x=>x.val)=n08 := by rfl
#print axioms cast08
def n09 : List Nat := [3,188,72,63,187,216,60,54,249,97,79,88,2,53,255,52,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast09 : (p08).map (fun x=>x.val)=n09 := by rfl
#print axioms cast09
def n10 : List Nat := [166,74,82,91,241,203,85,10,34,222,167,59,0,168,204,53,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast10 : (p09).map (fun x=>x.val)=n10 := by rfl
#print axioms cast10
def n11 : List Nat := [54,70,90,13,179,137,74,26,68,160,23,7,226,147,87,79,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast11 : (p10).map (fun x=>x.val)=n11 := by rfl
#print axioms cast11
def n12 : List Nat := [33,61,115,46,113,187,92,120,203,92,80,92,128,128,115,75,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast12 : (p11).map (fun x=>x.val)=n12 := by rfl
#print axioms cast12
def n13 : List Nat := [209,247,94,98,84,132,25,100,238,146,33,87,190,198,165,34,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast13 : (p12).map (fun x=>x.val)=n13 := by rfl
#print axioms cast13
def n14 : List Nat := [103,93,50,5,252,252,227,60,16,75,77,125,161,140,196,69,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast14 : (p13).map (fun x=>x.val)=n14 := by rfl
#print axioms cast14
def n15 : List Nat := [231,29,24,12,254,222,171,35,34,121,71,68,152,131,69,34,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast15 : (p14).map (fun x=>x.val)=n15 := by rfl
#print axioms cast15
def n16 : List Nat := [164,178,207,92,165,18,44,54,152,217,239,2,120,5,101,70,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast16 : (p15).map (fun x=>x.val)=n16 := by rfl
#print axioms cast16
def n17 : List Nat := [201,153,195,46,112,47,81,52,228,10,200,118,144,186,188,49,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast17 : (p16).map (fun x=>x.val)=n17 := by rfl
#print axioms cast17
def n18 : List Nat := [212,140,16,13,26,90,215,12,234,122,14,39,102,157,100,90,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast18 : (p17).map (fun x=>x.val)=n18 := by rfl
#print axioms cast18
def n19 : List Nat := [2,159,32,122,40,205,74,4,34,88,205,42,253,171,57,85,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast19 : (p18).map (fun x=>x.val)=n19 := by rfl
#print axioms cast19
def n20 : List Nat := [140,231,107,76,95,237,178,122,142,249,130,68,24,144,82,78,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast20 : (p19).map (fun x=>x.val)=n20 := by rfl
#print axioms cast20
def n21 : List Nat := [138,176,177,24,17,193,241,52,249,196,11,106,145,180,134,38,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast21 : (p20).map (fun x=>x.val)=n21 := by rfl
#print axioms cast21
def n22 : List Nat := [128,43,28,12,253,246,251,26,14,61,201,9,110,111,68,69,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast22 : (p21).map (fun x=>x.val)=n22 := by rfl
#print axioms cast22
def n23 : List Nat := [145,111,35,73,167,207,3,124,165,11,130,6,231,138,105,114,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast23 : (p22).map (fun x=>x.val)=n23 := by rfl
#print axioms cast23
def n24 : List Nat := [244,199,15,52,7,23,92,51,85,179,213,117,241,146,129,29,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast24 : (p23).map (fun x=>x.val)=n24 := by rfl
#print axioms cast24
def n25 : List Nat := [55,241,139,25,56,124,89,72,27,61,25,1,54,70,88,93,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast25 : (p24).map (fun x=>x.val)=n25 := by rfl
#print axioms cast25
def n26 : List Nat := [139,186,214,17,129,52,195,70,193,67,101,14,255,156,228,15,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast26 : (p25).map (fun x=>x.val)=n26 := by rfl
#print axioms cast26
def n27 : List Nat := [197,17,253,73,92,1,213,81,48,17,65,96,158,28,254,94,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast27 : (p26).map (fun x=>x.val)=n27 := by rfl
#print axioms cast27
def n28 : List Nat := [193,160,180,40,6,56,24,114,191,234,200,95,99,114,189,34,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast28 : (p27).map (fun x=>x.val)=n28 := by rfl
#print axioms cast28
def numeric : List Nat := n00 ++ n01 ++ n02 ++ n03 ++ n04 ++ n05 ++ n06 ++ n07 ++ n08 ++ n09 ++ n10 ++ n11 ++ n12 ++ n13 ++ n14 ++ n15 ++ n16 ++ n17 ++ n18 ++ n19 ++ n20 ++ n21 ++ n22 ++ n23 ++ n24 ++ n25 ++ n26 ++ n27 ++ n28
theorem payloadNat : sourcePayload.map (fun x=>x.val)=n01 ++ n02 ++ n03 ++ n04 ++ n05 ++ n06 ++ n07 ++ n08 ++ n09 ++ n10 ++ n11 ++ n12 ++ n13 ++ n14 ++ n15 ++ n16 ++ n17 ++ n18 ++ n19 ++ n20 ++ n21 ++ n22 ++ n23 ++ n24 ++ n25 ++ n26 ++ n27 ++ n28 := by
  simp only [sourcePayload,List.flatten_cons,List.flatten_nil,List.map_append,List.map_nil,List.append_nil,List.append_assoc,cast01,cast02,cast03,cast04,cast05,cast06,cast07,cast08,cast09,cast10,cast11,cast12,cast13,cast14,cast15,cast16,cast17,cast18,cast19,cast20,cast21,cast22,cast23,cast24,cast25,cast26,cast27,cast28]
#print axioms payloadNat
theorem prefixCast : ((encodeState JFm_Q20Source.ratchet).val.map (fun x=>x.val)) ++ [0,181] ++ [2,128,3,0,0]=n00 := by rfl
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
theorem step00 : rest00=JFm_Q21Absorb.B00.input ++ rest01 := by
  simp only [rest00,rest01,n00,n01]
  rfl
#print axioms step00
theorem step01 : rest01=JFm_Q21Absorb.B01.input ++ rest02 := by
  simp only [rest01,rest02,n01,n02,n03]
  rfl
#print axioms step01
theorem step02 : rest02=JFm_Q21Absorb.B02.input ++ rest03 := by
  simp only [rest02,rest03,n03,n04,n05]
  rfl
#print axioms step02
theorem step03 : rest03=JFm_Q21Absorb.B03.input ++ rest04 := by
  simp only [rest03,rest04,n05,n06,n07]
  rfl
#print axioms step03
theorem step04 : rest04=JFm_Q21Absorb.B04.input ++ rest05 := by
  simp only [rest04,rest05,n07,n08,n09]
  rfl
#print axioms step04
theorem step05 : rest05=JFm_Q21Absorb.B05.input ++ rest06 := by
  simp only [rest05,rest06,n09,n10,n11]
  rfl
#print axioms step05
theorem step06 : rest06=JFm_Q21Absorb.B06.input ++ rest07 := by
  simp only [rest06,rest07,n11,n12,n13]
  rfl
#print axioms step06
theorem step07 : rest07=JFm_Q21Absorb.B07.input ++ rest08 := by
  simp only [rest07,rest08,n13,n14,n15]
  rfl
#print axioms step07
theorem step08 : rest08=JFm_Q21Absorb.B08.input ++ rest09 := by
  simp only [rest08,rest09,n15,n16,n17]
  rfl
#print axioms step08
theorem step09 : rest09=JFm_Q21Absorb.B09.input ++ rest10 := by
  simp only [rest09,rest10,n17,n18,n19]
  rfl
#print axioms step09
theorem step10 : rest10=JFm_Q21Absorb.B10.input ++ rest11 := by
  simp only [rest10,rest11,n19,n20,n21]
  rfl
#print axioms step10
theorem step11 : rest11=JFm_Q21Absorb.B11.input ++ rest12 := by
  simp only [rest11,rest12,n21,n22,n23]
  rfl
#print axioms step11
theorem step12 : rest12=JFm_Q21Absorb.B12.input ++ rest13 := by
  simp only [rest12,rest13,n23,n24,n25]
  rfl
#print axioms step12
theorem step13 : rest13=JFm_Q21Absorb.B13.input ++ rest14 := by
  simp only [rest13,rest14,n25,n26,n27]
  rfl
#print axioms step13
theorem last : rest14=JFm_Q21Absorb.tail := by
  simp only [rest14,n26,n27,n28]
  rfl
#print axioms last
theorem regroup : numeric=JFm_Q21Absorb.message := by
  change rest00=JFm_Q21Absorb.message
  rw [step00,step01,step02,step03,step04,step05,step06,step07,step08,step09,step10,step11,step12,step13,last]
  simp only [JFm_Q21Absorb.message,JFm_Q21Absorb.head,List.flatten_cons,List.flatten_nil,List.append_nil,List.append_assoc]
#print axioms regroup
theorem native : (flatten (TranscriptStep.absorbParts (encodeState JFm_Q20Source.ratchet) 181#u8 frame)).map Fin.val=numeric := by
  simp only [flatten,TranscriptStep.absorbParts,Array.to_slice,Array.make,List.flatMap_cons,List.flatMap_nil,
    List.map_append,List.append_nil,List.map_map,Function.comp_def,decodeByte,frameBytes,payloadNat,List.map_cons,List.map_nil]
  change ((encodeState JFm_Q20Source.ratchet).val.map (fun x=>x.val)) ++ ([0,181] ++ ([2,128,3,0,0] ++ (n01 ++ n02 ++ n03 ++ n04 ++ n05 ++ n06 ++ n07 ++ n08 ++ n09 ++ n10 ++ n11 ++ n12 ++ n13 ++ n14 ++ n15 ++ n16 ++ n17 ++ n18 ++ n19 ++ n20 ++ n21 ++ n22 ++ n23 ++ n24 ++ n25 ++ n26 ++ n27 ++ n28)))=numeric
  have joined := congrArg (fun lead => lead ++ (n01 ++ n02 ++ n03 ++ n04 ++ n05 ++ n06 ++ n07 ++ n08 ++ n09 ++ n10 ++ n11 ++ n12 ++ n13 ++ n14 ++ n15 ++ n16 ++ n17 ++ n18 ++ n19 ++ n20 ++ n21 ++ n22 ++ n23 ++ n24 ++ n25 ++ n26 ++ n27 ++ n28)) prefixCast
  simpa only [numeric,List.append_assoc] using joined
#print axioms native
end Input
theorem absorbInput : (flatten (TranscriptStep.absorbParts (encodeState JFm_Q20Source.ratchet) 181#u8 frame)).map Fin.val=JFm_Q21Absorb.message := Input.native.trans Input.regroup
#print axioms absorbInput
theorem absorbHash : MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest (TranscriptStep.absorbParts (encodeState JFm_Q20Source.ratchet) 181#u8 frame)=encodeState absorbed := by
  unfold MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest
  rw [absorbInput,JFm_Q21Absorb.checked]
  rfl
#print axioms absorbHash
theorem readInput : (flatten (TranscriptStep.readParts (encodeState absorbed) 1#u8)).map Fin.val=JFm_Q21Read.message := by rfl
#print axioms readInput
theorem readHash : MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest (TranscriptStep.readParts (encodeState absorbed) 1#u8)=encodeState block := by
  unfold MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest
  rw [readInput,JFm_Q21Read.checked]
  rfl
#print axioms readHash
theorem ratchetInput : (flatten (TranscriptStep.readParts (encodeState absorbed) 2#u8)).map Fin.val=JFm_Q21Ratchet.message := by rfl
#print axioms ratchetInput
theorem ratchetHash : MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest (TranscriptStep.readParts (encodeState absorbed) 2#u8)=encodeState ratchet := by
  unfold MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest
  rw [ratchetInput,JFm_Q21Ratchet.checked]
  rfl
#print axioms ratchetHash
theorem source {Hash : Type} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Hash) (hash : Hash) :
    let D0 := AspisR1CurrentCaller.InstalledPreparation.retainedDigest
      (F3V_OracleDictionary.current JFp_SHADigest.digest D)
    r1_wire.SemanticTranscript.sample_block_validated D0
      (⟨encodeState JFm_Q20Source.ratchet,hash,21#u8⟩ : r1_wire.SemanticTranscript Hash)
      21#u8 JFw_NativeRow21.record=ok (.Ok (encodeState block),
        (⟨encodeState ratchet,hash,22#u8⟩ : r1_wire.SemanticTranscript Hash)) := by
  dsimp only
  rw [realFrame,TranscriptStep.step_of_add _ _ 21#u8 181#u8 22#u8 frame rfl (by rfl) (by rfl)]
  change (do let a ← ok (MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest
      (TranscriptStep.absorbParts (encodeState JFm_Q20Source.ratchet) 181#u8 frame))
             let b ← ok (MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest
               (TranscriptStep.readParts a 1#u8))
             let s ← ok (MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest
               (TranscriptStep.readParts a 2#u8))
             ok ((core.result.Result.Ok b : core.result.Result (Array U8 32#usize) r1_wire.Error),(⟨s,hash,22#u8⟩ : r1_wire.SemanticTranscript Hash)))=_
  rw [absorbHash,bind_tc_ok,readHash,bind_tc_ok,ratchetHash,bind_tc_ok]
#print axioms source
theorem word00 : AspisV8R19.SamplerWords.word block ⟨0,by omega⟩=2125512747 := by rfl
#print axioms word00
theorem word01 : AspisV8R19.SamplerWords.word block ⟨1,by omega⟩=1814213244 := by rfl
#print axioms word01
theorem word02 : AspisV8R19.SamplerWords.word block ⟨2,by omega⟩=206213353 := by rfl
#print axioms word02
theorem word03 : AspisV8R19.SamplerWords.word block ⟨3,by omega⟩=1857581509 := by rfl
#print axioms word03
theorem word04 : AspisV8R19.SamplerWords.word block ⟨4,by omega⟩=3304681213 := by rfl
#print axioms word04
theorem word05 : AspisV8R19.SamplerWords.word block ⟨5,by omega⟩=996077774 := by rfl
#print axioms word05
theorem word06 : AspisV8R19.SamplerWords.word block ⟨6,by omega⟩=4066994074 := by rfl
#print axioms word06
theorem word07 : AspisV8R19.SamplerWords.word block ⟨7,by omega⟩=2952840402 := by rfl
#print axioms word07
theorem rank : SourceSamplerByteRank.rank (encodeState block)=79608419780056590967010262349479506138932094957432306566229945795359655641131 := by
  unfold SourceSamplerByteRank.rank
  rw [state_roundtrip,←SamplerBlockRank.word_numeral_eq_rank]
  change SamplerPass.numeral (2^32) ([AspisV8R19.SamplerWords.word block ⟨0,by omega⟩,AspisV8R19.SamplerWords.word block ⟨1,by omega⟩,AspisV8R19.SamplerWords.word block ⟨2,by omega⟩,AspisV8R19.SamplerWords.word block ⟨3,by omega⟩,AspisV8R19.SamplerWords.word block ⟨4,by omega⟩,AspisV8R19.SamplerWords.word block ⟨5,by omega⟩,AspisV8R19.SamplerWords.word block ⟨6,by omega⟩,AspisV8R19.SamplerWords.word block ⟨7,by omega⟩].reverse)=79608419780056590967010262349479506138932094957432306566229945795359655641131
  rw [word00,word01,word02,word03,word04,word05,word06,word07]
  rfl
#print axioms rank
theorem digits : SamplerNatModel.qm31Digits 79608419780056590967010262349479506138932094957432306566229945795359655641131=[1410683225,375596669,973261870,122086709] := by rfl
#print axioms digits
theorem semantic {Hash : Type} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Hash) (hash : Hash) :
    let D0 := AspisR1CurrentCaller.InstalledPreparation.retainedDigest
      (F3V_OracleDictionary.current JFp_SHADigest.digest D)
    ∃ q : AspisR1PublicPreparation.aspis_core.field.QM31,
    r1_wire.SemanticTranscript.semantic_validated D0
      (⟨encodeState JFm_Q20Source.ratchet,hash,21#u8⟩ : r1_wire.SemanticTranscript Hash)
      record=ok (.Ok q,(⟨encodeState ratchet,hash,22#u8⟩ : r1_wire.SemanticTranscript Hash)) ∧
    ExtractedQM31SamplerCorrect.coordinates (AspisR1PublicPreparation.SamplerTransport.toOld q)=[1410683225,375596669,973261870,122086709] := by
  obtain ⟨q,call,canon,coords⟩ := AspisR1PublicPreparation.SamplerTransport.sample_total (encodeState block)
  refine ⟨q,?_,by simpa only [rank,digits] using coords⟩
  simp only [r1_wire.SemanticTranscript.semantic_validated,record,r1_wire.ValidatedRecord.impl.row,
    r1_wire.ValidatedRecord.impl.framed,bind_tc_ok]
  rw [if_neg (by change ¬(21:Nat)>24;omega)]
  rw [source,bind_tc_ok]
  change (do let v ← AspisR1PublicPreparation.sampler.qm31_sample (encodeState block)
             ok ((core.result.Result.Ok v : core.result.Result aspis_core.field.QM31 r1_wire.Error),
               (⟨encodeState ratchet,hash,22#u8⟩ : r1_wire.SemanticTranscript Hash)))=_
  rw [call,bind_tc_ok]
#print axioms semantic
end AspisR1.JFm_Q21Source
