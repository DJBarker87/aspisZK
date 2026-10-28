import JFm_BlockSplit
import NDO_JFm_Q24Source
import NDO_JFw_NativeRow25
import RPz7_ExtractedDigest32SamplerTransport
import NDO_JFu_Q25Aggregate
import NDO_JFu_Q25Reads
set_option autoImplicit false
namespace AspisR1.JFu_Q25Source
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
abbrev frame : Slice U8 := JFw_NativeRow25.record
def absorbed : State := JFp_SHADigest.output JFu_Q25Absorb.result
def block : State := JFp_SHADigest.output JFu_Q25Read.result
def ratchet : State := JFp_SHADigest.output JFu_Q25Ratchet.result
def record : r1_wire.ValidatedRecord := ⟨25#u8,JFw_NativeRow25.record⟩
theorem realFrame : JFw_NativeRow25.record=frame := by
  apply Subtype.ext
  rfl
#print axioms realFrame
namespace Input
attribute [local irreducible] JFx_NativeBytes.proof
def p00 : List U8 := [34#u8,223#u8,66#u8,75#u8,236#u8,13#u8,63#u8,103#u8,122#u8,93#u8,191#u8,89#u8,98#u8,227#u8,173#u8,35#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p01 : List U8 := [142#u8,0#u8,72#u8,7#u8,220#u8,99#u8,36#u8,91#u8,211#u8,49#u8,65#u8,107#u8,113#u8,117#u8,178#u8,112#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p02 : List U8 := [203#u8,165#u8,165#u8,35#u8,80#u8,173#u8,144#u8,21#u8,75#u8,178#u8,103#u8,88#u8,169#u8,233#u8,98#u8,5#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p03 : List U8 := [45#u8,220#u8,233#u8,94#u8,183#u8,30#u8,242#u8,115#u8,243#u8,132#u8,1#u8,106#u8,90#u8,214#u8,59#u8,32#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p04 : List U8 := [168#u8,65#u8,230#u8,38#u8,149#u8,23#u8,80#u8,34#u8,238#u8,223#u8,180#u8,103#u8,25#u8,20#u8,226#u8,126#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p05 : List U8 := [86#u8,144#u8,142#u8,15#u8,142#u8,57#u8,118#u8,85#u8,167#u8,49#u8,196#u8,124#u8,189#u8,200#u8,6#u8,107#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p06 : List U8 := [69#u8,21#u8,150#u8,90#u8,177#u8,199#u8,231#u8,24#u8,150#u8,61#u8,179#u8,101#u8,150#u8,157#u8,24#u8,95#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p07 : List U8 := [135#u8,197#u8,79#u8,50#u8,44#u8,170#u8,72#u8,108#u8,54#u8,5#u8,15#u8,101#u8,7#u8,201#u8,91#u8,35#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p08 : List U8 := [205#u8,250#u8,207#u8,104#u8,66#u8,80#u8,5#u8,102#u8,105#u8,34#u8,63#u8,115#u8,226#u8,98#u8,216#u8,94#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p09 : List U8 := [88#u8,133#u8,77#u8,106#u8,222#u8,80#u8,65#u8,120#u8,244#u8,137#u8,93#u8,112#u8,8#u8,157#u8,9#u8,16#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p10 : List U8 := [246#u8,128#u8,114#u8,80#u8,29#u8,194#u8,185#u8,12#u8,116#u8,5#u8,200#u8,7#u8,5#u8,255#u8,118#u8,69#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p11 : List U8 := [100#u8,235#u8,164#u8,6#u8,82#u8,233#u8,94#u8,120#u8,36#u8,101#u8,175#u8,11#u8,113#u8,16#u8,29#u8,27#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p12 : List U8 := [205#u8,19#u8,211#u8,82#u8,158#u8,229#u8,64#u8,29#u8,130#u8,253#u8,174#u8,29#u8,86#u8,190#u8,153#u8,31#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p13 : List U8 := [150#u8,26#u8,211#u8,57#u8,29#u8,75#u8,16#u8,21#u8,184#u8,154#u8,131#u8,39#u8,55#u8,147#u8,189#u8,86#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p14 : List U8 := [205#u8,209#u8,117#u8,52#u8,47#u8,127#u8,222#u8,63#u8,124#u8,133#u8,255#u8,111#u8,164#u8,90#u8,32#u8,79#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p15 : List U8 := [30#u8,191#u8,249#u8,114#u8,146#u8,15#u8,196#u8,100#u8,119#u8,181#u8,25#u8,19#u8,124#u8,113#u8,145#u8,90#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p16 : List U8 := [0#u8,119#u8,149#u8,28#u8,152#u8,103#u8,243#u8,18#u8,37#u8,144#u8,60#u8,18#u8,119#u8,233#u8,223#u8,85#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p17 : List U8 := [41#u8,161#u8,237#u8,68#u8,172#u8,109#u8,69#u8,112#u8,237#u8,11#u8,115#u8,104#u8,49#u8,162#u8,218#u8,123#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p18 : List U8 := [105#u8,9#u8,198#u8,22#u8,202#u8,243#u8,125#u8,82#u8,213#u8,26#u8,54#u8,65#u8,69#u8,202#u8,22#u8,65#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p19 : List U8 := [13#u8,200#u8,82#u8,9#u8,9#u8,87#u8,201#u8,45#u8,159#u8,156#u8,73#u8,27#u8,43#u8,2#u8,123#u8,126#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p20 : List U8 := [245#u8,193#u8,173#u8,103#u8,186#u8,19#u8,153#u8,36#u8,37#u8,245#u8,106#u8,0#u8,179#u8,116#u8,170#u8,61#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p21 : List U8 := [45#u8,122#u8,176#u8,121#u8,162#u8,212#u8,136#u8,50#u8,3#u8,61#u8,55#u8,101#u8,133#u8,200#u8,203#u8,100#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p22 : List U8 := [212#u8,196#u8,122#u8,108#u8,70#u8,229#u8,208#u8,105#u8,18#u8,202#u8,66#u8,111#u8,159#u8,11#u8,94#u8,92#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p23 : List U8 := [140#u8,136#u8,85#u8,34#u8,182#u8,154#u8,211#u8,116#u8,99#u8,156#u8,229#u8,15#u8,240#u8,133#u8,226#u8,80#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p24 : List U8 := [68#u8,246#u8,99#u8,2#u8,224#u8,117#u8,192#u8,93#u8,180#u8,8#u8,73#u8,67#u8,66#u8,56#u8,141#u8,86#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p25 : List U8 := [237#u8,207#u8,227#u8,1#u8,147#u8,132#u8,11#u8,68#u8,82#u8,253#u8,185#u8,92#u8,127#u8,77#u8,67#u8,40#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p26 : List U8 := [28#u8,184#u8,153#u8,90#u8,58#u8,166#u8,150#u8,117#u8,88#u8,30#u8,185#u8,12#u8,147#u8,141#u8,157#u8,93#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p27 : List U8 := [35#u8,234#u8,16#u8,50#u8,254#u8,61#u8,15#u8,83#u8,165#u8,230#u8,124#u8,86#u8,125#u8,161#u8,85#u8,29#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p28 : List U8 := [134#u8,136#u8,199#u8,95#u8,133#u8,116#u8,35#u8,66#u8,163#u8,48#u8,244#u8,16#u8,193#u8,10#u8,195#u8,92#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p29 : List U8 := [192#u8,139#u8,185#u8,40#u8,252#u8,253#u8,137#u8,66#u8,79#u8,83#u8,12#u8,34#u8,213#u8,1#u8,180#u8,1#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p30 : List U8 := [179#u8,52#u8,236#u8,38#u8,120#u8,117#u8,229#u8,120#u8,109#u8,134#u8,196#u8,5#u8,246#u8,184#u8,68#u8,37#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p31 : List U8 := [224#u8,233#u8,233#u8,117#u8,243#u8,129#u8,75#u8,22#u8,102#u8,67#u8,151#u8,61#u8,237#u8,150#u8,179#u8,72#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p32 : List U8 := [229#u8,19#u8,227#u8,54#u8,115#u8,48#u8,133#u8,40#u8,146#u8,51#u8,159#u8,107#u8,140#u8,127#u8,199#u8,43#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p33 : List U8 := [192#u8,136#u8,247#u8,125#u8,189#u8,158#u8,78#u8,2#u8,115#u8,98#u8,83#u8,10#u8,63#u8,214#u8,113#u8,93#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p34 : List U8 := [52#u8,162#u8,107#u8,86#u8,160#u8,251#u8,56#u8,122#u8,200#u8,151#u8,85#u8,88#u8,206#u8,97#u8,228#u8,16#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p35 : List U8 := [71#u8,38#u8,211#u8,92#u8,241#u8,170#u8,21#u8,126#u8,247#u8,123#u8,94#u8,11#u8,103#u8,215#u8,48#u8,83#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p36 : List U8 := [232#u8,55#u8,203#u8,58#u8,107#u8,55#u8,223#u8,82#u8,164#u8,46#u8,126#u8,13#u8,236#u8,48#u8,24#u8,118#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p37 : List U8 := [66#u8,254#u8,132#u8,28#u8,46#u8,22#u8,69#u8,5#u8,187#u8,173#u8,30#u8,60#u8,48#u8,224#u8,207#u8,114#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p38 : List U8 := [87#u8,66#u8,237#u8,89#u8,246#u8,215#u8,183#u8,31#u8,29#u8,213#u8,146#u8,29#u8,170#u8,223#u8,164#u8,63#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p39 : List U8 := [246#u8,167#u8,74#u8,73#u8,182#u8,250#u8,119#u8,25#u8,229#u8,31#u8,201#u8,27#u8,27#u8,199#u8,237#u8,89#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p40 : List U8 := [166#u8,144#u8,46#u8,74#u8,7#u8,198#u8,226#u8,120#u8,220#u8,152#u8,114#u8,87#u8,67#u8,17#u8,82#u8,16#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p41 : List U8 := [35#u8,226#u8,232#u8,6#u8,225#u8,14#u8,39#u8,111#u8,31#u8,183#u8,122#u8,17#u8,124#u8,210#u8,82#u8,45#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p42 : List U8 := [172#u8,30#u8,217#u8,18#u8,40#u8,103#u8,11#u8,5#u8,53#u8,72#u8,197#u8,78#u8,168#u8,158#u8,249#u8,70#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p43 : List U8 := [122#u8,148#u8,93#u8,17#u8,100#u8,240#u8,182#u8,95#u8,4#u8,132#u8,56#u8,114#u8,84#u8,75#u8,182#u8,127#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p44 : List U8 := [52#u8,92#u8,46#u8,54#u8,34#u8,45#u8,27#u8,105#u8,44#u8,123#u8,150#u8,23#u8,44#u8,59#u8,203#u8,79#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p45 : List U8 := [233#u8,145#u8,26#u8,53#u8,9#u8,216#u8,237#u8,15#u8,152#u8,229#u8,154#u8,52#u8,235#u8,3#u8,145#u8,82#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p46 : List U8 := [6#u8,29#u8,250#u8,92#u8,79#u8,187#u8,210#u8,55#u8,231#u8,99#u8,180#u8,57#u8,246#u8,100#u8,150#u8,66#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p47 : List U8 := [31#u8,70#u8,153#u8,64#u8,194#u8,151#u8,34#u8,34#u8,170#u8,229#u8,174#u8,82#u8,17#u8,254#u8,14#u8,85#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p48 : List U8 := [153#u8,23#u8,212#u8,52#u8,35#u8,249#u8,42#u8,9#u8,89#u8,31#u8,41#u8,21#u8,247#u8,13#u8,216#u8,65#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p49 : List U8 := [4#u8,217#u8,251#u8,112#u8,78#u8,92#u8,105#u8,26#u8,169#u8,163#u8,49#u8,123#u8,210#u8,96#u8,8#u8,22#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p50 : List U8 := [64#u8,137#u8,62#u8,34#u8,94#u8,71#u8,124#u8,123#u8,6#u8,68#u8,104#u8,39#u8,51#u8,61#u8,189#u8,123#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p51 : List U8 := [251#u8,179#u8,55#u8,93#u8,155#u8,194#u8,179#u8,61#u8,114#u8,21#u8,223#u8,8#u8,135#u8,251#u8,61#u8,96#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p52 : List U8 := [155#u8,167#u8,233#u8,18#u8,4#u8,78#u8,11#u8,104#u8,193#u8,222#u8,23#u8,25#u8,107#u8,105#u8,120#u8,12#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p53 : List U8 := [120#u8,189#u8,118#u8,5#u8,72#u8,22#u8,177#u8,88#u8,128#u8,181#u8,31#u8,15#u8,87#u8,229#u8,104#u8,75#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p54 : List U8 := [114#u8,10#u8,49#u8,2#u8,53#u8,76#u8,26#u8,20#u8,110#u8,114#u8,107#u8,26#u8,169#u8,192#u8,42#u8,75#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p55 : List U8 := [49#u8,114#u8,140#u8,41#u8,187#u8,158#u8,62#u8,4#u8,138#u8,73#u8,44#u8,55#u8,14#u8,35#u8,246#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p56 : List U8 := [22#u8,172#u8,206#u8,86#u8,159#u8,96#u8,148#u8,6#u8,22#u8,65#u8,102#u8,56#u8,34#u8,194#u8,217#u8,115#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p57 : List U8 := [76#u8,30#u8,192#u8,48#u8,58#u8,218#u8,182#u8,39#u8,131#u8,70#u8,226#u8,16#u8,178#u8,29#u8,113#u8,30#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p58 : List U8 := [127#u8,252#u8,42#u8,78#u8,251#u8,176#u8,113#u8,45#u8,235#u8,9#u8,94#u8,115#u8,53#u8,252#u8,13#u8,102#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p59 : List U8 := [172#u8,91#u8,37#u8,78#u8,8#u8,21#u8,196#u8,25#u8,240#u8,222#u8,4#u8,112#u8,99#u8,216#u8,106#u8,77#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p60 : List U8 := [117#u8,15#u8,145#u8,87#u8,253#u8,141#u8,43#u8,101#u8,60#u8,156#u8,139#u8,96#u8,50#u8,61#u8,74#u8,18#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p61 : List U8 := [176#u8,242#u8,16#u8,68#u8,138#u8,2#u8,3#u8,50#u8,56#u8,177#u8,249#u8,81#u8,244#u8,135#u8,10#u8,19#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p62 : List U8 := [12#u8,206#u8,223#u8,125#u8,186#u8,51#u8,16#u8,125#u8,76#u8,27#u8,22#u8,5#u8,29#u8,228#u8,115#u8,112#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p63 : List U8 := [144#u8,199#u8,207#u8,74#u8,88#u8,202#u8,195#u8,122#u8,249#u8,234#u8,151#u8,81#u8,31#u8,203#u8,38#u8,127#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p64 : List U8 := [254#u8,251#u8,218#u8,44#u8,93#u8,85#u8,68#u8,28#u8,240#u8,199#u8,16#u8,71#u8,185#u8,201#u8,109#u8,87#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p65 : List U8 := [221#u8,179#u8,118#u8,83#u8,248#u8,102#u8,143#u8,82#u8,105#u8,150#u8,219#u8,115#u8,87#u8,206#u8,233#u8,40#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p66 : List U8 := [119#u8,50#u8,135#u8,112#u8,18#u8,66#u8,121#u8,87#u8,49#u8,120#u8,230#u8,110#u8,119#u8,247#u8,122#u8,87#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p67 : List U8 := [219#u8,31#u8,252#u8,86#u8,182#u8,147#u8,116#u8,97#u8,173#u8,11#u8,34#u8,125#u8,169#u8,253#u8,250#u8,56#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p68 : List U8 := [166#u8,252#u8,10#u8,109#u8,161#u8,228#u8,104#u8,28#u8,202#u8,130#u8,171#u8,44#u8,99#u8,135#u8,186#u8,60#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p69 : List U8 := [33#u8,42#u8,13#u8,95#u8,252#u8,73#u8,0#u8,93#u8,246#u8,205#u8,95#u8,74#u8,201#u8,16#u8,230#u8,100#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p70 : List U8 := [58#u8,18#u8,144#u8,25#u8,190#u8,30#u8,227#u8,120#u8,91#u8,6#u8,129#u8,109#u8,190#u8,178#u8,162#u8,113#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p71 : List U8 := [123#u8,163#u8,62#u8,79#u8,246#u8,3#u8,194#u8,37#u8,76#u8,94#u8,211#u8,62#u8,88#u8,147#u8,181#u8,2#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p72 : List U8 := [210#u8,112#u8,9#u8,46#u8,198#u8,178#u8,227#u8,0#u8,21#u8,125#u8,243#u8,83#u8,5#u8,218#u8,199#u8,96#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p73 : List U8 := [52#u8,95#u8,13#u8,84#u8,194#u8,206#u8,252#u8,37#u8,246#u8,30#u8,241#u8,33#u8,196#u8,77#u8,10#u8,32#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p74 : List U8 := [139#u8,85#u8,1#u8,69#u8,81#u8,98#u8,99#u8,20#u8,128#u8,155#u8,220#u8,106#u8,88#u8,23#u8,152#u8,86#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p75 : List U8 := [26#u8,217#u8,94#u8,91#u8,21#u8,184#u8,18#u8,10#u8,146#u8,87#u8,238#u8,34#u8,48#u8,227#u8,242#u8,67#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p76 : List U8 := [161#u8,37#u8,226#u8,94#u8,178#u8,105#u8,166#u8,113#u8,237#u8,32#u8,168#u8,99#u8,239#u8,52#u8,154#u8,22#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p77 : List U8 := [151#u8,87#u8,141#u8,40#u8,159#u8,37#u8,239#u8,73#u8,121#u8,204#u8,138#u8,7#u8,238#u8,165#u8,2#u8,32#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p78 : List U8 := [90#u8,241#u8,94#u8,109#u8,219#u8,199#u8,120#u8,22#u8,81#u8,123#u8,185#u8,16#u8,14#u8,143#u8,27#u8,44#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p79 : List U8 := [33#u8,252#u8,72#u8,51#u8,174#u8,117#u8,208#u8,58#u8,148#u8,8#u8,214#u8,16#u8,4#u8,208#u8,236#u8,9#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p80 : List U8 := [199#u8,252#u8,35#u8,8#u8,86#u8,244#u8,104#u8,107#u8,174#u8,65#u8,69#u8,63#u8,108#u8,235#u8,118#u8,36#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p81 : List U8 := [21#u8,186#u8,242#u8,56#u8,10#u8,166#u8,5#u8,121#u8,21#u8,198#u8,15#u8,59#u8,173#u8,209#u8,36#u8,28#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p82 : List U8 := [74#u8,234#u8,77#u8,55#u8,209#u8,184#u8,53#u8,9#u8,107#u8,145#u8,87#u8,70#u8,62#u8,70#u8,164#u8,48#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p83 : List U8 := [31#u8,85#u8,111#u8,29#u8,125#u8,20#u8,220#u8,18#u8,199#u8,205#u8,87#u8,4#u8,212#u8,62#u8,80#u8,54#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p84 : List U8 := [122#u8,119#u8,180#u8,80#u8,64#u8,203#u8,234#u8,89#u8,159#u8,86#u8,192#u8,31#u8,15#u8,121#u8,239#u8,9#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p85 : List U8 := [154#u8,228#u8,117#u8,88#u8,33#u8,47#u8,233#u8,42#u8,133#u8,224#u8,21#u8,37#u8,224#u8,148#u8,164#u8,78#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p86 : List U8 := [78#u8,143#u8,19#u8,45#u8,102#u8,186#u8,53#u8,75#u8,44#u8,226#u8,178#u8,8#u8,230#u8,194#u8,98#u8,79#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p87 : List U8 := [54#u8,85#u8,193#u8,10#u8,1#u8,171#u8,37#u8,49#u8,136#u8,108#u8,34#u8,64#u8,175#u8,164#u8,1#u8,122#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p88 : List U8 := [85#u8,225#u8,95#u8,86#u8,217#u8,16#u8,98#u8,53#u8,8#u8,100#u8,128#u8,76#u8,70#u8,206#u8,60#u8,113#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p89 : List U8 := [153#u8,51#u8,176#u8,121#u8,171#u8,178#u8,124#u8,25#u8,113#u8,27#u8,10#u8,67#u8,180#u8,96#u8,75#u8,7#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p90 : List U8 := [61#u8,33#u8,142#u8,57#u8,4#u8,148#u8,98#u8,125#u8,212#u8,241#u8,125#u8,9#u8,79#u8,3#u8,176#u8,4#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p91 : List U8 := [17#u8,218#u8,248#u8,67#u8,148#u8,46#u8,3#u8,66#u8,69#u8,137#u8,193#u8,85#u8,171#u8,153#u8,233#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p92 : List U8 := [6#u8,125#u8,174#u8,114#u8,140#u8,27#u8,239#u8,117#u8,162#u8,113#u8,191#u8,72#u8,122#u8,231#u8,121#u8,18#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p93 : List U8 := [189#u8,111#u8,103#u8,67#u8,218#u8,76#u8,161#u8,37#u8,25#u8,59#u8,115#u8,100#u8,204#u8,76#u8,70#u8,84#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p94 : List U8 := [21#u8,155#u8,0#u8,100#u8,180#u8,207#u8,186#u8,82#u8,76#u8,61#u8,13#u8,87#u8,225#u8,153#u8,202#u8,49#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p95 : List U8 := [25#u8,39#u8,216#u8,100#u8,91#u8,135#u8,199#u8,98#u8,170#u8,6#u8,131#u8,83#u8,226#u8,64#u8,197#u8,4#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p96 : List U8 := [160#u8,200#u8,235#u8,65#u8,92#u8,245#u8,173#u8,7#u8,114#u8,51#u8,238#u8,0#u8,77#u8,189#u8,45#u8,17#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p97 : List U8 := [122#u8,104#u8,27#u8,66#u8,0#u8,97#u8,224#u8,68#u8,172#u8,212#u8,142#u8,16#u8,202#u8,166#u8,208#u8,41#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p98 : List U8 := [77#u8,103#u8,25#u8,74#u8,50#u8,80#u8,194#u8,52#u8,154#u8,16#u8,134#u8,40#u8,31#u8,146#u8,1#u8,95#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p99 : List U8 := [233#u8,205#u8,14#u8,105#u8,116#u8,68#u8,169#u8,99#u8,251#u8,117#u8,218#u8,127#u8,58#u8,26#u8,244#u8,118#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p100 : List U8 := [116#u8,112#u8,174#u8,83#u8,178#u8,6#u8,210#u8,12#u8,116#u8,119#u8,83#u8,80#u8,114#u8,78#u8,204#u8,105#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p101 : List U8 := [102#u8,146#u8,171#u8,83#u8,252#u8,127#u8,123#u8,68#u8,187#u8,41#u8,141#u8,6#u8,144#u8,35#u8,120#u8,44#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p102 : List U8 := [178#u8,85#u8,180#u8,117#u8,97#u8,175#u8,39#u8,126#u8,139#u8,113#u8,250#u8,113#u8,220#u8,199#u8,186#u8,22#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p103 : List U8 := [94#u8,26#u8,0#u8,1#u8,111#u8,90#u8,178#u8,92#u8,171#u8,105#u8,137#u8,10#u8,80#u8,162#u8,219#u8,34#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p104 : List U8 := [140#u8,109#u8,164#u8,39#u8,251#u8,148#u8,132#u8,69#u8,203#u8,120#u8,163#u8,70#u8,143#u8,236#u8,156#u8,81#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p105 : List U8 := [156#u8,34#u8,35#u8,24#u8,23#u8,14#u8,186#u8,21#u8,78#u8,92#u8,116#u8,25#u8,135#u8,207#u8,216#u8,7#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p106 : List U8 := [74#u8,147#u8,251#u8,55#u8,224#u8,166#u8,244#u8,29#u8,21#u8,208#u8,108#u8,18#u8,157#u8,81#u8,198#u8,14#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p107 : List U8 := [97#u8,122#u8,87#u8,56#u8,151#u8,53#u8,112#u8,64#u8,126#u8,55#u8,154#u8,35#u8,201#u8,0#u8,160#u8,111#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p108 : List U8 := [161#u8,137#u8,164#u8,74#u8,224#u8,138#u8,109#u8,51#u8,150#u8,82#u8,81#u8,85#u8,247#u8,102#u8,24#u8,6#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p109 : List U8 := [253#u8,31#u8,111#u8,45#u8,124#u8,91#u8,222#u8,102#u8,36#u8,209#u8,237#u8,112#u8,30#u8,242#u8,231#u8,91#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p110 : List U8 := [234#u8,179#u8,173#u8,4#u8,149#u8,91#u8,160#u8,23#u8,156#u8,104#u8,4#u8,76#u8,127#u8,92#u8,2#u8,85#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p111 : List U8 := [191#u8,62#u8,78#u8,109#u8,232#u8,249#u8,85#u8,9#u8,92#u8,53#u8,120#u8,59#u8,216#u8,192#u8,98#u8,66#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p112 : List U8 := [96#u8,74#u8,42#u8,64#u8,106#u8,44#u8,151#u8,13#u8,199#u8,28#u8,59#u8,16#u8,212#u8,142#u8,155#u8,59#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p113 : List U8 := [61#u8,92#u8,104#u8,23#u8,176#u8,15#u8,234#u8,110#u8,79#u8,134#u8,151#u8,66#u8,31#u8,94#u8,79#u8,48#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p114 : List U8 := [182#u8,159#u8,47#u8,110#u8,51#u8,123#u8,190#u8,94#u8,105#u8,20#u8,26#u8,66#u8,69#u8,9#u8,131#u8,19#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def p115 : List U8 := [184#u8,45#u8,199#u8,1#u8,173#u8,22#u8,151#u8,29#u8,36#u8,107#u8,149#u8,33#u8,36#u8,89#u8,236#u8,96#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
theorem blocks_b00 : JFw_Blocks.blocks 2 JFz_Scan58.b00=[p00,p01] := by rfl
#print axioms blocks_b00
theorem blocks_b01 : JFw_Blocks.blocks 2 JFz_Scan58.b01=[p02,p03] := by rfl
#print axioms blocks_b01
theorem blocks_b02 : JFw_Blocks.blocks 2 JFz_Scan58.b02=[p04,p05] := by rfl
#print axioms blocks_b02
theorem blocks_b03 : JFw_Blocks.blocks 2 JFz_Scan58.b03=[p06,p07] := by rfl
#print axioms blocks_b03
theorem blocks_b04 : JFw_Blocks.blocks 2 JFz_Scan58.b04=[p08,p09] := by rfl
#print axioms blocks_b04
theorem blocks_b05 : JFw_Blocks.blocks 2 JFz_Scan58.b05=[p10,p11] := by rfl
#print axioms blocks_b05
theorem blocks_b06 : JFw_Blocks.blocks 2 JFz_Scan58.b06=[p12,p13] := by rfl
#print axioms blocks_b06
theorem blocks_b07 : JFw_Blocks.blocks 2 JFz_Scan58.b07=[p14,p15] := by rfl
#print axioms blocks_b07
theorem blocks_b08 : JFw_Blocks.blocks 2 JFz_Scan58.b08=[p16,p17] := by rfl
#print axioms blocks_b08
theorem blocks_b09 : JFw_Blocks.blocks 2 JFz_Scan58.b09=[p18,p19] := by rfl
#print axioms blocks_b09
theorem blocks_b10 : JFw_Blocks.blocks 2 JFz_Scan58.b10=[p20,p21] := by rfl
#print axioms blocks_b10
theorem blocks_b11 : JFw_Blocks.blocks 2 JFz_Scan58.b11=[p22,p23] := by rfl
#print axioms blocks_b11
theorem blocks_b12 : JFw_Blocks.blocks 2 JFz_Scan58.b12=[p24,p25] := by rfl
#print axioms blocks_b12
theorem blocks_b13 : JFw_Blocks.blocks 2 JFz_Scan58.b13=[p26,p27] := by rfl
#print axioms blocks_b13
theorem blocks_b14 : JFw_Blocks.blocks 2 JFz_Scan58.b14=[p28,p29] := by rfl
#print axioms blocks_b14
theorem blocks_b15 : JFw_Blocks.blocks 2 JFz_Scan58.b15=[p30,p31] := by rfl
#print axioms blocks_b15
theorem blocks_b16 : JFw_Blocks.blocks 2 JFz_Scan58.b16=[p32,p33] := by rfl
#print axioms blocks_b16
theorem blocks_b17 : JFw_Blocks.blocks 2 JFz_Scan58.b17=[p34,p35] := by rfl
#print axioms blocks_b17
theorem blocks_b18 : JFw_Blocks.blocks 2 JFz_Scan58.b18=[p36,p37] := by rfl
#print axioms blocks_b18
theorem blocks_b19 : JFw_Blocks.blocks 2 JFz_Scan58.b19=[p38,p39] := by rfl
#print axioms blocks_b19
theorem blocks_b20 : JFw_Blocks.blocks 2 JFz_Scan58.b20=[p40,p41] := by rfl
#print axioms blocks_b20
theorem blocks_b21 : JFw_Blocks.blocks 2 JFz_Scan58.b21=[p42,p43] := by rfl
#print axioms blocks_b21
theorem blocks_b22 : JFw_Blocks.blocks 2 JFz_Scan58.b22=[p44,p45] := by rfl
#print axioms blocks_b22
theorem blocks_b23 : JFw_Blocks.blocks 2 JFz_Scan58.b23=[p46,p47] := by rfl
#print axioms blocks_b23
theorem blocks_b24 : JFw_Blocks.blocks 2 JFz_Scan58.b24=[p48,p49] := by rfl
#print axioms blocks_b24
theorem blocks_b25 : JFw_Blocks.blocks 2 JFz_Scan58.b25=[p50,p51] := by rfl
#print axioms blocks_b25
theorem blocks_b26 : JFw_Blocks.blocks 2 JFz_Scan58.b26=[p52,p53] := by rfl
#print axioms blocks_b26
theorem blocks_b27 : JFw_Blocks.blocks 2 JFz_Scan58.b27=[p54,p55] := by rfl
#print axioms blocks_b27
theorem blocks_b28 : JFw_Blocks.blocks 2 JFz_Scan58.b28=[p56,p57] := by rfl
#print axioms blocks_b28
theorem blocks_b29 : JFw_Blocks.blocks 2 JFz_Scan58.b29=[p58,p59] := by rfl
#print axioms blocks_b29
theorem blocks_b30 : JFw_Blocks.blocks 2 JFz_Scan58.b30=[p60,p61] := by rfl
#print axioms blocks_b30
theorem blocks_b31 : JFw_Blocks.blocks 2 JFz_Scan58.b31=[p62,p63] := by rfl
#print axioms blocks_b31
theorem blocks_b32 : JFw_Blocks.blocks 2 JFz_Scan58.b32=[p64,p65] := by rfl
#print axioms blocks_b32
theorem blocks_b33 : JFw_Blocks.blocks 2 JFz_Scan58.b33=[p66,p67] := by rfl
#print axioms blocks_b33
theorem blocks_b34 : JFw_Blocks.blocks 2 JFz_Scan58.b34=[p68,p69] := by rfl
#print axioms blocks_b34
theorem blocks_b35 : JFw_Blocks.blocks 2 JFz_Scan58.b35=[p70,p71] := by rfl
#print axioms blocks_b35
theorem blocks_b36 : JFw_Blocks.blocks 2 JFz_Scan58.b36=[p72,p73] := by rfl
#print axioms blocks_b36
theorem blocks_b37 : JFw_Blocks.blocks 2 JFz_Scan58.b37=[p74,p75] := by rfl
#print axioms blocks_b37
theorem blocks_b38 : JFw_Blocks.blocks 2 JFz_Scan58.b38=[p76,p77] := by rfl
#print axioms blocks_b38
theorem blocks_b39 : JFw_Blocks.blocks 2 JFz_Scan58.b39=[p78,p79] := by rfl
#print axioms blocks_b39
theorem blocks_b40 : JFw_Blocks.blocks 2 JFz_Scan58.b40=[p80,p81] := by rfl
#print axioms blocks_b40
theorem blocks_b41 : JFw_Blocks.blocks 2 JFz_Scan58.b41=[p82,p83] := by rfl
#print axioms blocks_b41
theorem blocks_b42 : JFw_Blocks.blocks 2 JFz_Scan58.b42=[p84,p85] := by rfl
#print axioms blocks_b42
theorem blocks_b43 : JFw_Blocks.blocks 2 JFz_Scan58.b43=[p86,p87] := by rfl
#print axioms blocks_b43
theorem blocks_b44 : JFw_Blocks.blocks 2 JFz_Scan58.b44=[p88,p89] := by rfl
#print axioms blocks_b44
theorem blocks_b45 : JFw_Blocks.blocks 2 JFz_Scan58.b45=[p90,p91] := by rfl
#print axioms blocks_b45
theorem blocks_b46 : JFw_Blocks.blocks 2 JFz_Scan58.b46=[p92,p93] := by rfl
#print axioms blocks_b46
theorem blocks_b47 : JFw_Blocks.blocks 2 JFz_Scan58.b47=[p94,p95] := by rfl
#print axioms blocks_b47
theorem blocks_b48 : JFw_Blocks.blocks 2 JFz_Scan58.b48=[p96,p97] := by rfl
#print axioms blocks_b48
theorem blocks_b49 : JFw_Blocks.blocks 2 JFz_Scan58.b49=[p98,p99] := by rfl
#print axioms blocks_b49
theorem blocks_b50 : JFw_Blocks.blocks 2 JFz_Scan58.b50=[p100,p101] := by rfl
#print axioms blocks_b50
theorem blocks_b51 : JFw_Blocks.blocks 2 JFz_Scan58.b51=[p102,p103] := by rfl
#print axioms blocks_b51
theorem blocks_b52 : JFw_Blocks.blocks 2 JFz_Scan58.b52=[p104,p105] := by rfl
#print axioms blocks_b52
theorem blocks_b53 : JFw_Blocks.blocks 2 JFz_Scan58.b53=[p106,p107] := by rfl
#print axioms blocks_b53
theorem blocks_b54 : JFw_Blocks.blocks 2 JFz_Scan58.b54=[p108,p109] := by rfl
#print axioms blocks_b54
theorem blocks_b55 : JFw_Blocks.blocks 2 JFz_Scan58.b55=[p110,p111] := by rfl
#print axioms blocks_b55
theorem blocks_b56 : JFw_Blocks.blocks 2 JFz_Scan58.b56=[p112,p113] := by rfl
#print axioms blocks_b56
theorem blocks_b57 : JFw_Blocks.blocks 2 JFz_Scan58.b57=[p114,p115] := by rfl
#print axioms blocks_b57
theorem blocks_j00 : JFw_Blocks.blocks 4 JFz_Scan58.j00=[p02,p03,p04,p05] := by
  rw [JFz_Scan58.j00,JFm_BlockSplit.append 2 2 _ _ JFz_Scan58.b01_length,blocks_b01,blocks_b02]
  rfl
#print axioms blocks_j00
theorem blocks_j01 : JFw_Blocks.blocks 6 JFz_Scan58.j01=[p00,p01,p02,p03,p04,p05] := by
  rw [JFz_Scan58.j01,JFm_BlockSplit.append 2 4 _ _ JFz_Scan58.b00_length,blocks_b00,blocks_j00]
  rfl
#print axioms blocks_j01
theorem blocks_j02 : JFw_Blocks.blocks 4 JFz_Scan58.j02=[p06,p07,p08,p09] := by
  rw [JFz_Scan58.j02,JFm_BlockSplit.append 2 2 _ _ JFz_Scan58.b03_length,blocks_b03,blocks_b04]
  rfl
#print axioms blocks_j02
theorem blocks_j03 : JFw_Blocks.blocks 4 JFz_Scan58.j03=[p10,p11,p12,p13] := by
  rw [JFz_Scan58.j03,JFm_BlockSplit.append 2 2 _ _ JFz_Scan58.b05_length,blocks_b05,blocks_b06]
  rfl
#print axioms blocks_j03
theorem blocks_j04 : JFw_Blocks.blocks 8 JFz_Scan58.j04=[p06,p07,p08,p09,p10,p11,p12,p13] := by
  rw [JFz_Scan58.j04,JFm_BlockSplit.append 4 4 _ _ JFz_Scan58.j02_length,blocks_j02,blocks_j03]
  rfl
#print axioms blocks_j04
theorem blocks_j05 : JFw_Blocks.blocks 14 JFz_Scan58.j05=[p00,p01,p02,p03,p04,p05,p06,p07,p08,p09,p10,p11,p12,p13] := by
  rw [JFz_Scan58.j05,JFm_BlockSplit.append 6 8 _ _ JFz_Scan58.j01_length,blocks_j01,blocks_j04]
  rfl
#print axioms blocks_j05
theorem blocks_j06 : JFw_Blocks.blocks 4 JFz_Scan58.j06=[p16,p17,p18,p19] := by
  rw [JFz_Scan58.j06,JFm_BlockSplit.append 2 2 _ _ JFz_Scan58.b08_length,blocks_b08,blocks_b09]
  rfl
#print axioms blocks_j06
theorem blocks_j07 : JFw_Blocks.blocks 6 JFz_Scan58.j07=[p14,p15,p16,p17,p18,p19] := by
  rw [JFz_Scan58.j07,JFm_BlockSplit.append 2 4 _ _ JFz_Scan58.b07_length,blocks_b07,blocks_j06]
  rfl
#print axioms blocks_j07
theorem blocks_j08 : JFw_Blocks.blocks 4 JFz_Scan58.j08=[p20,p21,p22,p23] := by
  rw [JFz_Scan58.j08,JFm_BlockSplit.append 2 2 _ _ JFz_Scan58.b10_length,blocks_b10,blocks_b11]
  rfl
#print axioms blocks_j08
theorem blocks_j09 : JFw_Blocks.blocks 4 JFz_Scan58.j09=[p24,p25,p26,p27] := by
  rw [JFz_Scan58.j09,JFm_BlockSplit.append 2 2 _ _ JFz_Scan58.b12_length,blocks_b12,blocks_b13]
  rfl
#print axioms blocks_j09
theorem blocks_j10 : JFw_Blocks.blocks 8 JFz_Scan58.j10=[p20,p21,p22,p23,p24,p25,p26,p27] := by
  rw [JFz_Scan58.j10,JFm_BlockSplit.append 4 4 _ _ JFz_Scan58.j08_length,blocks_j08,blocks_j09]
  rfl
#print axioms blocks_j10
theorem blocks_j11 : JFw_Blocks.blocks 14 JFz_Scan58.j11=[p14,p15,p16,p17,p18,p19,p20,p21,p22,p23,p24,p25,p26,p27] := by
  rw [JFz_Scan58.j11,JFm_BlockSplit.append 6 8 _ _ JFz_Scan58.j07_length,blocks_j07,blocks_j10]
  rfl
#print axioms blocks_j11
theorem blocks_j12 : JFw_Blocks.blocks 28 JFz_Scan58.j12=[p00,p01,p02,p03,p04,p05,p06,p07,p08,p09,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20,p21,p22,p23,p24,p25,p26,p27] := by
  rw [JFz_Scan58.j12,JFm_BlockSplit.append 14 14 _ _ JFz_Scan58.j05_length,blocks_j05,blocks_j11]
  rfl
#print axioms blocks_j12
theorem blocks_j13 : JFw_Blocks.blocks 4 JFz_Scan58.j13=[p30,p31,p32,p33] := by
  rw [JFz_Scan58.j13,JFm_BlockSplit.append 2 2 _ _ JFz_Scan58.b15_length,blocks_b15,blocks_b16]
  rfl
#print axioms blocks_j13
theorem blocks_j14 : JFw_Blocks.blocks 6 JFz_Scan58.j14=[p28,p29,p30,p31,p32,p33] := by
  rw [JFz_Scan58.j14,JFm_BlockSplit.append 2 4 _ _ JFz_Scan58.b14_length,blocks_b14,blocks_j13]
  rfl
#print axioms blocks_j14
theorem blocks_j15 : JFw_Blocks.blocks 4 JFz_Scan58.j15=[p34,p35,p36,p37] := by
  rw [JFz_Scan58.j15,JFm_BlockSplit.append 2 2 _ _ JFz_Scan58.b17_length,blocks_b17,blocks_b18]
  rfl
#print axioms blocks_j15
theorem blocks_j16 : JFw_Blocks.blocks 4 JFz_Scan58.j16=[p38,p39,p40,p41] := by
  rw [JFz_Scan58.j16,JFm_BlockSplit.append 2 2 _ _ JFz_Scan58.b19_length,blocks_b19,blocks_b20]
  rfl
#print axioms blocks_j16
theorem blocks_j17 : JFw_Blocks.blocks 8 JFz_Scan58.j17=[p34,p35,p36,p37,p38,p39,p40,p41] := by
  rw [JFz_Scan58.j17,JFm_BlockSplit.append 4 4 _ _ JFz_Scan58.j15_length,blocks_j15,blocks_j16]
  rfl
#print axioms blocks_j17
theorem blocks_j18 : JFw_Blocks.blocks 14 JFz_Scan58.j18=[p28,p29,p30,p31,p32,p33,p34,p35,p36,p37,p38,p39,p40,p41] := by
  rw [JFz_Scan58.j18,JFm_BlockSplit.append 6 8 _ _ JFz_Scan58.j14_length,blocks_j14,blocks_j17]
  rfl
#print axioms blocks_j18
theorem blocks_j19 : JFw_Blocks.blocks 4 JFz_Scan58.j19=[p42,p43,p44,p45] := by
  rw [JFz_Scan58.j19,JFm_BlockSplit.append 2 2 _ _ JFz_Scan58.b21_length,blocks_b21,blocks_b22]
  rfl
#print axioms blocks_j19
theorem blocks_j20 : JFw_Blocks.blocks 4 JFz_Scan58.j20=[p46,p47,p48,p49] := by
  rw [JFz_Scan58.j20,JFm_BlockSplit.append 2 2 _ _ JFz_Scan58.b23_length,blocks_b23,blocks_b24]
  rfl
#print axioms blocks_j20
theorem blocks_j21 : JFw_Blocks.blocks 8 JFz_Scan58.j21=[p42,p43,p44,p45,p46,p47,p48,p49] := by
  rw [JFz_Scan58.j21,JFm_BlockSplit.append 4 4 _ _ JFz_Scan58.j19_length,blocks_j19,blocks_j20]
  rfl
#print axioms blocks_j21
theorem blocks_j22 : JFw_Blocks.blocks 4 JFz_Scan58.j22=[p50,p51,p52,p53] := by
  rw [JFz_Scan58.j22,JFm_BlockSplit.append 2 2 _ _ JFz_Scan58.b25_length,blocks_b25,blocks_b26]
  rfl
#print axioms blocks_j22
theorem blocks_j23 : JFw_Blocks.blocks 4 JFz_Scan58.j23=[p54,p55,p56,p57] := by
  rw [JFz_Scan58.j23,JFm_BlockSplit.append 2 2 _ _ JFz_Scan58.b27_length,blocks_b27,blocks_b28]
  rfl
#print axioms blocks_j23
theorem blocks_j24 : JFw_Blocks.blocks 8 JFz_Scan58.j24=[p50,p51,p52,p53,p54,p55,p56,p57] := by
  rw [JFz_Scan58.j24,JFm_BlockSplit.append 4 4 _ _ JFz_Scan58.j22_length,blocks_j22,blocks_j23]
  rfl
#print axioms blocks_j24
theorem blocks_j25 : JFw_Blocks.blocks 16 JFz_Scan58.j25=[p42,p43,p44,p45,p46,p47,p48,p49,p50,p51,p52,p53,p54,p55,p56,p57] := by
  rw [JFz_Scan58.j25,JFm_BlockSplit.append 8 8 _ _ JFz_Scan58.j21_length,blocks_j21,blocks_j24]
  rfl
#print axioms blocks_j25
theorem blocks_j26 : JFw_Blocks.blocks 30 JFz_Scan58.j26=[p28,p29,p30,p31,p32,p33,p34,p35,p36,p37,p38,p39,p40,p41,p42,p43,p44,p45,p46,p47,p48,p49,p50,p51,p52,p53,p54,p55,p56,p57] := by
  rw [JFz_Scan58.j26,JFm_BlockSplit.append 14 16 _ _ JFz_Scan58.j18_length,blocks_j18,blocks_j25]
  rfl
#print axioms blocks_j26
theorem blocks_j27 : JFw_Blocks.blocks 58 JFz_Scan58.j27=[p00,p01,p02,p03,p04,p05,p06,p07,p08,p09,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20,p21,p22,p23,p24,p25,p26,p27,p28,p29,p30,p31,p32,p33,p34,p35,p36,p37,p38,p39,p40,p41,p42,p43,p44,p45,p46,p47,p48,p49,p50,p51,p52,p53,p54,p55,p56,p57] := by
  rw [JFz_Scan58.j27,JFm_BlockSplit.append 28 30 _ _ JFz_Scan58.j12_length,blocks_j12,blocks_j26]
  rfl
#print axioms blocks_j27
theorem blocks_j28 : JFw_Blocks.blocks 4 JFz_Scan58.j28=[p60,p61,p62,p63] := by
  rw [JFz_Scan58.j28,JFm_BlockSplit.append 2 2 _ _ JFz_Scan58.b30_length,blocks_b30,blocks_b31]
  rfl
#print axioms blocks_j28
theorem blocks_j29 : JFw_Blocks.blocks 6 JFz_Scan58.j29=[p58,p59,p60,p61,p62,p63] := by
  rw [JFz_Scan58.j29,JFm_BlockSplit.append 2 4 _ _ JFz_Scan58.b29_length,blocks_b29,blocks_j28]
  rfl
#print axioms blocks_j29
theorem blocks_j30 : JFw_Blocks.blocks 4 JFz_Scan58.j30=[p64,p65,p66,p67] := by
  rw [JFz_Scan58.j30,JFm_BlockSplit.append 2 2 _ _ JFz_Scan58.b32_length,blocks_b32,blocks_b33]
  rfl
#print axioms blocks_j30
theorem blocks_j31 : JFw_Blocks.blocks 4 JFz_Scan58.j31=[p68,p69,p70,p71] := by
  rw [JFz_Scan58.j31,JFm_BlockSplit.append 2 2 _ _ JFz_Scan58.b34_length,blocks_b34,blocks_b35]
  rfl
#print axioms blocks_j31
theorem blocks_j32 : JFw_Blocks.blocks 8 JFz_Scan58.j32=[p64,p65,p66,p67,p68,p69,p70,p71] := by
  rw [JFz_Scan58.j32,JFm_BlockSplit.append 4 4 _ _ JFz_Scan58.j30_length,blocks_j30,blocks_j31]
  rfl
#print axioms blocks_j32
theorem blocks_j33 : JFw_Blocks.blocks 14 JFz_Scan58.j33=[p58,p59,p60,p61,p62,p63,p64,p65,p66,p67,p68,p69,p70,p71] := by
  rw [JFz_Scan58.j33,JFm_BlockSplit.append 6 8 _ _ JFz_Scan58.j29_length,blocks_j29,blocks_j32]
  rfl
#print axioms blocks_j33
theorem blocks_j34 : JFw_Blocks.blocks 4 JFz_Scan58.j34=[p74,p75,p76,p77] := by
  rw [JFz_Scan58.j34,JFm_BlockSplit.append 2 2 _ _ JFz_Scan58.b37_length,blocks_b37,blocks_b38]
  rfl
#print axioms blocks_j34
theorem blocks_j35 : JFw_Blocks.blocks 6 JFz_Scan58.j35=[p72,p73,p74,p75,p76,p77] := by
  rw [JFz_Scan58.j35,JFm_BlockSplit.append 2 4 _ _ JFz_Scan58.b36_length,blocks_b36,blocks_j34]
  rfl
#print axioms blocks_j35
theorem blocks_j36 : JFw_Blocks.blocks 4 JFz_Scan58.j36=[p78,p79,p80,p81] := by
  rw [JFz_Scan58.j36,JFm_BlockSplit.append 2 2 _ _ JFz_Scan58.b39_length,blocks_b39,blocks_b40]
  rfl
#print axioms blocks_j36
theorem blocks_j37 : JFw_Blocks.blocks 4 JFz_Scan58.j37=[p82,p83,p84,p85] := by
  rw [JFz_Scan58.j37,JFm_BlockSplit.append 2 2 _ _ JFz_Scan58.b41_length,blocks_b41,blocks_b42]
  rfl
#print axioms blocks_j37
theorem blocks_j38 : JFw_Blocks.blocks 8 JFz_Scan58.j38=[p78,p79,p80,p81,p82,p83,p84,p85] := by
  rw [JFz_Scan58.j38,JFm_BlockSplit.append 4 4 _ _ JFz_Scan58.j36_length,blocks_j36,blocks_j37]
  rfl
#print axioms blocks_j38
theorem blocks_j39 : JFw_Blocks.blocks 14 JFz_Scan58.j39=[p72,p73,p74,p75,p76,p77,p78,p79,p80,p81,p82,p83,p84,p85] := by
  rw [JFz_Scan58.j39,JFm_BlockSplit.append 6 8 _ _ JFz_Scan58.j35_length,blocks_j35,blocks_j38]
  rfl
#print axioms blocks_j39
theorem blocks_j40 : JFw_Blocks.blocks 28 JFz_Scan58.j40=[p58,p59,p60,p61,p62,p63,p64,p65,p66,p67,p68,p69,p70,p71,p72,p73,p74,p75,p76,p77,p78,p79,p80,p81,p82,p83,p84,p85] := by
  rw [JFz_Scan58.j40,JFm_BlockSplit.append 14 14 _ _ JFz_Scan58.j33_length,blocks_j33,blocks_j39]
  rfl
#print axioms blocks_j40
theorem blocks_j41 : JFw_Blocks.blocks 4 JFz_Scan58.j41=[p88,p89,p90,p91] := by
  rw [JFz_Scan58.j41,JFm_BlockSplit.append 2 2 _ _ JFz_Scan58.b44_length,blocks_b44,blocks_b45]
  rfl
#print axioms blocks_j41
theorem blocks_j42 : JFw_Blocks.blocks 6 JFz_Scan58.j42=[p86,p87,p88,p89,p90,p91] := by
  rw [JFz_Scan58.j42,JFm_BlockSplit.append 2 4 _ _ JFz_Scan58.b43_length,blocks_b43,blocks_j41]
  rfl
#print axioms blocks_j42
theorem blocks_j43 : JFw_Blocks.blocks 4 JFz_Scan58.j43=[p92,p93,p94,p95] := by
  rw [JFz_Scan58.j43,JFm_BlockSplit.append 2 2 _ _ JFz_Scan58.b46_length,blocks_b46,blocks_b47]
  rfl
#print axioms blocks_j43
theorem blocks_j44 : JFw_Blocks.blocks 4 JFz_Scan58.j44=[p96,p97,p98,p99] := by
  rw [JFz_Scan58.j44,JFm_BlockSplit.append 2 2 _ _ JFz_Scan58.b48_length,blocks_b48,blocks_b49]
  rfl
#print axioms blocks_j44
theorem blocks_j45 : JFw_Blocks.blocks 8 JFz_Scan58.j45=[p92,p93,p94,p95,p96,p97,p98,p99] := by
  rw [JFz_Scan58.j45,JFm_BlockSplit.append 4 4 _ _ JFz_Scan58.j43_length,blocks_j43,blocks_j44]
  rfl
#print axioms blocks_j45
theorem blocks_j46 : JFw_Blocks.blocks 14 JFz_Scan58.j46=[p86,p87,p88,p89,p90,p91,p92,p93,p94,p95,p96,p97,p98,p99] := by
  rw [JFz_Scan58.j46,JFm_BlockSplit.append 6 8 _ _ JFz_Scan58.j42_length,blocks_j42,blocks_j45]
  rfl
#print axioms blocks_j46
theorem blocks_j47 : JFw_Blocks.blocks 4 JFz_Scan58.j47=[p100,p101,p102,p103] := by
  rw [JFz_Scan58.j47,JFm_BlockSplit.append 2 2 _ _ JFz_Scan58.b50_length,blocks_b50,blocks_b51]
  rfl
#print axioms blocks_j47
theorem blocks_j48 : JFw_Blocks.blocks 4 JFz_Scan58.j48=[p104,p105,p106,p107] := by
  rw [JFz_Scan58.j48,JFm_BlockSplit.append 2 2 _ _ JFz_Scan58.b52_length,blocks_b52,blocks_b53]
  rfl
#print axioms blocks_j48
theorem blocks_j49 : JFw_Blocks.blocks 8 JFz_Scan58.j49=[p100,p101,p102,p103,p104,p105,p106,p107] := by
  rw [JFz_Scan58.j49,JFm_BlockSplit.append 4 4 _ _ JFz_Scan58.j47_length,blocks_j47,blocks_j48]
  rfl
#print axioms blocks_j49
theorem blocks_j50 : JFw_Blocks.blocks 4 JFz_Scan58.j50=[p108,p109,p110,p111] := by
  rw [JFz_Scan58.j50,JFm_BlockSplit.append 2 2 _ _ JFz_Scan58.b54_length,blocks_b54,blocks_b55]
  rfl
#print axioms blocks_j50
theorem blocks_j51 : JFw_Blocks.blocks 4 JFz_Scan58.j51=[p112,p113,p114,p115] := by
  rw [JFz_Scan58.j51,JFm_BlockSplit.append 2 2 _ _ JFz_Scan58.b56_length,blocks_b56,blocks_b57]
  rfl
#print axioms blocks_j51
theorem blocks_j52 : JFw_Blocks.blocks 8 JFz_Scan58.j52=[p108,p109,p110,p111,p112,p113,p114,p115] := by
  rw [JFz_Scan58.j52,JFm_BlockSplit.append 4 4 _ _ JFz_Scan58.j50_length,blocks_j50,blocks_j51]
  rfl
#print axioms blocks_j52
theorem blocks_j53 : JFw_Blocks.blocks 16 JFz_Scan58.j53=[p100,p101,p102,p103,p104,p105,p106,p107,p108,p109,p110,p111,p112,p113,p114,p115] := by
  rw [JFz_Scan58.j53,JFm_BlockSplit.append 8 8 _ _ JFz_Scan58.j49_length,blocks_j49,blocks_j52]
  rfl
#print axioms blocks_j53
theorem blocks_j54 : JFw_Blocks.blocks 30 JFz_Scan58.j54=[p86,p87,p88,p89,p90,p91,p92,p93,p94,p95,p96,p97,p98,p99,p100,p101,p102,p103,p104,p105,p106,p107,p108,p109,p110,p111,p112,p113,p114,p115] := by
  rw [JFz_Scan58.j54,JFm_BlockSplit.append 14 16 _ _ JFz_Scan58.j46_length,blocks_j46,blocks_j53]
  rfl
#print axioms blocks_j54
theorem blocks_j55 : JFw_Blocks.blocks 58 JFz_Scan58.j55=[p58,p59,p60,p61,p62,p63,p64,p65,p66,p67,p68,p69,p70,p71,p72,p73,p74,p75,p76,p77,p78,p79,p80,p81,p82,p83,p84,p85,p86,p87,p88,p89,p90,p91,p92,p93,p94,p95,p96,p97,p98,p99,p100,p101,p102,p103,p104,p105,p106,p107,p108,p109,p110,p111,p112,p113,p114,p115] := by
  rw [JFz_Scan58.j55,JFm_BlockSplit.append 28 30 _ _ JFz_Scan58.j40_length,blocks_j40,blocks_j54]
  rfl
#print axioms blocks_j55
theorem blocks_j56 : JFw_Blocks.blocks 116 JFz_Scan58.j56=[p00,p01,p02,p03,p04,p05,p06,p07,p08,p09,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20,p21,p22,p23,p24,p25,p26,p27,p28,p29,p30,p31,p32,p33,p34,p35,p36,p37,p38,p39,p40,p41,p42,p43,p44,p45,p46,p47,p48,p49,p50,p51,p52,p53,p54,p55,p56,p57,p58,p59,p60,p61,p62,p63,p64,p65,p66,p67,p68,p69,p70,p71,p72,p73,p74,p75,p76,p77,p78,p79,p80,p81,p82,p83,p84,p85,p86,p87,p88,p89,p90,p91,p92,p93,p94,p95,p96,p97,p98,p99,p100,p101,p102,p103,p104,p105,p106,p107,p108,p109,p110,p111,p112,p113,p114,p115] := by
  rw [JFz_Scan58.j56,JFm_BlockSplit.append 58 58 _ _ JFz_Scan58.j27_length,blocks_j27,blocks_j55]
  rfl
#print axioms blocks_j56
def sourcePayload : List U8 := [p00,p01,p02,p03,p04,p05,p06,p07,p08,p09,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20,p21,p22,p23,p24,p25,p26,p27,p28,p29,p30,p31,p32,p33,p34,p35,p36,p37,p38,p39,p40,p41,p42,p43,p44,p45,p46,p47,p48,p49,p50,p51,p52,p53,p54,p55,p56,p57,p58,p59,p60,p61,p62,p63,p64,p65,p66,p67,p68,p69,p70,p71,p72,p73,p74,p75,p76,p77,p78,p79,p80,p81,p82,p83,p84,p85,p86,p87,p88,p89,p90,p91,p92,p93,p94,p95,p96,p97,p98,p99,p100,p101,p102,p103,p104,p105,p106,p107,p108,p109,p110,p111,p112,p113,p114,p115].flatten
theorem payloadBytes : JFw_NativeRow25.payload.val=sourcePayload := by
  dsimp only [JFw_NativeRow25.payload,JFw_Frames.expandedPayload,JFw_Frames.window]
  rw [JFz_Scan58.selected]
  unfold JFz_Scan58.data
  rw [blocks_j56]
  rfl
#print axioms payloadBytes
theorem frameBytes : JFw_NativeRow25.record.val=[4#u8,128#u8,14#u8,0#u8,0#u8] ++ sourcePayload := by
  change _::_::_::_::_::JFw_NativeRow25.payload.val=_
  rw [payloadBytes]
  rfl
#print axioms frameBytes
def n00 : List Nat := [216,205,220,49,211,152,134,213,198,235,161,218,78,185,79,192,66,117,232,155,248,212,234,84,158,136,111,125,0,37,143,21,0,185,4,128,14,0,0]
def n01 : List Nat := [34,223,66,75,236,13,63,103,122,93,191,89,98,227,173,35,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast01 : (p00).map (fun x=>x.val)=n01 := by rfl
#print axioms cast01
def n02 : List Nat := [142,0,72,7,220,99,36,91,211,49,65,107,113,117,178,112,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast02 : (p01).map (fun x=>x.val)=n02 := by rfl
#print axioms cast02
def n03 : List Nat := [203,165,165,35,80,173,144,21,75,178,103,88,169,233,98,5,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast03 : (p02).map (fun x=>x.val)=n03 := by rfl
#print axioms cast03
def n04 : List Nat := [45,220,233,94,183,30,242,115,243,132,1,106,90,214,59,32,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast04 : (p03).map (fun x=>x.val)=n04 := by rfl
#print axioms cast04
def n05 : List Nat := [168,65,230,38,149,23,80,34,238,223,180,103,25,20,226,126,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast05 : (p04).map (fun x=>x.val)=n05 := by rfl
#print axioms cast05
def n06 : List Nat := [86,144,142,15,142,57,118,85,167,49,196,124,189,200,6,107,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast06 : (p05).map (fun x=>x.val)=n06 := by rfl
#print axioms cast06
def n07 : List Nat := [69,21,150,90,177,199,231,24,150,61,179,101,150,157,24,95,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast07 : (p06).map (fun x=>x.val)=n07 := by rfl
#print axioms cast07
def n08 : List Nat := [135,197,79,50,44,170,72,108,54,5,15,101,7,201,91,35,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast08 : (p07).map (fun x=>x.val)=n08 := by rfl
#print axioms cast08
def n09 : List Nat := [205,250,207,104,66,80,5,102,105,34,63,115,226,98,216,94,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast09 : (p08).map (fun x=>x.val)=n09 := by rfl
#print axioms cast09
def n10 : List Nat := [88,133,77,106,222,80,65,120,244,137,93,112,8,157,9,16,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast10 : (p09).map (fun x=>x.val)=n10 := by rfl
#print axioms cast10
def n11 : List Nat := [246,128,114,80,29,194,185,12,116,5,200,7,5,255,118,69,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast11 : (p10).map (fun x=>x.val)=n11 := by rfl
#print axioms cast11
def n12 : List Nat := [100,235,164,6,82,233,94,120,36,101,175,11,113,16,29,27,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast12 : (p11).map (fun x=>x.val)=n12 := by rfl
#print axioms cast12
def n13 : List Nat := [205,19,211,82,158,229,64,29,130,253,174,29,86,190,153,31,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast13 : (p12).map (fun x=>x.val)=n13 := by rfl
#print axioms cast13
def n14 : List Nat := [150,26,211,57,29,75,16,21,184,154,131,39,55,147,189,86,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast14 : (p13).map (fun x=>x.val)=n14 := by rfl
#print axioms cast14
def n15 : List Nat := [205,209,117,52,47,127,222,63,124,133,255,111,164,90,32,79,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast15 : (p14).map (fun x=>x.val)=n15 := by rfl
#print axioms cast15
def n16 : List Nat := [30,191,249,114,146,15,196,100,119,181,25,19,124,113,145,90,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast16 : (p15).map (fun x=>x.val)=n16 := by rfl
#print axioms cast16
def n17 : List Nat := [0,119,149,28,152,103,243,18,37,144,60,18,119,233,223,85,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast17 : (p16).map (fun x=>x.val)=n17 := by rfl
#print axioms cast17
def n18 : List Nat := [41,161,237,68,172,109,69,112,237,11,115,104,49,162,218,123,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast18 : (p17).map (fun x=>x.val)=n18 := by rfl
#print axioms cast18
def n19 : List Nat := [105,9,198,22,202,243,125,82,213,26,54,65,69,202,22,65,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast19 : (p18).map (fun x=>x.val)=n19 := by rfl
#print axioms cast19
def n20 : List Nat := [13,200,82,9,9,87,201,45,159,156,73,27,43,2,123,126,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast20 : (p19).map (fun x=>x.val)=n20 := by rfl
#print axioms cast20
def n21 : List Nat := [245,193,173,103,186,19,153,36,37,245,106,0,179,116,170,61,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast21 : (p20).map (fun x=>x.val)=n21 := by rfl
#print axioms cast21
def n22 : List Nat := [45,122,176,121,162,212,136,50,3,61,55,101,133,200,203,100,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast22 : (p21).map (fun x=>x.val)=n22 := by rfl
#print axioms cast22
def n23 : List Nat := [212,196,122,108,70,229,208,105,18,202,66,111,159,11,94,92,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast23 : (p22).map (fun x=>x.val)=n23 := by rfl
#print axioms cast23
def n24 : List Nat := [140,136,85,34,182,154,211,116,99,156,229,15,240,133,226,80,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast24 : (p23).map (fun x=>x.val)=n24 := by rfl
#print axioms cast24
def n25 : List Nat := [68,246,99,2,224,117,192,93,180,8,73,67,66,56,141,86,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast25 : (p24).map (fun x=>x.val)=n25 := by rfl
#print axioms cast25
def n26 : List Nat := [237,207,227,1,147,132,11,68,82,253,185,92,127,77,67,40,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast26 : (p25).map (fun x=>x.val)=n26 := by rfl
#print axioms cast26
def n27 : List Nat := [28,184,153,90,58,166,150,117,88,30,185,12,147,141,157,93,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast27 : (p26).map (fun x=>x.val)=n27 := by rfl
#print axioms cast27
def n28 : List Nat := [35,234,16,50,254,61,15,83,165,230,124,86,125,161,85,29,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast28 : (p27).map (fun x=>x.val)=n28 := by rfl
#print axioms cast28
def n29 : List Nat := [134,136,199,95,133,116,35,66,163,48,244,16,193,10,195,92,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast29 : (p28).map (fun x=>x.val)=n29 := by rfl
#print axioms cast29
def n30 : List Nat := [192,139,185,40,252,253,137,66,79,83,12,34,213,1,180,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast30 : (p29).map (fun x=>x.val)=n30 := by rfl
#print axioms cast30
def n31 : List Nat := [179,52,236,38,120,117,229,120,109,134,196,5,246,184,68,37,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast31 : (p30).map (fun x=>x.val)=n31 := by rfl
#print axioms cast31
def n32 : List Nat := [224,233,233,117,243,129,75,22,102,67,151,61,237,150,179,72,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast32 : (p31).map (fun x=>x.val)=n32 := by rfl
#print axioms cast32
def n33 : List Nat := [229,19,227,54,115,48,133,40,146,51,159,107,140,127,199,43,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast33 : (p32).map (fun x=>x.val)=n33 := by rfl
#print axioms cast33
def n34 : List Nat := [192,136,247,125,189,158,78,2,115,98,83,10,63,214,113,93,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast34 : (p33).map (fun x=>x.val)=n34 := by rfl
#print axioms cast34
def n35 : List Nat := [52,162,107,86,160,251,56,122,200,151,85,88,206,97,228,16,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast35 : (p34).map (fun x=>x.val)=n35 := by rfl
#print axioms cast35
def n36 : List Nat := [71,38,211,92,241,170,21,126,247,123,94,11,103,215,48,83,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast36 : (p35).map (fun x=>x.val)=n36 := by rfl
#print axioms cast36
def n37 : List Nat := [232,55,203,58,107,55,223,82,164,46,126,13,236,48,24,118,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast37 : (p36).map (fun x=>x.val)=n37 := by rfl
#print axioms cast37
def n38 : List Nat := [66,254,132,28,46,22,69,5,187,173,30,60,48,224,207,114,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast38 : (p37).map (fun x=>x.val)=n38 := by rfl
#print axioms cast38
def n39 : List Nat := [87,66,237,89,246,215,183,31,29,213,146,29,170,223,164,63,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast39 : (p38).map (fun x=>x.val)=n39 := by rfl
#print axioms cast39
def n40 : List Nat := [246,167,74,73,182,250,119,25,229,31,201,27,27,199,237,89,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast40 : (p39).map (fun x=>x.val)=n40 := by rfl
#print axioms cast40
def n41 : List Nat := [166,144,46,74,7,198,226,120,220,152,114,87,67,17,82,16,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast41 : (p40).map (fun x=>x.val)=n41 := by rfl
#print axioms cast41
def n42 : List Nat := [35,226,232,6,225,14,39,111,31,183,122,17,124,210,82,45,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast42 : (p41).map (fun x=>x.val)=n42 := by rfl
#print axioms cast42
def n43 : List Nat := [172,30,217,18,40,103,11,5,53,72,197,78,168,158,249,70,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast43 : (p42).map (fun x=>x.val)=n43 := by rfl
#print axioms cast43
def n44 : List Nat := [122,148,93,17,100,240,182,95,4,132,56,114,84,75,182,127,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast44 : (p43).map (fun x=>x.val)=n44 := by rfl
#print axioms cast44
def n45 : List Nat := [52,92,46,54,34,45,27,105,44,123,150,23,44,59,203,79,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast45 : (p44).map (fun x=>x.val)=n45 := by rfl
#print axioms cast45
def n46 : List Nat := [233,145,26,53,9,216,237,15,152,229,154,52,235,3,145,82,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast46 : (p45).map (fun x=>x.val)=n46 := by rfl
#print axioms cast46
def n47 : List Nat := [6,29,250,92,79,187,210,55,231,99,180,57,246,100,150,66,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast47 : (p46).map (fun x=>x.val)=n47 := by rfl
#print axioms cast47
def n48 : List Nat := [31,70,153,64,194,151,34,34,170,229,174,82,17,254,14,85,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast48 : (p47).map (fun x=>x.val)=n48 := by rfl
#print axioms cast48
def n49 : List Nat := [153,23,212,52,35,249,42,9,89,31,41,21,247,13,216,65,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast49 : (p48).map (fun x=>x.val)=n49 := by rfl
#print axioms cast49
def n50 : List Nat := [4,217,251,112,78,92,105,26,169,163,49,123,210,96,8,22,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast50 : (p49).map (fun x=>x.val)=n50 := by rfl
#print axioms cast50
def n51 : List Nat := [64,137,62,34,94,71,124,123,6,68,104,39,51,61,189,123,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast51 : (p50).map (fun x=>x.val)=n51 := by rfl
#print axioms cast51
def n52 : List Nat := [251,179,55,93,155,194,179,61,114,21,223,8,135,251,61,96,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast52 : (p51).map (fun x=>x.val)=n52 := by rfl
#print axioms cast52
def n53 : List Nat := [155,167,233,18,4,78,11,104,193,222,23,25,107,105,120,12,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast53 : (p52).map (fun x=>x.val)=n53 := by rfl
#print axioms cast53
def n54 : List Nat := [120,189,118,5,72,22,177,88,128,181,31,15,87,229,104,75,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast54 : (p53).map (fun x=>x.val)=n54 := by rfl
#print axioms cast54
def n55 : List Nat := [114,10,49,2,53,76,26,20,110,114,107,26,169,192,42,75,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast55 : (p54).map (fun x=>x.val)=n55 := by rfl
#print axioms cast55
def n56 : List Nat := [49,114,140,41,187,158,62,4,138,73,44,55,14,35,246,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast56 : (p55).map (fun x=>x.val)=n56 := by rfl
#print axioms cast56
def n57 : List Nat := [22,172,206,86,159,96,148,6,22,65,102,56,34,194,217,115,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast57 : (p56).map (fun x=>x.val)=n57 := by rfl
#print axioms cast57
def n58 : List Nat := [76,30,192,48,58,218,182,39,131,70,226,16,178,29,113,30,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast58 : (p57).map (fun x=>x.val)=n58 := by rfl
#print axioms cast58
def n59 : List Nat := [127,252,42,78,251,176,113,45,235,9,94,115,53,252,13,102,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast59 : (p58).map (fun x=>x.val)=n59 := by rfl
#print axioms cast59
def n60 : List Nat := [172,91,37,78,8,21,196,25,240,222,4,112,99,216,106,77,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast60 : (p59).map (fun x=>x.val)=n60 := by rfl
#print axioms cast60
def n61 : List Nat := [117,15,145,87,253,141,43,101,60,156,139,96,50,61,74,18,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast61 : (p60).map (fun x=>x.val)=n61 := by rfl
#print axioms cast61
def n62 : List Nat := [176,242,16,68,138,2,3,50,56,177,249,81,244,135,10,19,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast62 : (p61).map (fun x=>x.val)=n62 := by rfl
#print axioms cast62
def n63 : List Nat := [12,206,223,125,186,51,16,125,76,27,22,5,29,228,115,112,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast63 : (p62).map (fun x=>x.val)=n63 := by rfl
#print axioms cast63
def n64 : List Nat := [144,199,207,74,88,202,195,122,249,234,151,81,31,203,38,127,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast64 : (p63).map (fun x=>x.val)=n64 := by rfl
#print axioms cast64
def n65 : List Nat := [254,251,218,44,93,85,68,28,240,199,16,71,185,201,109,87,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast65 : (p64).map (fun x=>x.val)=n65 := by rfl
#print axioms cast65
def n66 : List Nat := [221,179,118,83,248,102,143,82,105,150,219,115,87,206,233,40,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast66 : (p65).map (fun x=>x.val)=n66 := by rfl
#print axioms cast66
def n67 : List Nat := [119,50,135,112,18,66,121,87,49,120,230,110,119,247,122,87,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast67 : (p66).map (fun x=>x.val)=n67 := by rfl
#print axioms cast67
def n68 : List Nat := [219,31,252,86,182,147,116,97,173,11,34,125,169,253,250,56,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast68 : (p67).map (fun x=>x.val)=n68 := by rfl
#print axioms cast68
def n69 : List Nat := [166,252,10,109,161,228,104,28,202,130,171,44,99,135,186,60,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast69 : (p68).map (fun x=>x.val)=n69 := by rfl
#print axioms cast69
def n70 : List Nat := [33,42,13,95,252,73,0,93,246,205,95,74,201,16,230,100,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast70 : (p69).map (fun x=>x.val)=n70 := by rfl
#print axioms cast70
def n71 : List Nat := [58,18,144,25,190,30,227,120,91,6,129,109,190,178,162,113,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast71 : (p70).map (fun x=>x.val)=n71 := by rfl
#print axioms cast71
def n72 : List Nat := [123,163,62,79,246,3,194,37,76,94,211,62,88,147,181,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast72 : (p71).map (fun x=>x.val)=n72 := by rfl
#print axioms cast72
def n73 : List Nat := [210,112,9,46,198,178,227,0,21,125,243,83,5,218,199,96,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast73 : (p72).map (fun x=>x.val)=n73 := by rfl
#print axioms cast73
def n74 : List Nat := [52,95,13,84,194,206,252,37,246,30,241,33,196,77,10,32,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast74 : (p73).map (fun x=>x.val)=n74 := by rfl
#print axioms cast74
def n75 : List Nat := [139,85,1,69,81,98,99,20,128,155,220,106,88,23,152,86,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast75 : (p74).map (fun x=>x.val)=n75 := by rfl
#print axioms cast75
def n76 : List Nat := [26,217,94,91,21,184,18,10,146,87,238,34,48,227,242,67,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast76 : (p75).map (fun x=>x.val)=n76 := by rfl
#print axioms cast76
def n77 : List Nat := [161,37,226,94,178,105,166,113,237,32,168,99,239,52,154,22,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast77 : (p76).map (fun x=>x.val)=n77 := by rfl
#print axioms cast77
def n78 : List Nat := [151,87,141,40,159,37,239,73,121,204,138,7,238,165,2,32,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast78 : (p77).map (fun x=>x.val)=n78 := by rfl
#print axioms cast78
def n79 : List Nat := [90,241,94,109,219,199,120,22,81,123,185,16,14,143,27,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast79 : (p78).map (fun x=>x.val)=n79 := by rfl
#print axioms cast79
def n80 : List Nat := [33,252,72,51,174,117,208,58,148,8,214,16,4,208,236,9,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast80 : (p79).map (fun x=>x.val)=n80 := by rfl
#print axioms cast80
def n81 : List Nat := [199,252,35,8,86,244,104,107,174,65,69,63,108,235,118,36,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast81 : (p80).map (fun x=>x.val)=n81 := by rfl
#print axioms cast81
def n82 : List Nat := [21,186,242,56,10,166,5,121,21,198,15,59,173,209,36,28,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast82 : (p81).map (fun x=>x.val)=n82 := by rfl
#print axioms cast82
def n83 : List Nat := [74,234,77,55,209,184,53,9,107,145,87,70,62,70,164,48,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast83 : (p82).map (fun x=>x.val)=n83 := by rfl
#print axioms cast83
def n84 : List Nat := [31,85,111,29,125,20,220,18,199,205,87,4,212,62,80,54,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast84 : (p83).map (fun x=>x.val)=n84 := by rfl
#print axioms cast84
def n85 : List Nat := [122,119,180,80,64,203,234,89,159,86,192,31,15,121,239,9,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast85 : (p84).map (fun x=>x.val)=n85 := by rfl
#print axioms cast85
def n86 : List Nat := [154,228,117,88,33,47,233,42,133,224,21,37,224,148,164,78,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast86 : (p85).map (fun x=>x.val)=n86 := by rfl
#print axioms cast86
def n87 : List Nat := [78,143,19,45,102,186,53,75,44,226,178,8,230,194,98,79,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast87 : (p86).map (fun x=>x.val)=n87 := by rfl
#print axioms cast87
def n88 : List Nat := [54,85,193,10,1,171,37,49,136,108,34,64,175,164,1,122,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast88 : (p87).map (fun x=>x.val)=n88 := by rfl
#print axioms cast88
def n89 : List Nat := [85,225,95,86,217,16,98,53,8,100,128,76,70,206,60,113,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast89 : (p88).map (fun x=>x.val)=n89 := by rfl
#print axioms cast89
def n90 : List Nat := [153,51,176,121,171,178,124,25,113,27,10,67,180,96,75,7,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast90 : (p89).map (fun x=>x.val)=n90 := by rfl
#print axioms cast90
def n91 : List Nat := [61,33,142,57,4,148,98,125,212,241,125,9,79,3,176,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast91 : (p90).map (fun x=>x.val)=n91 := by rfl
#print axioms cast91
def n92 : List Nat := [17,218,248,67,148,46,3,66,69,137,193,85,171,153,233,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast92 : (p91).map (fun x=>x.val)=n92 := by rfl
#print axioms cast92
def n93 : List Nat := [6,125,174,114,140,27,239,117,162,113,191,72,122,231,121,18,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast93 : (p92).map (fun x=>x.val)=n93 := by rfl
#print axioms cast93
def n94 : List Nat := [189,111,103,67,218,76,161,37,25,59,115,100,204,76,70,84,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast94 : (p93).map (fun x=>x.val)=n94 := by rfl
#print axioms cast94
def n95 : List Nat := [21,155,0,100,180,207,186,82,76,61,13,87,225,153,202,49,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast95 : (p94).map (fun x=>x.val)=n95 := by rfl
#print axioms cast95
def n96 : List Nat := [25,39,216,100,91,135,199,98,170,6,131,83,226,64,197,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast96 : (p95).map (fun x=>x.val)=n96 := by rfl
#print axioms cast96
def n97 : List Nat := [160,200,235,65,92,245,173,7,114,51,238,0,77,189,45,17,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast97 : (p96).map (fun x=>x.val)=n97 := by rfl
#print axioms cast97
def n98 : List Nat := [122,104,27,66,0,97,224,68,172,212,142,16,202,166,208,41,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast98 : (p97).map (fun x=>x.val)=n98 := by rfl
#print axioms cast98
def n99 : List Nat := [77,103,25,74,50,80,194,52,154,16,134,40,31,146,1,95,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast99 : (p98).map (fun x=>x.val)=n99 := by rfl
#print axioms cast99
def n100 : List Nat := [233,205,14,105,116,68,169,99,251,117,218,127,58,26,244,118,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast100 : (p99).map (fun x=>x.val)=n100 := by rfl
#print axioms cast100
def n101 : List Nat := [116,112,174,83,178,6,210,12,116,119,83,80,114,78,204,105,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast101 : (p100).map (fun x=>x.val)=n101 := by rfl
#print axioms cast101
def n102 : List Nat := [102,146,171,83,252,127,123,68,187,41,141,6,144,35,120,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast102 : (p101).map (fun x=>x.val)=n102 := by rfl
#print axioms cast102
def n103 : List Nat := [178,85,180,117,97,175,39,126,139,113,250,113,220,199,186,22,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast103 : (p102).map (fun x=>x.val)=n103 := by rfl
#print axioms cast103
def n104 : List Nat := [94,26,0,1,111,90,178,92,171,105,137,10,80,162,219,34,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast104 : (p103).map (fun x=>x.val)=n104 := by rfl
#print axioms cast104
def n105 : List Nat := [140,109,164,39,251,148,132,69,203,120,163,70,143,236,156,81,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast105 : (p104).map (fun x=>x.val)=n105 := by rfl
#print axioms cast105
def n106 : List Nat := [156,34,35,24,23,14,186,21,78,92,116,25,135,207,216,7,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast106 : (p105).map (fun x=>x.val)=n106 := by rfl
#print axioms cast106
def n107 : List Nat := [74,147,251,55,224,166,244,29,21,208,108,18,157,81,198,14,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast107 : (p106).map (fun x=>x.val)=n107 := by rfl
#print axioms cast107
def n108 : List Nat := [97,122,87,56,151,53,112,64,126,55,154,35,201,0,160,111,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast108 : (p107).map (fun x=>x.val)=n108 := by rfl
#print axioms cast108
def n109 : List Nat := [161,137,164,74,224,138,109,51,150,82,81,85,247,102,24,6,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast109 : (p108).map (fun x=>x.val)=n109 := by rfl
#print axioms cast109
def n110 : List Nat := [253,31,111,45,124,91,222,102,36,209,237,112,30,242,231,91,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast110 : (p109).map (fun x=>x.val)=n110 := by rfl
#print axioms cast110
def n111 : List Nat := [234,179,173,4,149,91,160,23,156,104,4,76,127,92,2,85,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast111 : (p110).map (fun x=>x.val)=n111 := by rfl
#print axioms cast111
def n112 : List Nat := [191,62,78,109,232,249,85,9,92,53,120,59,216,192,98,66,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast112 : (p111).map (fun x=>x.val)=n112 := by rfl
#print axioms cast112
def n113 : List Nat := [96,74,42,64,106,44,151,13,199,28,59,16,212,142,155,59,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast113 : (p112).map (fun x=>x.val)=n113 := by rfl
#print axioms cast113
def n114 : List Nat := [61,92,104,23,176,15,234,110,79,134,151,66,31,94,79,48,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast114 : (p113).map (fun x=>x.val)=n114 := by rfl
#print axioms cast114
def n115 : List Nat := [182,159,47,110,51,123,190,94,105,20,26,66,69,9,131,19,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast115 : (p114).map (fun x=>x.val)=n115 := by rfl
#print axioms cast115
def n116 : List Nat := [184,45,199,1,173,22,151,29,36,107,149,33,36,89,236,96,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast116 : (p115).map (fun x=>x.val)=n116 := by rfl
#print axioms cast116
def numeric : List Nat := n00 ++ n01 ++ n02 ++ n03 ++ n04 ++ n05 ++ n06 ++ n07 ++ n08 ++ n09 ++ n10 ++ n11 ++ n12 ++ n13 ++ n14 ++ n15 ++ n16 ++ n17 ++ n18 ++ n19 ++ n20 ++ n21 ++ n22 ++ n23 ++ n24 ++ n25 ++ n26 ++ n27 ++ n28 ++ n29 ++ n30 ++ n31 ++ n32 ++ n33 ++ n34 ++ n35 ++ n36 ++ n37 ++ n38 ++ n39 ++ n40 ++ n41 ++ n42 ++ n43 ++ n44 ++ n45 ++ n46 ++ n47 ++ n48 ++ n49 ++ n50 ++ n51 ++ n52 ++ n53 ++ n54 ++ n55 ++ n56 ++ n57 ++ n58 ++ n59 ++ n60 ++ n61 ++ n62 ++ n63 ++ n64 ++ n65 ++ n66 ++ n67 ++ n68 ++ n69 ++ n70 ++ n71 ++ n72 ++ n73 ++ n74 ++ n75 ++ n76 ++ n77 ++ n78 ++ n79 ++ n80 ++ n81 ++ n82 ++ n83 ++ n84 ++ n85 ++ n86 ++ n87 ++ n88 ++ n89 ++ n90 ++ n91 ++ n92 ++ n93 ++ n94 ++ n95 ++ n96 ++ n97 ++ n98 ++ n99 ++ n100 ++ n101 ++ n102 ++ n103 ++ n104 ++ n105 ++ n106 ++ n107 ++ n108 ++ n109 ++ n110 ++ n111 ++ n112 ++ n113 ++ n114 ++ n115 ++ n116
theorem payloadNat : sourcePayload.map (fun x=>x.val)=n01 ++ n02 ++ n03 ++ n04 ++ n05 ++ n06 ++ n07 ++ n08 ++ n09 ++ n10 ++ n11 ++ n12 ++ n13 ++ n14 ++ n15 ++ n16 ++ n17 ++ n18 ++ n19 ++ n20 ++ n21 ++ n22 ++ n23 ++ n24 ++ n25 ++ n26 ++ n27 ++ n28 ++ n29 ++ n30 ++ n31 ++ n32 ++ n33 ++ n34 ++ n35 ++ n36 ++ n37 ++ n38 ++ n39 ++ n40 ++ n41 ++ n42 ++ n43 ++ n44 ++ n45 ++ n46 ++ n47 ++ n48 ++ n49 ++ n50 ++ n51 ++ n52 ++ n53 ++ n54 ++ n55 ++ n56 ++ n57 ++ n58 ++ n59 ++ n60 ++ n61 ++ n62 ++ n63 ++ n64 ++ n65 ++ n66 ++ n67 ++ n68 ++ n69 ++ n70 ++ n71 ++ n72 ++ n73 ++ n74 ++ n75 ++ n76 ++ n77 ++ n78 ++ n79 ++ n80 ++ n81 ++ n82 ++ n83 ++ n84 ++ n85 ++ n86 ++ n87 ++ n88 ++ n89 ++ n90 ++ n91 ++ n92 ++ n93 ++ n94 ++ n95 ++ n96 ++ n97 ++ n98 ++ n99 ++ n100 ++ n101 ++ n102 ++ n103 ++ n104 ++ n105 ++ n106 ++ n107 ++ n108 ++ n109 ++ n110 ++ n111 ++ n112 ++ n113 ++ n114 ++ n115 ++ n116 := by
  simp only [sourcePayload,List.flatten_cons,List.flatten_nil,List.map_append,List.map_nil,List.append_nil,List.append_assoc,cast01,cast02,cast03,cast04,cast05,cast06,cast07,cast08,cast09,cast10,cast11,cast12,cast13,cast14,cast15,cast16,cast17,cast18,cast19,cast20,cast21,cast22,cast23,cast24,cast25,cast26,cast27,cast28,cast29,cast30,cast31,cast32,cast33,cast34,cast35,cast36,cast37,cast38,cast39,cast40,cast41,cast42,cast43,cast44,cast45,cast46,cast47,cast48,cast49,cast50,cast51,cast52,cast53,cast54,cast55,cast56,cast57,cast58,cast59,cast60,cast61,cast62,cast63,cast64,cast65,cast66,cast67,cast68,cast69,cast70,cast71,cast72,cast73,cast74,cast75,cast76,cast77,cast78,cast79,cast80,cast81,cast82,cast83,cast84,cast85,cast86,cast87,cast88,cast89,cast90,cast91,cast92,cast93,cast94,cast95,cast96,cast97,cast98,cast99,cast100,cast101,cast102,cast103,cast104,cast105,cast106,cast107,cast108,cast109,cast110,cast111,cast112,cast113,cast114,cast115,cast116]
#print axioms payloadNat
theorem prefixCast : ((encodeState JFm_Q24Source.ratchet).val.map (fun x=>x.val)) ++ [0,185] ++ [4,128,14,0,0]=n00 := by rfl
#print axioms prefixCast
end Input
end AspisR1.JFu_Q25Source
