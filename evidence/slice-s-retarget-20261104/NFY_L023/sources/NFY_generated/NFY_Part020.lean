import Lean
import Aeneas
import NFY_Part006
import NFY_Part007
import NFY_Part008
import NFY_Part009
import NFY_Part010
import NFY_Part011
import NFY_Part012
import NFY_Part013
import NFY_Part014
import NFY_Part015
import NFY_Part016
import NFY_Part017
import NFY_Part018
import NFY_Part019
import ExtractedTerminalDecoderSuccess
import RPz7_S6CurrentCodecTotalV1
import RPz7_S6CurrentFirstInstallationV1
import RPz7_DrvC_Installation
import AspisR1DecodeKFullV10.Funs
import PSem_FieldCanonical
import R1CandidateCM31Parser
import R1CandidateQM31Parser
import MultiproofConeEndian
import MultiproofConeCanonicalAppend

-- BEGIN copied JFx_DataCheckpoint00: lean/JFx_DataCheckpoint00.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFx_DataCheckpoint00
open Aeneas Aeneas.Std
def c00 : List U8 := [82#u8,49#u8,80#u8,50#u8,67#u8,75#u8,80#u8,50#u8,2#u8,10#u8,1#u8,0#u8,0#u8,0#u8,0#u8,0#u8,85#u8,56#u8,108#u8,80#u8,125#u8,63#u8,238#u8,235#u8,252#u8,69#u8,39#u8,42#u8,28#u8,241#u8,92#u8,51#u8]
theorem c00_length : c00.length = 32 := by simp only [c00,List.length_cons,List.length_nil]
#print axioms c00_length
def c01 : List U8 := [204#u8,185#u8,204#u8,240#u8,168#u8,168#u8,244#u8,17#u8,128#u8,252#u8,101#u8,77#u8,128#u8,111#u8,255#u8,111#u8,246#u8,188#u8,212#u8,148#u8,70#u8,241#u8,7#u8,125#u8,44#u8,94#u8,212#u8,190#u8,148#u8,14#u8,145#u8,240#u8]
theorem c01_length : c01.length = 32 := by simp only [c01,List.length_cons,List.length_nil]
#print axioms c01_length
def c02 : List U8 := [190#u8,68#u8,78#u8,252#u8,90#u8,232#u8,48#u8,36#u8,236#u8,7#u8,0#u8,184#u8,194#u8,5#u8,195#u8,49#u8,221#u8,90#u8,114#u8,244#u8,118#u8,28#u8,79#u8,177#u8,218#u8,241#u8,150#u8,70#u8,88#u8,109#u8,78#u8,121#u8]
theorem c02_length : c02.length = 32 := by simp only [c02,List.length_cons,List.length_nil]
#print axioms c02_length
def c03 : List U8 := [71#u8,84#u8,228#u8,197#u8,229#u8,251#u8,221#u8,242#u8,14#u8,76#u8,246#u8,26#u8,93#u8,145#u8,251#u8,132#u8,154#u8,186#u8,129#u8,123#u8,118#u8,141#u8,34#u8,107#u8,41#u8,162#u8,65#u8,31#u8,231#u8,186#u8,247#u8,183#u8]
theorem c03_length : c03.length = 32 := by simp only [c03,List.length_cons,List.length_nil]
#print axioms c03_length
def c04 : List U8 := [176#u8,78#u8,206#u8,66#u8,178#u8,115#u8,221#u8,182#u8,126#u8,10#u8,44#u8,98#u8,98#u8,19#u8,142#u8,75#u8,187#u8,179#u8,50#u8,81#u8,254#u8,209#u8,90#u8,69#u8,227#u8,132#u8,48#u8,25#u8,66#u8,63#u8,114#u8,62#u8]
theorem c04_length : c04.length = 32 := by simp only [c04,List.length_cons,List.length_nil]
#print axioms c04_length
def c05 : List U8 := [10#u8,165#u8,82#u8,0#u8,175#u8,83#u8,136#u8,107#u8,86#u8,58#u8,136#u8,54#u8,4#u8,206#u8,252#u8,106#u8,235#u8,4#u8,0#u8,51#u8,247#u8,16#u8,103#u8,88#u8,217#u8,32#u8,44#u8,113#u8,70#u8,87#u8,65#u8,110#u8]
theorem c05_length : c05.length = 32 := by simp only [c05,List.length_cons,List.length_nil]
#print axioms c05_length
def c06 : List U8 := [253#u8,249#u8,77#u8,66#u8,17#u8,56#u8,25#u8,107#u8,107#u8,253#u8,155#u8,109#u8,76#u8,18#u8,245#u8,24#u8,57#u8,233#u8,142#u8,66#u8,163#u8,48#u8,44#u8,94#u8,32#u8,13#u8,28#u8,70#u8,184#u8,14#u8,111#u8,43#u8]
theorem c06_length : c06.length = 32 := by simp only [c06,List.length_cons,List.length_nil]
#print axioms c06_length
def c07 : List U8 := [104#u8,223#u8,46#u8,38#u8,153#u8,16#u8,93#u8,71#u8,79#u8,50#u8,159#u8,127#u8,13#u8,29#u8,254#u8,72#u8,28#u8,22#u8,98#u8,29#u8,30#u8,22#u8,71#u8,42#u8,70#u8,207#u8,106#u8,96#u8,178#u8,29#u8,185#u8,35#u8]
theorem c07_length : c07.length = 32 := by simp only [c07,List.length_cons,List.length_nil]
#print axioms c07_length
def c08 : List U8 := [60#u8,22#u8,115#u8,99#u8,125#u8,55#u8,176#u8,74#u8,29#u8,35#u8,95#u8,20#u8,75#u8,185#u8,123#u8,52#u8,237#u8,158#u8,163#u8,114#u8,251#u8,162#u8,41#u8,36#u8,196#u8,7#u8,69#u8,23#u8,193#u8,178#u8,228#u8,84#u8]
theorem c08_length : c08.length = 32 := by simp only [c08,List.length_cons,List.length_nil]
#print axioms c08_length
def c09 : List U8 := [5#u8,89#u8,94#u8,95#u8,46#u8,195#u8,117#u8,33#u8,168#u8,49#u8,81#u8,73#u8,182#u8,92#u8,89#u8,30#u8,31#u8,217#u8,61#u8,89#u8,231#u8,15#u8,145#u8,16#u8,105#u8,50#u8,82#u8,52#u8,26#u8,36#u8,204#u8,101#u8]
theorem c09_length : c09.length = 32 := by simp only [c09,List.length_cons,List.length_nil]
#print axioms c09_length
def c10 : List U8 := [59#u8,109#u8,1#u8,0#u8,73#u8,64#u8,2#u8,0#u8,247#u8,78#u8,3#u8,0#u8,139#u8,192#u8,3#u8,0#u8,219#u8,49#u8,3#u8,0#u8,61#u8,239#u8,2#u8,0#u8,57#u8,0#u8,1#u8,0#u8,51#u8,206#u8,2#u8,0#u8]
theorem c10_length : c10.length = 32 := by simp only [c10,List.length_cons,List.length_nil]
#print axioms c10_length
def c11 : List U8 := [69#u8,242#u8,2#u8,0#u8,69#u8,112#u8,2#u8,0#u8,3#u8,5#u8,2#u8,0#u8,238#u8,83#u8,3#u8,0#u8,160#u8,183#u8,2#u8,0#u8,120#u8,72#u8,2#u8,0#u8,21#u8,137#u8,2#u8,0#u8,174#u8,164#u8,0#u8,0#u8]
theorem c11_length : c11.length = 32 := by simp only [c11,List.length_cons,List.length_nil]
#print axioms c11_length
def c12 : List U8 := [166#u8,189#u8,2#u8,0#u8,0#u8,83#u8,0#u8,0#u8,116#u8,249#u8,0#u8,0#u8,81#u8,216#u8,0#u8,0#u8,37#u8,213#u8,2#u8,0#u8,217#u8,55#u8,0#u8,0#u8,214#u8,175#u8,10#u8,42#u8,181#u8,108#u8,37#u8,116#u8]
theorem c12_length : c12.length = 32 := by simp only [c12,List.length_cons,List.length_nil]
#print axioms c12_length
def c13 : List U8 := [156#u8,123#u8,234#u8,51#u8,161#u8,62#u8,30#u8,12#u8,50#u8,153#u8,132#u8,31#u8,173#u8,236#u8,176#u8,99#u8,5#u8,157#u8,245#u8,75#u8,219#u8,43#u8,237#u8,32#u8,211#u8,150#u8,203#u8,98#u8,216#u8,96#u8,41#u8,17#u8]
theorem c13_length : c13.length = 32 := by simp only [c13,List.length_cons,List.length_nil]
#print axioms c13_length
def c14 : List U8 := [2#u8,53#u8,111#u8,108#u8,11#u8,93#u8,16#u8,71#u8,30#u8,215#u8,23#u8,68#u8,113#u8,47#u8,147#u8,119#u8,174#u8,12#u8,137#u8,100#u8,240#u8,68#u8,227#u8,119#u8,118#u8,179#u8,242#u8,65#u8,135#u8,220#u8,110#u8,20#u8]
theorem c14_length : c14.length = 32 := by simp only [c14,List.length_cons,List.length_nil]
#print axioms c14_length
def c15 : List U8 := [50#u8,162#u8,205#u8,61#u8,231#u8,21#u8,47#u8,18#u8,231#u8,29#u8,84#u8,48#u8,211#u8,248#u8,236#u8,68#u8,227#u8,29#u8,211#u8,45#u8,183#u8,249#u8,181#u8,60#u8,89#u8,81#u8,21#u8,84#u8,125#u8,38#u8,99#u8,22#u8]
theorem c15_length : c15.length = 32 := by simp only [c15,List.length_cons,List.length_nil]
#print axioms c15_length
def c16 : List U8 := [46#u8,204#u8,2#u8,58#u8,53#u8,229#u8,70#u8,7#u8,96#u8,184#u8,161#u8,120#u8,16#u8,161#u8,152#u8,58#u8,225#u8,214#u8,50#u8,11#u8,45#u8,46#u8,198#u8,79#u8,5#u8,148#u8,21#u8,27#u8,58#u8,246#u8,17#u8,30#u8]
theorem c16_length : c16.length = 32 := by simp only [c16,List.length_cons,List.length_nil]
#print axioms c16_length
def c17 : List U8 := [212#u8,233#u8,176#u8,119#u8,38#u8,98#u8,170#u8,74#u8,199#u8,206#u8,2#u8,121#u8,76#u8,41#u8,17#u8,84#u8,74#u8,195#u8,94#u8,113#u8,27#u8,151#u8,189#u8,3#u8,152#u8,192#u8,147#u8,114#u8,7#u8,19#u8,38#u8,105#u8]
theorem c17_length : c17.length = 32 := by simp only [c17,List.length_cons,List.length_nil]
#print axioms c17_length
def c18 : List U8 := [111#u8,109#u8,251#u8,64#u8,62#u8,191#u8,48#u8,117#u8,192#u8,152#u8,163#u8,34#u8,166#u8,158#u8,231#u8,14#u8,127#u8,59#u8,111#u8,113#u8,209#u8,57#u8,61#u8,108#u8,76#u8,8#u8,74#u8,95#u8,210#u8,106#u8,165#u8,101#u8]
theorem c18_length : c18.length = 32 := by simp only [c18,List.length_cons,List.length_nil]
#print axioms c18_length
def c19 : List U8 := [124#u8,170#u8,252#u8,2#u8,19#u8,144#u8,163#u8,23#u8,116#u8,160#u8,53#u8,81#u8,252#u8,112#u8,207#u8,17#u8,181#u8,168#u8,117#u8,54#u8,94#u8,96#u8,135#u8,121#u8,192#u8,108#u8,144#u8,98#u8,202#u8,69#u8,182#u8,66#u8]
theorem c19_length : c19.length = 32 := by simp only [c19,List.length_cons,List.length_nil]
#print axioms c19_length
def c20 : List U8 := [67#u8,126#u8,171#u8,89#u8,244#u8,136#u8,135#u8,72#u8,218#u8,224#u8,64#u8,119#u8,97#u8,98#u8,74#u8,97#u8,57#u8,41#u8,226#u8,92#u8,194#u8,150#u8,124#u8,76#u8,147#u8,82#u8,20#u8,87#u8,76#u8,154#u8,32#u8,113#u8]
theorem c20_length : c20.length = 32 := by simp only [c20,List.length_cons,List.length_nil]
#print axioms c20_length
def c21 : List U8 := [207#u8,214#u8,47#u8,122#u8,116#u8,229#u8,65#u8,26#u8,3#u8,163#u8,110#u8,115#u8,72#u8,55#u8,75#u8,6#u8,5#u8,211#u8,116#u8,93#u8,120#u8,200#u8,255#u8,126#u8,151#u8,188#u8,19#u8,60#u8,50#u8,123#u8,90#u8,31#u8]
theorem c21_length : c21.length = 32 := by simp only [c21,List.length_cons,List.length_nil]
#print axioms c21_length
def c22 : List U8 := [251#u8,194#u8,185#u8,20#u8,60#u8,86#u8,254#u8,15#u8,207#u8,95#u8,150#u8,15#u8,45#u8,12#u8,202#u8,98#u8,17#u8,162#u8,150#u8,101#u8,83#u8,224#u8,64#u8,53#u8,140#u8,129#u8,45#u8,28#u8,137#u8,64#u8,132#u8,46#u8]
theorem c22_length : c22.length = 32 := by simp only [c22,List.length_cons,List.length_nil]
#print axioms c22_length
def c23 : List U8 := [176#u8,43#u8,72#u8,41#u8,151#u8,153#u8,59#u8,57#u8,19#u8,52#u8,219#u8,5#u8,129#u8,255#u8,21#u8,115#u8,2#u8,34#u8,138#u8,44#u8,238#u8,198#u8,176#u8,3#u8,64#u8,86#u8,132#u8,51#u8,241#u8,35#u8,134#u8,71#u8]
theorem c23_length : c23.length = 32 := by simp only [c23,List.length_cons,List.length_nil]
#print axioms c23_length
def c24 : List U8 := [134#u8,124#u8,177#u8,103#u8,253#u8,10#u8,190#u8,75#u8,83#u8,227#u8,92#u8,27#u8,121#u8,57#u8,21#u8,64#u8,197#u8,189#u8,232#u8,26#u8,69#u8,89#u8,30#u8,36#u8,148#u8,196#u8,198#u8,70#u8,199#u8,65#u8,194#u8,74#u8]
theorem c24_length : c24.length = 32 := by simp only [c24,List.length_cons,List.length_nil]
#print axioms c24_length
def c25 : List U8 := [254#u8,9#u8,217#u8,48#u8,11#u8,237#u8,223#u8,68#u8,183#u8,169#u8,161#u8,46#u8,204#u8,89#u8,27#u8,91#u8,179#u8,163#u8,215#u8,106#u8,228#u8,174#u8,17#u8,116#u8,216#u8,206#u8,251#u8,79#u8,23#u8,233#u8,254#u8,59#u8]
theorem c25_length : c25.length = 32 := by simp only [c25,List.length_cons,List.length_nil]
#print axioms c25_length
def c26 : List U8 := [126#u8,118#u8,225#u8,52#u8,180#u8,125#u8,249#u8,23#u8,179#u8,131#u8,51#u8,23#u8,77#u8,239#u8,147#u8,79#u8,205#u8,128#u8,178#u8,41#u8,44#u8,19#u8,21#u8,79#u8,214#u8,130#u8,16#u8,92#u8,195#u8,196#u8,204#u8,9#u8]
theorem c26_length : c26.length = 32 := by simp only [c26,List.length_cons,List.length_nil]
#print axioms c26_length
def c27 : List U8 := [135#u8,63#u8,72#u8,86#u8,92#u8,202#u8,213#u8,61#u8,229#u8,24#u8,163#u8,119#u8,11#u8,233#u8,24#u8,88#u8,39#u8,175#u8,99#u8,32#u8,84#u8,220#u8,255#u8,73#u8,180#u8,150#u8,79#u8,103#u8,36#u8,114#u8,223#u8,30#u8]
theorem c27_length : c27.length = 32 := by simp only [c27,List.length_cons,List.length_nil]
#print axioms c27_length
def c28 : List U8 := [155#u8,211#u8,46#u8,11#u8,222#u8,248#u8,83#u8,103#u8,46#u8,96#u8,5#u8,36#u8,2#u8,9#u8,114#u8,95#u8,247#u8,7#u8,213#u8,54#u8,228#u8,123#u8,69#u8,44#u8,64#u8,86#u8,78#u8,2#u8,247#u8,185#u8,200#u8,34#u8]
theorem c28_length : c28.length = 32 := by simp only [c28,List.length_cons,List.length_nil]
#print axioms c28_length
def c29 : List U8 := [93#u8,148#u8,47#u8,43#u8,56#u8,38#u8,195#u8,2#u8,176#u8,211#u8,233#u8,45#u8,236#u8,253#u8,214#u8,8#u8,150#u8,47#u8,68#u8,71#u8,68#u8,98#u8,207#u8,5#u8,98#u8,12#u8,236#u8,118#u8,7#u8,243#u8,89#u8,94#u8]
theorem c29_length : c29.length = 32 := by simp only [c29,List.length_cons,List.length_nil]
#print axioms c29_length
def c30 : List U8 := [131#u8,36#u8,14#u8,0#u8,59#u8,124#u8,29#u8,92#u8,253#u8,86#u8,152#u8,81#u8,37#u8,144#u8,167#u8,98#u8,190#u8,236#u8,141#u8,67#u8,210#u8,157#u8,215#u8,126#u8,79#u8,75#u8,183#u8,95#u8,219#u8,47#u8,21#u8,93#u8]
theorem c30_length : c30.length = 32 := by simp only [c30,List.length_cons,List.length_nil]
#print axioms c30_length
def c31 : List U8 := [14#u8,91#u8,201#u8,47#u8,233#u8,123#u8,251#u8,29#u8,179#u8,91#u8,79#u8,5#u8,231#u8,68#u8,8#u8,29#u8,90#u8,53#u8,62#u8,4#u8,97#u8,94#u8,71#u8,11#u8,148#u8,127#u8,190#u8,100#u8,124#u8,171#u8,37#u8,2#u8]
theorem c31_length : c31.length = 32 := by simp only [c31,List.length_cons,List.length_nil]
#print axioms c31_length
def c32 : List U8 := [40#u8,225#u8,66#u8,22#u8,122#u8,138#u8,102#u8,84#u8,117#u8,132#u8,95#u8,68#u8,106#u8,92#u8,223#u8,85#u8,251#u8,216#u8,8#u8,112#u8,158#u8,97#u8,196#u8,46#u8,217#u8,188#u8,218#u8,29#u8,117#u8,222#u8,69#u8,6#u8]
theorem c32_length : c32.length = 32 := by simp only [c32,List.length_cons,List.length_nil]
#print axioms c32_length
def c33 : List U8 := [161#u8,137#u8,145#u8,12#u8,92#u8,59#u8,66#u8,113#u8,48#u8,151#u8,29#u8,112#u8,17#u8,79#u8,244#u8,20#u8,44#u8,11#u8,178#u8,16#u8,12#u8,118#u8,72#u8,79#u8,70#u8,112#u8,209#u8,64#u8,205#u8,19#u8,144#u8,69#u8]
theorem c33_length : c33.length = 32 := by simp only [c33,List.length_cons,List.length_nil]
#print axioms c33_length
def c34 : List U8 := [142#u8,120#u8,2#u8,13#u8,163#u8,97#u8,212#u8,45#u8,182#u8,56#u8,134#u8,115#u8,115#u8,171#u8,96#u8,52#u8,108#u8,191#u8,171#u8,27#u8,237#u8,215#u8,20#u8,22#u8,227#u8,106#u8,90#u8,92#u8,99#u8,25#u8,46#u8,23#u8]
theorem c34_length : c34.length = 32 := by simp only [c34,List.length_cons,List.length_nil]
#print axioms c34_length
def c35 : List U8 := [255#u8,239#u8,233#u8,123#u8,93#u8,30#u8,165#u8,36#u8,195#u8,131#u8,173#u8,49#u8,255#u8,237#u8,228#u8,121#u8,159#u8,185#u8,193#u8,51#u8,168#u8,88#u8,123#u8,116#u8,131#u8,201#u8,25#u8,70#u8,31#u8,28#u8,134#u8,19#u8]
theorem c35_length : c35.length = 32 := by simp only [c35,List.length_cons,List.length_nil]
#print axioms c35_length
def c36 : List U8 := [201#u8,168#u8,153#u8,126#u8,245#u8,202#u8,22#u8,23#u8,70#u8,191#u8,146#u8,76#u8,112#u8,2#u8,37#u8,102#u8,167#u8,96#u8,84#u8,71#u8,235#u8,179#u8,31#u8,40#u8,98#u8,51#u8,76#u8,60#u8,69#u8,31#u8,78#u8,81#u8]
theorem c36_length : c36.length = 32 := by simp only [c36,List.length_cons,List.length_nil]
#print axioms c36_length
def c37 : List U8 := [48#u8,82#u8,243#u8,113#u8,116#u8,51#u8,119#u8,14#u8,135#u8,39#u8,81#u8,83#u8,12#u8,101#u8,32#u8,123#u8,147#u8,120#u8,160#u8,12#u8,2#u8,52#u8,2#u8,24#u8,145#u8,134#u8,25#u8,64#u8,152#u8,159#u8,231#u8,17#u8]
theorem c37_length : c37.length = 32 := by simp only [c37,List.length_cons,List.length_nil]
#print axioms c37_length
def c38 : List U8 := [99#u8,60#u8,104#u8,82#u8,117#u8,20#u8,4#u8,10#u8,202#u8,57#u8,118#u8,33#u8,250#u8,145#u8,215#u8,79#u8,243#u8,53#u8,46#u8,88#u8,207#u8,55#u8,237#u8,103#u8,193#u8,41#u8,98#u8,10#u8,184#u8,204#u8,47#u8,86#u8]
theorem c38_length : c38.length = 32 := by simp only [c38,List.length_cons,List.length_nil]
#print axioms c38_length
def c39 : List U8 := [15#u8,58#u8,23#u8,6#u8,1#u8,106#u8,170#u8,125#u8,100#u8,163#u8,50#u8,23#u8,250#u8,101#u8,102#u8,99#u8,47#u8,88#u8,72#u8,71#u8,82#u8,112#u8,165#u8,27#u8,31#u8,33#u8,181#u8,68#u8,79#u8,0#u8,138#u8,26#u8]
theorem c39_length : c39.length = 32 := by simp only [c39,List.length_cons,List.length_nil]
#print axioms c39_length
def c40 : List U8 := [153#u8,91#u8,120#u8,98#u8,68#u8,101#u8,4#u8,64#u8,138#u8,204#u8,53#u8,40#u8,213#u8,187#u8,205#u8,48#u8,36#u8,91#u8,78#u8,33#u8,123#u8,72#u8,3#u8,13#u8,149#u8,63#u8,41#u8,102#u8,135#u8,32#u8,196#u8,85#u8]
theorem c40_length : c40.length = 32 := by simp only [c40,List.length_cons,List.length_nil]
#print axioms c40_length
def c41 : List U8 := [73#u8,101#u8,160#u8,77#u8,47#u8,177#u8,214#u8,8#u8,99#u8,198#u8,18#u8,11#u8,216#u8,73#u8,188#u8,78#u8,175#u8,36#u8,193#u8,89#u8,172#u8,50#u8,65#u8,106#u8,74#u8,70#u8,212#u8,89#u8,27#u8,148#u8,89#u8,126#u8]
theorem c41_length : c41.length = 32 := by simp only [c41,List.length_cons,List.length_nil]
#print axioms c41_length
def c42 : List U8 := [161#u8,114#u8,212#u8,32#u8,99#u8,80#u8,90#u8,124#u8,166#u8,12#u8,96#u8,30#u8,68#u8,51#u8,131#u8,73#u8,235#u8,83#u8,196#u8,96#u8,222#u8,166#u8,10#u8,51#u8,230#u8,23#u8,245#u8,102#u8,14#u8,208#u8,209#u8,125#u8]
theorem c42_length : c42.length = 32 := by simp only [c42,List.length_cons,List.length_nil]
#print axioms c42_length
def c43 : List U8 := [102#u8,115#u8,160#u8,127#u8,14#u8,5#u8,119#u8,65#u8,41#u8,9#u8,181#u8,45#u8,233#u8,184#u8,193#u8,115#u8,89#u8,192#u8,160#u8,8#u8,29#u8,221#u8,58#u8,81#u8,67#u8,178#u8,176#u8,69#u8,75#u8,133#u8,250#u8,67#u8]
theorem c43_length : c43.length = 32 := by simp only [c43,List.length_cons,List.length_nil]
#print axioms c43_length
def c44 : List U8 := [156#u8,53#u8,43#u8,57#u8,64#u8,3#u8,72#u8,79#u8,222#u8,17#u8,112#u8,125#u8,166#u8,47#u8,153#u8,121#u8,21#u8,1#u8,20#u8,36#u8,33#u8,22#u8,139#u8,68#u8,29#u8,243#u8,233#u8,89#u8,28#u8,250#u8,163#u8,96#u8]
theorem c44_length : c44.length = 32 := by simp only [c44,List.length_cons,List.length_nil]
#print axioms c44_length
def c45 : List U8 := [160#u8,0#u8,160#u8,114#u8,33#u8,202#u8,90#u8,103#u8,152#u8,125#u8,30#u8,79#u8,115#u8,11#u8,188#u8,71#u8,211#u8,185#u8,5#u8,97#u8,240#u8,230#u8,159#u8,83#u8,242#u8,197#u8,157#u8,105#u8,171#u8,196#u8,204#u8,72#u8]
theorem c45_length : c45.length = 32 := by simp only [c45,List.length_cons,List.length_nil]
#print axioms c45_length
def c46 : List U8 := [251#u8,103#u8,186#u8,120#u8,231#u8,210#u8,93#u8,89#u8,41#u8,196#u8,76#u8,10#u8,249#u8,92#u8,77#u8,81#u8,118#u8,204#u8,43#u8,89#u8,9#u8,160#u8,170#u8,4#u8,241#u8,112#u8,18#u8,124#u8,50#u8,2#u8,236#u8,117#u8]
theorem c46_length : c46.length = 32 := by simp only [c46,List.length_cons,List.length_nil]
#print axioms c46_length
def c47 : List U8 := [77#u8,27#u8,137#u8,13#u8,138#u8,201#u8,179#u8,72#u8,32#u8,151#u8,212#u8,115#u8,193#u8,156#u8,131#u8,118#u8,2#u8,99#u8,245#u8,72#u8,105#u8,246#u8,106#u8,27#u8,209#u8,75#u8,195#u8,126#u8,216#u8,44#u8,181#u8,12#u8]
theorem c47_length : c47.length = 32 := by simp only [c47,List.length_cons,List.length_nil]
#print axioms c47_length
def c48 : List U8 := [229#u8,253#u8,111#u8,53#u8,26#u8,59#u8,200#u8,78#u8,223#u8,15#u8,0#u8,106#u8,32#u8,144#u8,37#u8,45#u8,14#u8,222#u8,193#u8,94#u8,180#u8,66#u8,148#u8,116#u8,142#u8,74#u8,78#u8,29#u8,129#u8,212#u8,181#u8,112#u8]
theorem c48_length : c48.length = 32 := by simp only [c48,List.length_cons,List.length_nil]
#print axioms c48_length
def c49 : List U8 := [248#u8,176#u8,85#u8,121#u8,113#u8,95#u8,122#u8,32#u8,87#u8,229#u8,192#u8,103#u8,65#u8,156#u8,115#u8,11#u8,78#u8,241#u8,151#u8,2#u8,19#u8,123#u8,233#u8,59#u8,231#u8,36#u8,191#u8,11#u8,224#u8,85#u8,106#u8,2#u8]
theorem c49_length : c49.length = 32 := by simp only [c49,List.length_cons,List.length_nil]
#print axioms c49_length
def c50 : List U8 := [58#u8,67#u8,252#u8,29#u8,121#u8,3#u8,118#u8,103#u8,138#u8,74#u8,199#u8,34#u8,125#u8,148#u8,118#u8,16#u8,92#u8,166#u8,174#u8,34#u8,207#u8,85#u8,225#u8,90#u8,218#u8,230#u8,35#u8,106#u8,108#u8,27#u8,186#u8,74#u8]
theorem c50_length : c50.length = 32 := by simp only [c50,List.length_cons,List.length_nil]
#print axioms c50_length
def c51 : List U8 := [149#u8,36#u8,224#u8,71#u8,225#u8,241#u8,127#u8,49#u8,171#u8,33#u8,229#u8,49#u8,16#u8,223#u8,33#u8,94#u8,44#u8,29#u8,155#u8,58#u8,71#u8,140#u8,221#u8,4#u8,231#u8,147#u8,249#u8,93#u8,57#u8,171#u8,81#u8,99#u8]
theorem c51_length : c51.length = 32 := by simp only [c51,List.length_cons,List.length_nil]
#print axioms c51_length
def c52 : List U8 := [82#u8,60#u8,246#u8,12#u8,140#u8,178#u8,244#u8,105#u8,104#u8,80#u8,245#u8,17#u8,46#u8,117#u8,154#u8,22#u8,44#u8,45#u8,201#u8,108#u8,200#u8,84#u8,167#u8,80#u8,209#u8,207#u8,93#u8,108#u8,135#u8,52#u8,249#u8,13#u8]
theorem c52_length : c52.length = 32 := by simp only [c52,List.length_cons,List.length_nil]
#print axioms c52_length
def c53 : List U8 := [225#u8,71#u8,228#u8,87#u8,1#u8,81#u8,53#u8,16#u8,58#u8,14#u8,213#u8,90#u8,177#u8,248#u8,165#u8,18#u8,231#u8,136#u8,56#u8,116#u8,131#u8,101#u8,183#u8,94#u8,130#u8,208#u8,101#u8,85#u8,96#u8,211#u8,67#u8,53#u8]
theorem c53_length : c53.length = 32 := by simp only [c53,List.length_cons,List.length_nil]
#print axioms c53_length
def c54 : List U8 := [23#u8,7#u8,176#u8,65#u8,47#u8,32#u8,136#u8,15#u8,32#u8,246#u8,96#u8,198#u8,113#u8,134#u8,136#u8,76#u8,14#u8,247#u8,82#u8,65#u8,136#u8,220#u8,116#u8,122#u8,97#u8,205#u8,102#u8,170#u8,156#u8,68#u8,205#u8,19#u8]
theorem c54_length : c54.length = 32 := by simp only [c54,List.length_cons,List.length_nil]
#print axioms c54_length
def c55 : List U8 := [231#u8,251#u8,82#u8,170#u8,25#u8,168#u8,239#u8,199#u8]
theorem c55_length : c55.length = 8 := by simp only [c55,List.length_cons,List.length_nil]
#print axioms c55_length
def bytes : List U8 := (((((c00 ++ (c01 ++ c02)) ++ ((c03 ++ c04) ++ (c05 ++ c06))) ++ ((c07 ++ (c08 ++ c09)) ++ ((c10 ++ c11) ++ (c12 ++ c13)))) ++ (((c14 ++ (c15 ++ c16)) ++ ((c17 ++ c18) ++ (c19 ++ c20))) ++ ((c21 ++ (c22 ++ c23)) ++ ((c24 ++ c25) ++ (c26 ++ c27))))) ++ ((((c28 ++ (c29 ++ c30)) ++ ((c31 ++ c32) ++ (c33 ++ c34))) ++ ((c35 ++ (c36 ++ c37)) ++ ((c38 ++ c39) ++ (c40 ++ c41)))) ++ (((c42 ++ (c43 ++ c44)) ++ ((c45 ++ c46) ++ (c47 ++ c48))) ++ ((c49 ++ (c50 ++ c51)) ++ ((c52 ++ c53) ++ (c54 ++ c55))))))
theorem length : bytes.length = 1768 := by
  simp only [bytes,List.length_append,c00_length,c01_length,c02_length,c03_length,c04_length,c05_length,c06_length,c07_length,c08_length,c09_length,c10_length,c11_length,c12_length,c13_length,c14_length,c15_length,c16_length,c17_length,c18_length,c19_length,c20_length,c21_length,c22_length,c23_length,c24_length,c25_length,c26_length,c27_length,c28_length,c29_length,c30_length,c31_length,c32_length,c33_length,c34_length,c35_length,c36_length,c37_length,c38_length,c39_length,c40_length,c41_length,c42_length,c43_length,c44_length,c45_length,c46_length,c47_length,c48_length,c49_length,c50_length,c51_length,c52_length,c53_length,c54_length,c55_length]
#print axioms length
end AspisR1.NFY_JFx_DataCheckpoint00
-- END copied JFx_DataCheckpoint00
-- BEGIN copied JFx_NativeBytes: lean/JFx_NativeBytes.lean
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFY_JFx_NativeBytes
open Aeneas Aeneas.Std
def proofBytes : List U8 := NFY_JFx_DataProof00.bytes ++ NFY_JFx_DataProof01.bytes ++ NFY_JFx_DataProof02.bytes ++ NFY_JFx_DataProof03.bytes ++ NFY_JFx_DataProof04.bytes ++ NFY_JFx_DataProof05.bytes ++ NFY_JFx_DataProof06.bytes ++ NFY_JFx_DataProof07.bytes ++ NFY_JFx_DataProof08.bytes ++ NFY_JFx_DataProof09.bytes ++ NFY_JFx_DataProof10.bytes ++ NFY_JFx_DataProof11.bytes ++ NFY_JFx_DataProof12.bytes ++ NFY_JFx_DataProof13.bytes ++ NFY_JFx_DataProof14.bytes
theorem proofBytes_length : proofBytes.length = 57607 := by
  simp only [proofBytes,List.length_append,NFY_JFx_DataProof00.length,NFY_JFx_DataProof01.length,NFY_JFx_DataProof02.length,NFY_JFx_DataProof03.length,NFY_JFx_DataProof04.length,NFY_JFx_DataProof05.length,NFY_JFx_DataProof06.length,NFY_JFx_DataProof07.length,NFY_JFx_DataProof08.length,NFY_JFx_DataProof09.length,NFY_JFx_DataProof10.length,NFY_JFx_DataProof11.length,NFY_JFx_DataProof12.length,NFY_JFx_DataProof13.length,NFY_JFx_DataProof14.length]
#print axioms proofBytes_length
def proof : Slice U8 := ⟨proofBytes,by rw [proofBytes_length]; scalar_tac⟩
def publicBytes : List U8 := NFY_JFx_DataPublic00.bytes
theorem publicBytes_length : publicBytes.length = 1880 := by
  simp only [publicBytes,NFY_JFx_DataPublic00.length]
#print axioms publicBytes_length
def publicInput : Slice U8 := ⟨publicBytes,by rw [publicBytes_length]; scalar_tac⟩
def checkpointBytes : List U8 := NFY_JFx_DataCheckpoint00.bytes
theorem checkpointBytes_length : checkpointBytes.length = 1768 := by
  simp only [checkpointBytes,NFY_JFx_DataCheckpoint00.length]
#print axioms checkpointBytes_length
def checkpoint : Slice U8 := ⟨checkpointBytes,by rw [checkpointBytes_length]; scalar_tac⟩
end AspisR1.NFY_JFx_NativeBytes
end
-- END copied JFx_NativeBytes
-- BEGIN copied JFu_PublicHeader: lean/JFu_PublicHeader.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFu_PublicHeader
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder.pool_v1.pair_forest_terminal

theorem length : NFY_JFx_NativeBytes.publicInput.length=1880 := NFY_JFx_NativeBytes.publicBytes_length

theorem first_eight : NFY_JFx_NativeBytes.publicInput.val.take 8 =
    [65#u8,83#u8,70#u8,56#u8,1#u8,1#u8,1#u8,3#u8] := by
  rfl

theorem header :
    NFY_JFx_NativeBytes.publicInput.val.take 4=POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_MAGIC.val ∧
    NFY_JFx_NativeBytes.publicInput.val[4]?=some POOL_V1_PAIR_FOREST_TERMINAL_VERSION ∧
    NFY_JFx_NativeBytes.publicInput.val[5]?=some 1#u8 ∧
    NFY_JFx_NativeBytes.publicInput.val[6]?=some 1#u8 := by
  have p:=first_eight
  refine ⟨?_,?_,?_,?_⟩
  · have h:=congrArg (List.take 4) p
    simpa only [List.take_take,show min 4 8=4 from rfl, List.take_succ_cons,List.take_zero, POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_MAGIC,Array.make] using h
  · have h:=congrArg (fun xs : List U8 => xs[4]?) p
    simpa only [List.getElem?_take_of_lt (by decide : 4<8),List.getElem?_cons_succ,List.getElem?_cons_zero, POOL_V1_PAIR_FOREST_TERMINAL_VERSION] using h
  · have h:=congrArg (fun xs : List U8 => xs[5]?) p
    simpa only [List.getElem?_take_of_lt (by decide : 5<8),List.getElem?_cons_succ,List.getElem?_cons_zero] using h
  · have h:=congrArg (fun xs : List U8 => xs[6]?) p
    simpa only [List.getElem?_take_of_lt (by decide : 6<8),List.getElem?_cons_succ,List.getElem?_cons_zero] using h

#print axioms length
#print axioms first_eight
#print axioms header
end AspisR1.NFY_JFu_PublicHeader
-- END copied JFu_PublicHeader
-- BEGIN copied JFu_PublicRange: lean/JFu_PublicRange.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFu_PublicRange
open Aeneas Aeneas.Std Result WP

def segment (off n : Nat) (bound : off+n≤1880) : Slice U8 :=
  ⟨(NFY_JFx_NativeBytes.publicInput.val.drop off).take n,by
    have h:=NFY_JFx_NativeBytes.publicInput.property
    simp only [List.length_take,List.length_drop]
    omega⟩

theorem length (off n : Nat) (bound : off+n≤1880) : (segment off n bound).length=n := by
  simp only [segment,Slice.length,List.length_take,List.length_drop,NFY_JFx_NativeBytes.publicBytes_length]
  have h : NFY_JFx_NativeBytes.publicInput.val.length=1880 := NFY_JFx_NativeBytes.publicBytes_length
  simp only [h]
  omega

theorem nested {A : Type} (xs : List A) (off n start count : Nat) (bound : start+count≤n) :
    (((xs.drop off).take n).drop start).take count=(xs.drop (off+start)).take count := by
  simp only [List.drop_take,List.drop_drop,List.take_take]
  rw [Nat.min_eq_left (by omega : count≤n-start)]

theorem read (start stop : Usize) (order : start.val≤stop.val) (bound : stop.val≤1880) :
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      NFY_JFx_NativeBytes.publicInput {start:=start,«end»:=stop}=
      ok (segment start.val (stop.val-start.val) (by omega)) := by
  have size : NFY_JFx_NativeBytes.publicInput.val.length=1880 := NFY_JFx_NativeBytes.publicBytes_length
  have spec : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      NFY_JFx_NativeBytes.publicInput {start:=start,«end»:=stop}
      ⦃ out => out=segment start.val (stop.val-start.val) (by omega) ⦄ := by
    unfold core.slice.index.Slice.index
    step*
    all_goals apply Subtype.ext
    all_goals simpa only [segment,List.slice] using out_post1
  obtain ⟨out,call,same⟩:=WP.spec_imp_exists spec
  rw [same] at call
  exact call

def snapshot := segment 176 800 (by decide)
def afterstate := segment 976 688 (by decide)
def late := segment 144 1520 (by decide)
def payment := segment 1664 216 (by decide)

#print axioms length
#print axioms nested
#print axioms read
end AspisR1.NFY_JFu_PublicRange
-- END copied JFu_PublicRange
-- BEGIN copied S6N_Decoder: lean/S6N_Decoder.lean
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.NFY_S6N_Decoder
open AspisS6CurrentCodecInstallation AspisS6CurrentAdapterCarrier
open AspisS6OuterNativeOps

/-- Complete wrapper Result, including decoder rejection, fail and divergence.
Safe Box introduction/moves use the existing D188 standard model. -/
theorem complete (bytes : Slice U8) :
    decode bytes = (do
      let reply ← rawDecoder bytes
      match reply with
      | .Ok value => ok (.Ok value)
      | .Err _ => ok (.Err AdapterRw.solana_program_error.ProgramError.InvalidAccountData)) :=
  boxed_eq boxOps bytes

/-- A continuation consumes exactly the returned owned value or exact error. -/
theorem contextual {A : Type} (bytes : Slice U8)
    (next : core.result.Result Statement PE → Result A) :
    (do let value ← decode bytes; next value) =
    (do
      let reply ← rawDecoder bytes
      match reply with
      | .Ok value => next (.Ok value)
      | .Err _ => next (.Err AdapterRw.solana_program_error.ProgramError.InvalidAccountData)) := by
  rw [complete]
  cases rawDecoder bytes with
  | fail e => rfl
  | div => rfl
  | ok r => cases r <;> rfl

/-- Native caller acceptance identifies the decoder value, rather than
postulating an independently successful decoder on the same bytes. -/
theorem accepted_content (bytes : Slice U8) (statement : Statement)
    (accepted : decode bytes = ok (.Ok statement)) :
    AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_statement_v1 bytes =
      ok (.Ok (toPoolV1PairForestTerminalStatementV1 statement)) :=
  decode_success bytes statement accepted

/-- The wrapper cannot manufacture success on decoder rejection. -/
theorem error (bytes : Slice U8) (e : FormatError)
    (rejected : rawDecoder bytes = ok (.Err e)) :
    decode bytes = ok (.Err AdapterRw.solana_program_error.ProgramError.InvalidAccountData) := by
  rw [complete, rejected]
  rfl

#print axioms complete
#print axioms contextual
#print axioms accepted_content
#print axioms error
end AspisR1.NFY_S6N_Decoder
-- END copied S6N_Decoder
-- BEGIN copied S6N_Getters: lean/S6N_Getters.lean
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.NFY_S6N_Getters
open AdapterRw.aspis_statement.pool_v1
abbrev Statement := pair_forest_terminal.PoolV1PairForestTerminalStatementV1
abbrev Common := pair_forest_terminal.PoolV1PairForestTerminalCommonV1
abbrev Public := pair_forest_semantic_terminal.r0.Public

def commonValue : Statement → Common
  | .PrivateTransfer common _ => common
  | .Withdrawal common _ => common

def publicValue : Statement → Public
  | .PrivateTransfer common pub => .Transfer pub common.lane_transition
  | .Withdrawal common pub => .Withdrawal pub common.lane_transition

/-- The complete extracted getters are total field projections on both enum
variants. No validator, decoder success or canonicality premise is used. -/
theorem complete (statement : Statement) :
    pair_forest_terminal.PoolV1PairForestTerminalStatementV1.common statement = ok (commonValue statement) ∧
    pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public statement = ok (publicValue statement) := by
  cases statement <;> exact ⟨rfl,rfl⟩

/-- Arbitrary continuations retain the same statement and selected public
fields. This is the Aeneas value/borrow model; native pointer checks are separate. -/
theorem contextual {A : Type} (statement : Statement)
    (tail : Common → Public → Statement → Result A) :
    (do let common ← pair_forest_terminal.PoolV1PairForestTerminalStatementV1.common statement
        let pub ← pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public statement
        tail common pub statement) =
      tail (commonValue statement) (publicValue statement) statement := by
  rw [(complete statement).1,(complete statement).2]
  rfl

/-- The source semantic projection is exactly the public carrier consumed by
S6 and Claims. The same statement is retained across the conversion. -/
theorem selected (statement : Statement) :
    AspisS6CurrentVerifierCarrier.toPublic (publicValue statement) =
      AspisR1CurrentCaller.FirstComposition.toCurrentPublic
        (AspisR1PublicPreparation.PreparationBinding.preparationPublic
          (AspisS6CurrentAdapterCarrier.toPoolV1PairForestTerminalStatementV1 statement)) := by
  cases statement <;> rfl

#print axioms complete
#print axioms contextual
#print axioms selected
end AspisR1.NFY_S6N_Getters
-- END copied S6N_Getters
-- BEGIN copied S6N_Installation: lean/S6N_Installation.lean
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.NFY_S6N_Installation
open AspisS6CurrentCodecInstallation

/-- Value-level deployment certificate for the actual selected SDK. Native
safe ownership/cleanup is interpreted under D188, with source pins and native
checks in the S6N receipt packet; it is not a new hypothesis of deployed. -/
structure Facts (ops : AdapterRw.Ops) : Prop where
  installed : ops.op47 = decode
  complete : ∀ bytes, ops.op47 bytes = (do
    let reply ← rawDecoder bytes
    match reply with
    | .Ok value => ok (.Ok value)
    | .Err _ => ok (.Err AdapterRw.solana_program_error.ProgramError.InvalidAccountData))
  total : ∀ bytes, ∃ result, ops.op47 bytes = ok result
  getters : ∀ statement : NFY_S6N_Getters.Statement,
    AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.common statement =
      ok (NFY_S6N_Getters.commonValue statement) ∧
    AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public statement =
      ok (NFY_S6N_Getters.publicValue statement)

/-- Every installed configuration uses the concrete decoder. The free adapter
record does not supply a native/public equality or decoder success premise. -/
theorem facts {F E : Type} (c : DrvC_Installation.Configuration F E) :
    Facts (DrvC_Installation.sdk c) := by
  refine ⟨rfl,?_,?_,NFY_S6N_Getters.complete⟩
  · exact NFY_S6N_Decoder.complete
  · exact AspisS6CurrentCodecInstallation.decode_total

/-- Applies to the actual source-selected cut statement, preserving the same
public bytes and successful output. No independent decoder witness is chosen. -/
theorem accepted {F E : Type} (c : DrvC_Installation.Configuration F E)
    (bytes : Slice U8) (statement : Statement)
    (run : (DrvC_Installation.sdk c).op47 bytes = ok (.Ok statement)) :
    AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_statement_v1 bytes =
      ok (.Ok (AspisS6CurrentAdapterCarrier.toPoolV1PairForestTerminalStatementV1 statement)) ∧
    AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public statement =
      ok (NFY_S6N_Getters.publicValue statement) := by
  rw [(facts c).installed] at run
  exact ⟨NFY_S6N_Decoder.accepted_content bytes statement run,(NFY_S6N_Getters.complete statement).2⟩

#print axioms facts
#print axioms accepted
end AspisR1.NFY_S6N_Installation
end
-- END copied S6N_Installation
-- BEGIN copied JFv_M31: lean/JFv_M31.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFv_M31
open Aeneas Aeneas.Std Result
open AspisR1DecodeKFullV10

theorem success (bytes : Array U8 4#usize)
    (canonical : (core.num.U32.from_le_bytes bytes).val < 2147483647) :
    aspis_core.field.M31.from_le_bytes bytes = ok (some (core.num.U32.from_le_bytes bytes)) := by
  unfold aspis_core.field.M31.from_le_bytes
  simp only [lift,bind_tc_ok]
  rw [if_neg (by unfold aspis_core.field.P; change ¬ (2147483647:Nat) ≤ (core.num.U32.from_le_bytes bytes).val;omega)]

#print axioms success
end AspisR1.NFY_JFv_M31
-- END copied JFv_M31
-- BEGIN copied JFv_CM31: lean/JFv_CM31.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFv_CM31
open Aeneas Aeneas.Std Result
open AspisR1DecodeKFullV10
open CandidateCM31Parser

theorem success (arr : Array U8 8#usize)
    (h0 : (core.num.U32.from_le_bytes (half0 arr)).val < 2147483647)
    (h1 : (core.num.U32.from_le_bytes (half1 arr)).val < 2147483647) :
    aspis_core.field.CM31.from_le_bytes (Array.to_slice arr) =
      ok (some ⟨core.num.U32.from_le_bytes (half0 arr),core.num.U32.from_le_bytes (half1 arr)⟩) := by
  have s0 := ParserArraySlice.slice_segment arr 0#usize 4#usize (by decide) 4#usize (by decide)
  have s1 := ParserArraySlice.slice_segment arr 4#usize 4#usize (by decide) 8#usize (by decide)
  change _ = ok (Array.to_slice (half0 arr)) at s0
  change _ = ok (Array.to_slice (half1 arr)) at s1
  have p0 := NFY_JFv_M31.success (half0 arr) h0
  have p1 := NFY_JFv_M31.success (half1 arr) h1
  simp only [aspis_core.field.CM31.from_le_bytes,s0,s1,
    AspisV8R19.SamplerWordRead.conversion_success,p0,p1,bind_tc_ok,
    core.option.Option.Insts.CoreOpsTry_traitTry.branch]

#print axioms success
end AspisR1.NFY_JFv_CM31
-- END copied JFv_CM31
-- BEGIN copied JFv_QM31: lean/JFv_QM31.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFv_QM31
open Aeneas Aeneas.Std Result
open AspisR1DecodeKFullV10

def word (arr : Array U8 16#usize) (high low : Bool) : Array U8 4#usize :=
  let half := if high then CandidateQM31Parser.half1 arr else CandidateQM31Parser.half0 arr
  if low then CandidateCM31Parser.half1 half else CandidateCM31Parser.half0 half

def value (arr : Array U8 16#usize) : aspis_core.field.QM31 :=
  ⟨⟨core.num.U32.from_le_bytes (word arr false false),core.num.U32.from_le_bytes (word arr false true)⟩,
   ⟨core.num.U32.from_le_bytes (word arr true false),core.num.U32.from_le_bytes (word arr true true)⟩⟩

theorem success (arr : Array U8 16#usize)
    (canonical : ∀ high low,(core.num.U32.from_le_bytes (word arr high low)).val < 2147483647) :
    aspis_core.field.QM31.from_le_bytes (Array.to_slice arr)=ok (some (value arr)) := by
  have s0 := ParserArraySlice.slice_segment arr 0#usize 8#usize (by decide) 8#usize (by decide)
  have s1 := ParserArraySlice.slice_segment arr 8#usize 8#usize (by decide) 16#usize (by decide)
  change _ = ok (Array.to_slice (CandidateQM31Parser.half0 arr)) at s0
  change _ = ok (Array.to_slice (CandidateQM31Parser.half1 arr)) at s1
  have p0 := NFY_JFv_CM31.success (CandidateQM31Parser.half0 arr) (canonical false false) (canonical false true)
  have p1 := NFY_JFv_CM31.success (CandidateQM31Parser.half1 arr) (canonical true false) (canonical true true)
  simp only [aspis_core.field.QM31.from_le_bytes,s0,s1,p0,p1,bind_tc_ok,
    core.option.Option.Insts.CoreOpsTry_traitTry.branch]
  rfl

#print axioms success
end AspisR1.NFY_JFv_QM31
-- END copied JFv_QM31
-- BEGIN copied JFv_WordCanonical: lean/JFv_WordCanonical.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFv_WordCanonical
open Aeneas Aeneas.Std Result
open OraclePortCompactDraft MultiproofConeCanonical

theorem bytes (arr : Array U8 4#usize) :
    List.ofFn (M31ParserArray.arrayBytes arr) = bytesOf arr.val := by
  apply List.ext_getElem
  · simp only [List.length_ofFn,bytesOf,List.length_map,arr.property,show (4#usize).val=4 from rfl]
  · intro i hi hj
    simp only [List.getElem_ofFn,M31ParserArray.arrayBytes,bytesOf,List.getElem_map]

theorem bound (arr : Array U8 4#usize) (canonical : canonical (bytesOf arr.val)) :
    (core.num.U32.from_le_bytes arr).val < 2147483647 := by
  rw [MultiproofConeEndian.strict_word_iff,←MultiproofConeEndian.little_four,bytes]
  have h := canonical.2 0 (by simp only [List.mem_range,bytesOf,List.length_map,arr.property];decide)
  have len : (bytesOf arr.val).length ≤ 4 := by
    simp only [bytesOf,List.length_map,arr.property];decide
  simpa only [slice,Nat.mul_zero,List.drop_zero,List.take_of_length_le len] using h

#print axioms bytes
#print axioms bound
end AspisR1.NFY_JFv_WordCanonical
-- END copied JFv_WordCanonical
-- BEGIN copied JFv_CanonicalSlice: lean/JFv_CanonicalSlice.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFv_CanonicalSlice
open Aeneas Aeneas.Std Result
open OraclePortCompactDraft MultiproofConeCanonical MultiproofConeCanonicalAppend

theorem selected (b : AspisV8R19.DuplexFrames.Bytes) (off n : Nat)
    (a : off%4=0) (z : n%4=0) (fits : off+n ≤ b.length)
    (canon : canonical b) : canonical (slice b off n) := by
  have tail := ((canonical_take_drop b off a (by omega)).mp canon).2
  have first := ((canonical_take_drop (b.drop off) n z (by rw [List.length_drop];omega)).mp tail).1
  exact first

theorem word (arr : Array U8 16#usize) (high low : Bool) :
    (NFY_JFv_QM31.word arr high low).val =
      (arr.val.drop ((if high then 8 else 0)+(if low then 4 else 0))).take 4 := by
  cases high <;> cases low <;>
    simp [NFY_JFv_QM31.word,CandidateCM31Parser.half0,CandidateCM31Parser.half1,
      CandidateQM31Parser.half0,CandidateQM31Parser.half1,ParserArraySlice.segment,
      List.drop_take,List.drop_drop,List.take_take]

theorem bounds (arr : Array U8 16#usize) (canon : canonical (bytesOf arr.val)) :
    ∀ high low,(core.num.U32.from_le_bytes (NFY_JFv_QM31.word arr high low)).val < 2147483647 := by
  intro high low
  apply NFY_JFv_WordCanonical.bound
  rw [word]
  simp only [bytesOf,List.map_take,List.map_drop]
  apply selected (bytesOf arr.val) _ 4
  · cases high <;> cases low <;> decide
  · decide
  · simp only [bytesOf,List.length_map,arr.property]
    cases high <;> cases low <;> decide
  · exact canon

#print axioms selected
#print axioms word
#print axioms bounds
end AspisR1.NFY_JFv_CanonicalSlice
-- END copied JFv_CanonicalSlice
-- BEGIN copied JFv_Consecutive: lean/JFv_Consecutive.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFv_Consecutive

theorem slice {α : Type} (xs : List α) (start n : Nat) (bound : start+n ≤ xs.length) :
    List.ofFn (fun i : Fin n => xs[start+i.val]'(by omega)) = (xs.drop start).take n := by
  apply List.ext_getElem
  · simp only [List.length_ofFn,List.length_take,List.length_drop]
    omega
  · intro i hi hj
    simp only [List.getElem_ofFn,List.getElem_take,List.getElem_drop]

#print axioms slice
end AspisR1.NFY_JFv_Consecutive
-- END copied JFv_Consecutive
-- BEGIN copied JFv_SelectedBytes: lean/JFv_SelectedBytes.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFv_SelectedBytes
open Aeneas Aeneas.Std Result
open MultiproofConeCanonical OraclePortCompactDraft

theorem equality (input output : Slice U8) (start n : Nat) (length : output.length=n)
    (bound : start+n ≤ input.length)
    (same : ∀ j : Nat, (h : j<n) → output.val[j]'(by change output.val.length=n at length;omega) =
      input.val[start+j]'(by change start+n ≤ input.val.length at bound;omega)) :
    output.val=(input.val.drop start).take n := by
  apply List.ext_getElem
  · change output.val.length=n at length
    change start+n ≤ input.val.length at bound
    simp only [List.length_take,List.length_drop,length]
    omega
  · intro j hi hj
    rw [List.getElem_take,List.getElem_drop]
    exact same j (by change output.val.length=n at length;omega)

theorem canonical_slice (input output : Slice U8) (start n : Nat) (length : output.length=n)
    (bound : start+n ≤ input.length) (a : start%4=0) (z : n%4=0)
    (canon : OraclePortCompactDraft.canonical (bytesOf input.val))
    (same : ∀ j : Nat, (h : j<n) → output.val[j]'(by change output.val.length=n at length;omega) =
      input.val[start+j]'(by change start+n ≤ input.val.length at bound;omega)) :
    OraclePortCompactDraft.canonical (bytesOf output.val) := by
  rw [equality input output start n length bound same]
  simp only [bytesOf,List.map_take,List.map_drop]
  exact NFY_JFv_CanonicalSlice.selected (bytesOf input.val) start n a z
    (by simpa only [bytesOf,List.length_map] using bound) canon

#print axioms equality
#print axioms canonical_slice
end AspisR1.NFY_JFv_SelectedBytes
-- END copied JFv_SelectedBytes
-- BEGIN copied JFu_DigestDecode: lean/JFu_DigestDecode.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFu_DigestDecode
open Aeneas Aeneas.Std Result WP
open AspisR1TerminalDecoder
open OraclePortCompactDraft MultiproofConeCanonical

@[local step] theorem word (arr : Array U8 4#usize) (canon : canonical (bytesOf arr.val)) :
    aspis_core.field.M31.from_le_bytes arr
      ⦃ out => out=some (core.num.U32.from_le_bytes arr) ⦄ := by
  have bound:=NFY_JFv_WordCanonical.bound arr canon
  apply exists_imp_spec
  refine ⟨some (core.num.U32.from_le_bytes arr),?_,rfl⟩
  unfold aspis_core.field.M31.from_le_bytes
  simp only [lift,bind_tc_ok]
  have small : ¬(core.num.U32.from_le_bytes arr) ≥ aspis_core.field.P := by
    unfold aspis_core.field.P
    scalar_tac
  simp only [if_neg small]

@[local step] theorem option {T E : Type} (o : Option T) (e : E) :
    core.option.Option.ok_or o e
      ⦃ out => out=(match o with | some v => .Ok v | none => .Err e) ⦄ := by
  apply exists_imp_spec
  cases o <;> exact ⟨_,rfl,rfl⟩

theorem chunk (arr : Array U8 32#usize) (canon : canonical (bytesOf arr.val))
    (k : Nat) (hk : k<8) :
    canonical (bytesOf [arr.val[4*k]'(by simp only [arr.property,show (32#usize).val=32 from rfl];omega),
      arr.val[4*k+1]'(by simp only [arr.property,show (32#usize).val=32 from rfl];omega),
      arr.val[4*k+2]'(by simp only [arr.property,show (32#usize).val=32 from rfl];omega),
      arr.val[4*k+3]'(by simp only [arr.property,show (32#usize).val=32 from rfl];omega)]) := by
  let out : Slice U8 := ⟨[arr.val[4*k]'(by simp only [arr.property,show (32#usize).val=32 from rfl];omega),
      arr.val[4*k+1]'(by simp only [arr.property,show (32#usize).val=32 from rfl];omega),
      arr.val[4*k+2]'(by simp only [arr.property,show (32#usize).val=32 from rfl];omega),
      arr.val[4*k+3]'(by simp only [arr.property,show (32#usize).val=32 from rfl];omega)],by simp;scalar_tac⟩
  apply NFY_JFv_SelectedBytes.canonical_slice (Array.to_slice arr) out (4*k) 4 rfl
    (by simp only [Array.to_slice,Slice.length,arr.property,show (32#usize).val=32 from rfl];omega) (by omega) (by decide) canon
  intro j hj
  interval_cases j <;> simp only [out,Array.to_slice,List.getElem_cons_succ,List.getElem_cons_zero,Nat.add_zero]

/-- Only eight scalar word decodes; no whole public decoder reduction. -/
theorem success (arr : Array U8 32#usize) (canon : canonical (bytesOf arr.val)) :
    ∃ out,atomic_statement.decode_digest_canonical arr=ok (.Ok out) := by
  have spec : atomic_statement.decode_digest_canonical arr ⦃ out => ∃ q,out=.Ok q ⦄ := by
    unfold atomic_statement.decode_digest_canonical
    step*
    case canon =>
      simpa only [Array.make,i_post,i1_post,i2_post,i3_post] using chunk arr canon 0 (by decide)
    case canon =>
      simpa only [Array.make,i4_post,i5_post,i6_post,i7_post] using chunk arr canon 1 (by decide)
    case canon =>
      simpa only [Array.make,i8_post,i9_post,i10_post,i11_post] using chunk arr canon 2 (by decide)
    case canon =>
      simpa only [Array.make,i12_post,i13_post,i14_post,i15_post] using chunk arr canon 3 (by decide)
    case canon =>
      simpa only [Array.make,i16_post,i17_post,i18_post,i19_post] using chunk arr canon 4 (by decide)
    case canon =>
      simpa only [Array.make,i20_post,i21_post,i22_post,i23_post] using chunk arr canon 5 (by decide)
    case canon =>
      simpa only [Array.make,i24_post,i25_post,i26_post,i27_post] using chunk arr canon 6 (by decide)
    case canon =>
      simpa only [Array.make,i28_post,i29_post,i30_post,i31_post] using chunk arr canon 7 (by decide)
    all_goals simp_all [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
    all_goals exact ⟨_,rfl⟩
  obtain ⟨out,call,q,same⟩:=WP.spec_imp_exists spec
  exact ⟨q,by rw [same] at call;exact call⟩

#print axioms word
#print axioms option
#print axioms chunk
#print axioms success
end AspisR1.NFY_JFu_DigestDecode
-- END copied JFu_DigestDecode
-- BEGIN copied JFu_DigestSlice: lean/JFu_DigestSlice.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFu_DigestSlice
open Aeneas Aeneas.Std Result WP
open AspisR1TerminalDecoder
open OraclePortCompactDraft MultiproofConeCanonical

@[local step] theorem digest (arr : Array U8 32#usize) (canon : canonical (bytesOf arr.val)) :
    atomic_statement.decode_digest_canonical arr ⦃ out => ∃ q,out=.Ok q ⦄ := by
  obtain ⟨q,call⟩:=NFY_JFu_DigestDecode.success arr canon
  rw [call,WP.spec_ok]
  exact ⟨q,rfl⟩

theorem success (bytes : Slice U8) (size : bytes.length=32)
    (canon : canonical (bytesOf bytes.val)) :
    ∃ out,AspisS6NativeSnapshotReadDigest.read_digest bytes=ok (.Ok out) := by
  have spec : AspisS6NativeSnapshotReadDigest.read_digest bytes ⦃ out => ∃ q,out=.Ok q ⦄ := by
    unfold AspisS6NativeSnapshotReadDigest.read_digest
    step*
    cases converted with
    | Err e => simp only at converted_post;exact False.elim (converted_post size)
    | Ok arr =>
      simp only at converted_post
      simp only [atomic_statement.unwrap_fixed_slice,bind_tc_ok]
      exact digest arr (by rw [converted_post.1];exact canon)
  obtain ⟨out,call,q,same⟩:=WP.spec_imp_exists spec
  exact ⟨q,by rw [same] at call;exact call⟩

#print axioms digest
#print axioms success
#print core.array.TryFromSharedArraySlice.try_from
end AspisR1.NFY_JFu_DigestSlice
-- END copied JFu_DigestSlice

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
