import JHm_BlockWindows
import NDO_JFu_DecodeAt
import NDO_JGi_FieldWindows
import NDO_JGe_Decode26
set_option autoImplicit false
namespace AspisR1.JHm_Row26Windows
open Aeneas Aeneas.Std Result
attribute [local irreducible] JFx_NativeBytes.proof JFx_NativeBytes.proofBytes
def b00 : List U8 := [131#u8,211#u8,253#u8,58#u8,3#u8,204#u8,2#u8,71#u8,226#u8,38#u8,90#u8,29#u8,226#u8,132#u8,203#u8,25#u8]
def b01 : List U8 := [170#u8,170#u8,175#u8,125#u8,58#u8,8#u8,72#u8,36#u8,11#u8,203#u8,72#u8,19#u8,213#u8,115#u8,71#u8,120#u8]
def b02 : List U8 := [92#u8,225#u8,10#u8,81#u8,218#u8,1#u8,95#u8,0#u8,248#u8,200#u8,240#u8,46#u8,5#u8,48#u8,230#u8,40#u8]
def b03 : List U8 := [40#u8,171#u8,211#u8,20#u8,197#u8,210#u8,201#u8,83#u8,78#u8,89#u8,250#u8,127#u8,202#u8,169#u8,245#u8,85#u8]
def b04 : List U8 := [15#u8,126#u8,33#u8,76#u8,85#u8,208#u8,214#u8,68#u8,155#u8,15#u8,48#u8,63#u8,247#u8,11#u8,203#u8,118#u8]
def b05 : List U8 := [158#u8,213#u8,193#u8,32#u8,18#u8,210#u8,221#u8,19#u8,224#u8,225#u8,53#u8,16#u8,79#u8,40#u8,235#u8,79#u8]
def b06 : List U8 := [223#u8,249#u8,248#u8,92#u8,210#u8,229#u8,185#u8,28#u8,77#u8,224#u8,10#u8,39#u8,196#u8,120#u8,113#u8,22#u8]
def b07 : List U8 := [36#u8,12#u8,98#u8,52#u8,209#u8,213#u8,123#u8,68#u8,248#u8,185#u8,8#u8,64#u8,185#u8,39#u8,244#u8,27#u8]
def b08 : List U8 := [30#u8,150#u8,43#u8,111#u8,239#u8,72#u8,196#u8,12#u8,74#u8,207#u8,38#u8,62#u8,25#u8,175#u8,110#u8,34#u8]
def b09 : List U8 := [5#u8,35#u8,78#u8,88#u8,9#u8,202#u8,31#u8,127#u8,134#u8,154#u8,13#u8,28#u8,243#u8,210#u8,241#u8,116#u8]
def b10 : List U8 := [48#u8,124#u8,105#u8,72#u8,191#u8,241#u8,38#u8,27#u8,228#u8,122#u8,13#u8,78#u8,126#u8,49#u8,250#u8,59#u8]
def b11 : List U8 := [67#u8,141#u8,217#u8,76#u8,38#u8,136#u8,132#u8,18#u8,55#u8,58#u8,228#u8,63#u8,230#u8,70#u8,199#u8,108#u8]
def b12 : List U8 := [195#u8,48#u8,79#u8,41#u8,11#u8,56#u8,116#u8,24#u8,76#u8,47#u8,107#u8,72#u8,142#u8,149#u8,6#u8,121#u8]
def b13 : List U8 := [179#u8,228#u8,57#u8,54#u8,131#u8,130#u8,40#u8,118#u8,33#u8,252#u8,79#u8,11#u8,212#u8,153#u8,152#u8,15#u8]
def b14 : List U8 := [160#u8,1#u8,242#u8,4#u8,106#u8,52#u8,176#u8,106#u8,56#u8,126#u8,19#u8,62#u8,87#u8,211#u8,240#u8,59#u8]
def b15 : List U8 := [34#u8,104#u8,97#u8,72#u8,75#u8,135#u8,131#u8,15#u8,21#u8,157#u8,31#u8,93#u8,47#u8,160#u8,207#u8,65#u8]
def b16 : List U8 := [26#u8,9#u8,28#u8,57#u8,98#u8,155#u8,203#u8,126#u8,208#u8,128#u8,23#u8,31#u8,220#u8,65#u8,144#u8,24#u8]
def b17 : List U8 := [208#u8,135#u8,145#u8,126#u8,29#u8,43#u8,148#u8,63#u8,160#u8,132#u8,220#u8,83#u8,82#u8,203#u8,87#u8,105#u8]
def b18 : List U8 := [61#u8,23#u8,156#u8,4#u8,211#u8,35#u8,222#u8,117#u8,182#u8,69#u8,140#u8,7#u8,162#u8,200#u8,165#u8,105#u8]
def b19 : List U8 := [235#u8,113#u8,240#u8,5#u8,57#u8,119#u8,245#u8,122#u8,194#u8,187#u8,100#u8,75#u8,162#u8,33#u8,211#u8,8#u8]
def b20 : List U8 := [143#u8,29#u8,71#u8,31#u8,156#u8,249#u8,48#u8,73#u8,252#u8,84#u8,85#u8,104#u8,136#u8,5#u8,85#u8,87#u8]
def b21 : List U8 := [99#u8,223#u8,121#u8,0#u8,171#u8,91#u8,189#u8,93#u8,207#u8,51#u8,182#u8,124#u8,220#u8,21#u8,163#u8,112#u8]
def b22 : List U8 := [50#u8,76#u8,184#u8,114#u8,70#u8,100#u8,80#u8,69#u8,154#u8,224#u8,31#u8,91#u8,97#u8,84#u8,233#u8,87#u8]
def b23 : List U8 := [129#u8,173#u8,173#u8,38#u8,45#u8,251#u8,178#u8,117#u8,54#u8,151#u8,157#u8,105#u8,14#u8,251#u8,2#u8,2#u8]
def b24 : List U8 := [103#u8,123#u8,145#u8,36#u8,5#u8,72#u8,101#u8,122#u8,59#u8,28#u8,17#u8,63#u8,80#u8,79#u8,71#u8,57#u8]
def b25 : List U8 := [153#u8,224#u8,245#u8,47#u8,152#u8,65#u8,45#u8,90#u8,25#u8,66#u8,194#u8,67#u8,245#u8,183#u8,24#u8,22#u8]
def b26 : List U8 := [110#u8,96#u8,214#u8,78#u8,228#u8,174#u8,129#u8,21#u8,124#u8,153#u8,68#u8,111#u8,119#u8,101#u8,196#u8,50#u8]
def b27 : List U8 := [227#u8,192#u8,61#u8,33#u8,60#u8,130#u8,195#u8,20#u8,128#u8,242#u8,20#u8,122#u8,109#u8,77#u8,139#u8,67#u8]
def b28 : List U8 := [20#u8,219#u8,131#u8,59#u8,7#u8,248#u8,46#u8,12#u8,21#u8,184#u8,131#u8,5#u8,120#u8,4#u8,47#u8,103#u8]
def chunks : List (List U8) := [b00++List.replicate 16 0#u8,b01++List.replicate 16 0#u8,b02++List.replicate 16 0#u8,b03++List.replicate 16 0#u8,b04++List.replicate 16 0#u8,b05++List.replicate 16 0#u8,b06++List.replicate 16 0#u8,b07++List.replicate 16 0#u8,b08++List.replicate 16 0#u8,b09++List.replicate 16 0#u8,b10++List.replicate 16 0#u8,b11++List.replicate 16 0#u8,b12++List.replicate 16 0#u8,b13++List.replicate 16 0#u8,b14++List.replicate 16 0#u8,b15++List.replicate 16 0#u8,b16++List.replicate 16 0#u8,b17++List.replicate 16 0#u8,b18++List.replicate 16 0#u8,b19++List.replicate 16 0#u8,b20++List.replicate 16 0#u8,b21++List.replicate 16 0#u8,b22++List.replicate 16 0#u8,b23++List.replicate 16 0#u8,b24++List.replicate 16 0#u8,b25++List.replicate 16 0#u8,b26++List.replicate 16 0#u8,b27++List.replicate 16 0#u8,b28++List.replicate 16 0#u8]
theorem lengths : ∀ c∈chunks,c.length=32 := by
  intro c hc
  simp only [chunks,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27|h28
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
#print axioms lengths
theorem selected (j : Fin 29) :
    ((JFu_Q26Source.record.framed.val.drop 5).drop (32*j.val)).take 16=
      ((JFw_Frames.window 6567 464).val.drop (16*j.val)).take 16 := by
  change ((JFw_Blocks.blocks 29 (JFw_Frames.window 6567 464).val).flatten.drop (32*j.val)).take 16=_
  have len : (JFw_Frames.window 6567 464).val.length=16*29 := by
    rw [show (JFw_Frames.window 6567 464).val.length=464 from JFw_Frames.window_length 6567 464 (by decide)]
  exact JHm_BlockWindows.source 29 (JFw_Frames.window 6567 464).val len j.val j.isLt
#print axioms selected
end AspisR1.JHm_Row26Windows
