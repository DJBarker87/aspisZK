import JFz_Canonical
import JFx_NativeBytes
import MultiproofConeCanonicalAppend
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_Scan00
open Aeneas Aeneas.Std
open AspisV8R19.DuplexFrames OraclePortCompactDraft MultiproofConeCanonical
def b00 : List U8 := [34#u8,194#u8,187#u8,46#u8,77#u8,91#u8,113#u8,104#u8,129#u8,133#u8,219#u8,40#u8,197#u8,161#u8,69#u8,71#u8,72#u8,132#u8,161#u8,5#u8,145#u8,155#u8,80#u8,48#u8,181#u8,166#u8,23#u8,94#u8,46#u8,11#u8,39#u8,116#u8]
theorem b00_length : b00.length = 32 := by simp only [b00,List.length_cons,List.length_nil]
theorem b00_canonical : canonical (bytesOf b00) := by
  change canonical [34,194,187,46,77,91,113,104,129,133,219,40,197,161,69,71,72,132,161,5,145,155,80,48,181,166,23,94,46,11,39,116]
  simp only [canonical_four]
  exact ⟨by decide, ⟨by decide, ⟨by decide, ⟨by decide, ⟨by decide, ⟨by decide, ⟨by decide, ⟨by decide, JFz_Canonical.nil⟩⟩⟩⟩⟩⟩⟩⟩
#print axioms b00_canonical
#print axioms b00_length
def b01 : List U8 := [148#u8,62#u8,130#u8,121#u8,55#u8,9#u8,143#u8,40#u8,145#u8,201#u8,103#u8,29#u8,96#u8,88#u8,145#u8,24#u8,130#u8,91#u8,96#u8,22#u8,222#u8,172#u8,0#u8,56#u8,249#u8,244#u8,137#u8,42#u8,169#u8,229#u8,6#u8,67#u8]
theorem b01_length : b01.length = 32 := by simp only [b01,List.length_cons,List.length_nil]
theorem b01_canonical : canonical (bytesOf b01) := by
  change canonical [148,62,130,121,55,9,143,40,145,201,103,29,96,88,145,24,130,91,96,22,222,172,0,56,249,244,137,42,169,229,6,67]
  simp only [canonical_four]
  exact ⟨by decide, ⟨by decide, ⟨by decide, ⟨by decide, ⟨by decide, ⟨by decide, ⟨by decide, ⟨by decide, JFz_Canonical.nil⟩⟩⟩⟩⟩⟩⟩⟩
#print axioms b01_canonical
#print axioms b01_length
def b02 : List U8 := [23#u8,160#u8,4#u8,126#u8,44#u8,204#u8,162#u8,18#u8,248#u8,86#u8,90#u8,108#u8,219#u8,182#u8,34#u8,114#u8,225#u8,36#u8,87#u8,53#u8,174#u8,189#u8,128#u8,106#u8,7#u8,123#u8,178#u8,91#u8,109#u8,253#u8,228#u8,33#u8]
theorem b02_length : b02.length = 32 := by simp only [b02,List.length_cons,List.length_nil]
theorem b02_canonical : canonical (bytesOf b02) := by
  change canonical [23,160,4,126,44,204,162,18,248,86,90,108,219,182,34,114,225,36,87,53,174,189,128,106,7,123,178,91,109,253,228,33]
  simp only [canonical_four]
  exact ⟨by decide, ⟨by decide, ⟨by decide, ⟨by decide, ⟨by decide, ⟨by decide, ⟨by decide, ⟨by decide, JFz_Canonical.nil⟩⟩⟩⟩⟩⟩⟩⟩
#print axioms b02_canonical
#print axioms b02_length
def b03 : List U8 := [221#u8,137#u8,3#u8,66#u8,212#u8,39#u8,192#u8,8#u8,250#u8,231#u8,100#u8,36#u8,11#u8,45#u8,15#u8,0#u8,213#u8,61#u8,44#u8,75#u8,85#u8,38#u8,92#u8,14#u8,39#u8,71#u8,243#u8,61#u8,158#u8,121#u8,109#u8,18#u8]
theorem b03_length : b03.length = 32 := by simp only [b03,List.length_cons,List.length_nil]
theorem b03_canonical : canonical (bytesOf b03) := by
  change canonical [221,137,3,66,212,39,192,8,250,231,100,36,11,45,15,0,213,61,44,75,85,38,92,14,39,71,243,61,158,121,109,18]
  simp only [canonical_four]
  exact ⟨by decide, ⟨by decide, ⟨by decide, ⟨by decide, ⟨by decide, ⟨by decide, ⟨by decide, ⟨by decide, JFz_Canonical.nil⟩⟩⟩⟩⟩⟩⟩⟩
#print axioms b03_canonical
#print axioms b03_length
def b04 : List U8 := [93#u8,160#u8,19#u8,21#u8,234#u8,7#u8,171#u8,61#u8,146#u8,221#u8,114#u8,28#u8,37#u8,168#u8,119#u8,46#u8,186#u8,190#u8,88#u8,96#u8,227#u8,57#u8,148#u8,65#u8,181#u8,174#u8,156#u8,25#u8,80#u8,161#u8,252#u8,36#u8]
theorem b04_length : b04.length = 32 := by simp only [b04,List.length_cons,List.length_nil]
theorem b04_canonical : canonical (bytesOf b04) := by
  change canonical [93,160,19,21,234,7,171,61,146,221,114,28,37,168,119,46,186,190,88,96,227,57,148,65,181,174,156,25,80,161,252,36]
  simp only [canonical_four]
  exact ⟨by decide, ⟨by decide, ⟨by decide, ⟨by decide, ⟨by decide, ⟨by decide, ⟨by decide, ⟨by decide, JFz_Canonical.nil⟩⟩⟩⟩⟩⟩⟩⟩
#print axioms b04_canonical
#print axioms b04_length
def b05 : List U8 := [179#u8,227#u8,216#u8,115#u8,107#u8,30#u8,42#u8,90#u8,30#u8,186#u8,122#u8,97#u8,100#u8,85#u8,149#u8,1#u8,156#u8,226#u8,232#u8,37#u8,141#u8,175#u8,231#u8,19#u8,154#u8,163#u8,133#u8,78#u8,210#u8,210#u8,119#u8,73#u8]
theorem b05_length : b05.length = 32 := by simp only [b05,List.length_cons,List.length_nil]
theorem b05_canonical : canonical (bytesOf b05) := by
  change canonical [179,227,216,115,107,30,42,90,30,186,122,97,100,85,149,1,156,226,232,37,141,175,231,19,154,163,133,78,210,210,119,73]
  simp only [canonical_four]
  exact ⟨by decide, ⟨by decide, ⟨by decide, ⟨by decide, ⟨by decide, ⟨by decide, ⟨by decide, ⟨by decide, JFz_Canonical.nil⟩⟩⟩⟩⟩⟩⟩⟩
#print axioms b05_canonical
#print axioms b05_length
def b06 : List U8 := [156#u8,130#u8,139#u8,110#u8,109#u8,177#u8,253#u8,37#u8,54#u8,100#u8,66#u8,4#u8,195#u8,114#u8,105#u8,16#u8,44#u8,214#u8,249#u8,118#u8,214#u8,186#u8,0#u8,1#u8,123#u8,81#u8,156#u8,103#u8,42#u8,0#u8,182#u8,3#u8]
theorem b06_length : b06.length = 32 := by simp only [b06,List.length_cons,List.length_nil]
theorem b06_canonical : canonical (bytesOf b06) := by
  change canonical [156,130,139,110,109,177,253,37,54,100,66,4,195,114,105,16,44,214,249,118,214,186,0,1,123,81,156,103,42,0,182,3]
  simp only [canonical_four]
  exact ⟨by decide, ⟨by decide, ⟨by decide, ⟨by decide, ⟨by decide, ⟨by decide, ⟨by decide, ⟨by decide, JFz_Canonical.nil⟩⟩⟩⟩⟩⟩⟩⟩
#print axioms b06_canonical
#print axioms b06_length
def b07 : List U8 := [16#u8,146#u8,47#u8,0#u8,167#u8,9#u8,193#u8,19#u8,65#u8,138#u8,102#u8,117#u8,218#u8,229#u8,69#u8,86#u8,237#u8,195#u8,240#u8,13#u8,85#u8,148#u8,114#u8,23#u8,251#u8,177#u8,99#u8,124#u8,176#u8,183#u8,252#u8,120#u8]
theorem b07_length : b07.length = 32 := by simp only [b07,List.length_cons,List.length_nil]
theorem b07_canonical : canonical (bytesOf b07) := by
  change canonical [16,146,47,0,167,9,193,19,65,138,102,117,218,229,69,86,237,195,240,13,85,148,114,23,251,177,99,124,176,183,252,120]
  simp only [canonical_four]
  exact ⟨by decide, ⟨by decide, ⟨by decide, ⟨by decide, ⟨by decide, ⟨by decide, ⟨by decide, ⟨by decide, JFz_Canonical.nil⟩⟩⟩⟩⟩⟩⟩⟩
#print axioms b07_canonical
#print axioms b07_length
def b08 : List U8 := [215#u8,23#u8,94#u8,114#u8,124#u8,36#u8,215#u8,72#u8,56#u8,117#u8,255#u8,47#u8,63#u8,185#u8,57#u8,118#u8,71#u8,32#u8,40#u8,76#u8,80#u8,212#u8,95#u8,14#u8,167#u8,150#u8,210#u8,14#u8,253#u8,69#u8,115#u8,68#u8]
theorem b08_length : b08.length = 32 := by simp only [b08,List.length_cons,List.length_nil]
theorem b08_canonical : canonical (bytesOf b08) := by
  change canonical [215,23,94,114,124,36,215,72,56,117,255,47,63,185,57,118,71,32,40,76,80,212,95,14,167,150,210,14,253,69,115,68]
  simp only [canonical_four]
  exact ⟨by decide, ⟨by decide, ⟨by decide, ⟨by decide, ⟨by decide, ⟨by decide, ⟨by decide, ⟨by decide, JFz_Canonical.nil⟩⟩⟩⟩⟩⟩⟩⟩
#print axioms b08_canonical
#print axioms b08_length
def b09 : List U8 := [225#u8,240#u8,228#u8,101#u8,91#u8,30#u8,37#u8,110#u8,239#u8,34#u8,238#u8,46#u8,34#u8,14#u8,48#u8,94#u8,245#u8,64#u8,186#u8,37#u8,127#u8,205#u8,219#u8,92#u8,24#u8,193#u8,230#u8,94#u8,24#u8,216#u8,188#u8,58#u8]
theorem b09_length : b09.length = 32 := by simp only [b09,List.length_cons,List.length_nil]
theorem b09_canonical : canonical (bytesOf b09) := by
  change canonical [225,240,228,101,91,30,37,110,239,34,238,46,34,14,48,94,245,64,186,37,127,205,219,92,24,193,230,94,24,216,188,58]
  simp only [canonical_four]
  exact ⟨by decide, ⟨by decide, ⟨by decide, ⟨by decide, ⟨by decide, ⟨by decide, ⟨by decide, ⟨by decide, JFz_Canonical.nil⟩⟩⟩⟩⟩⟩⟩⟩
#print axioms b09_canonical
#print axioms b09_length
def b10 : List U8 := [39#u8,3#u8,9#u8,72#u8,195#u8,213#u8,189#u8,16#u8,30#u8,220#u8,173#u8,16#u8,185#u8,187#u8,23#u8,70#u8,116#u8,100#u8,1#u8,113#u8,177#u8,113#u8,1#u8,98#u8,31#u8,30#u8,193#u8,17#u8,234#u8,47#u8,241#u8,48#u8]
theorem b10_length : b10.length = 32 := by simp only [b10,List.length_cons,List.length_nil]
theorem b10_canonical : canonical (bytesOf b10) := by
  change canonical [39,3,9,72,195,213,189,16,30,220,173,16,185,187,23,70,116,100,1,113,177,113,1,98,31,30,193,17,234,47,241,48]
  simp only [canonical_four]
  exact ⟨by decide, ⟨by decide, ⟨by decide, ⟨by decide, ⟨by decide, ⟨by decide, ⟨by decide, ⟨by decide, JFz_Canonical.nil⟩⟩⟩⟩⟩⟩⟩⟩
#print axioms b10_canonical
#print axioms b10_length
def b11 : List U8 := [125#u8,151#u8,107#u8,55#u8,211#u8,19#u8,7#u8,116#u8,21#u8,177#u8,142#u8,45#u8,237#u8,130#u8,62#u8,10#u8,220#u8,113#u8,195#u8,62#u8,103#u8,111#u8,155#u8,73#u8,103#u8,118#u8,122#u8,44#u8,214#u8,251#u8,171#u8,54#u8]
theorem b11_length : b11.length = 32 := by simp only [b11,List.length_cons,List.length_nil]
theorem b11_canonical : canonical (bytesOf b11) := by
  change canonical [125,151,107,55,211,19,7,116,21,177,142,45,237,130,62,10,220,113,195,62,103,111,155,73,103,118,122,44,214,251,171,54]
  simp only [canonical_four]
  exact ⟨by decide, ⟨by decide, ⟨by decide, ⟨by decide, ⟨by decide, ⟨by decide, ⟨by decide, ⟨by decide, JFz_Canonical.nil⟩⟩⟩⟩⟩⟩⟩⟩
#print axioms b11_canonical
#print axioms b11_length
def b12 : List U8 := [27#u8,94#u8,179#u8,81#u8,49#u8,89#u8,173#u8,87#u8,247#u8,194#u8,181#u8,48#u8,202#u8,96#u8,12#u8,122#u8,150#u8,5#u8,36#u8,4#u8,215#u8,118#u8,233#u8,44#u8,21#u8,253#u8,238#u8,29#u8,85#u8,232#u8,143#u8,113#u8]
theorem b12_length : b12.length = 32 := by simp only [b12,List.length_cons,List.length_nil]
theorem b12_canonical : canonical (bytesOf b12) := by
  change canonical [27,94,179,81,49,89,173,87,247,194,181,48,202,96,12,122,150,5,36,4,215,118,233,44,21,253,238,29,85,232,143,113]
  simp only [canonical_four]
  exact ⟨by decide, ⟨by decide, ⟨by decide, ⟨by decide, ⟨by decide, ⟨by decide, ⟨by decide, ⟨by decide, JFz_Canonical.nil⟩⟩⟩⟩⟩⟩⟩⟩
#print axioms b12_canonical
#print axioms b12_length
def b13 : List U8 := [211#u8,78#u8,148#u8,68#u8,1#u8,255#u8,57#u8,89#u8,177#u8,62#u8,97#u8,100#u8,117#u8,69#u8,14#u8,117#u8,111#u8,146#u8,53#u8,39#u8,205#u8,39#u8,212#u8,116#u8,202#u8,244#u8,6#u8,32#u8,234#u8,183#u8,192#u8,84#u8]
theorem b13_length : b13.length = 32 := by simp only [b13,List.length_cons,List.length_nil]
theorem b13_canonical : canonical (bytesOf b13) := by
  change canonical [211,78,148,68,1,255,57,89,177,62,97,100,117,69,14,117,111,146,53,39,205,39,212,116,202,244,6,32,234,183,192,84]
  simp only [canonical_four]
  exact ⟨by decide, ⟨by decide, ⟨by decide, ⟨by decide, ⟨by decide, ⟨by decide, ⟨by decide, ⟨by decide, JFz_Canonical.nil⟩⟩⟩⟩⟩⟩⟩⟩
#print axioms b13_canonical
#print axioms b13_length
def b14 : List U8 := [132#u8,34#u8,205#u8,24#u8,61#u8,12#u8,127#u8,6#u8,218#u8,51#u8,141#u8,7#u8,13#u8,180#u8,50#u8,85#u8]
theorem b14_length : b14.length = 16 := by simp only [b14,List.length_cons,List.length_nil]
theorem b14_canonical : canonical (bytesOf b14) := by
  change canonical [132,34,205,24,61,12,127,6,218,51,141,7,13,180,50,85]
  simp only [canonical_four]
  exact ⟨by decide, ⟨by decide, ⟨by decide, ⟨by decide, JFz_Canonical.nil⟩⟩⟩⟩
#print axioms b14_canonical
#print axioms b14_length
def data : List U8 := (((b00 ++ (b01 ++ b02)) ++ ((b03 ++ b04) ++ (b05 ++ b06))) ++ (((b07 ++ b08) ++ (b09 ++ b10)) ++ ((b11 ++ b12) ++ (b13 ++ b14))))
theorem length : data.length = 464 := by simp only [data,List.length_append,b00_length,b01_length,b02_length,b03_length,b04_length,b05_length,b06_length,b07_length,b08_length,b09_length,b10_length,b11_length,b12_length,b13_length,b14_length]
theorem join0_length : (b01 ++ b02).length = 64 := by rw [List.length_append,b01_length,b02_length]
theorem join0 : canonical (bytesOf (b01 ++ b02)) := by
  rw [bytesOf,List.map_append,MultiproofConeCanonicalAppend.canonical_append _ _ (by change (b01).length % 4 = 0; rw [b01_length]; decide)]
  exact ⟨b01_canonical,b02_canonical⟩
theorem join1_length : (b00 ++ (b01 ++ b02)).length = 96 := by rw [List.length_append,b00_length,join0_length]
theorem join1 : canonical (bytesOf (b00 ++ (b01 ++ b02))) := by
  rw [bytesOf,List.map_append,MultiproofConeCanonicalAppend.canonical_append _ _ (by change (b00).length % 4 = 0; rw [b00_length]; decide)]
  exact ⟨b00_canonical,join0⟩
theorem join2_length : (b03 ++ b04).length = 64 := by rw [List.length_append,b03_length,b04_length]
theorem join2 : canonical (bytesOf (b03 ++ b04)) := by
  rw [bytesOf,List.map_append,MultiproofConeCanonicalAppend.canonical_append _ _ (by change (b03).length % 4 = 0; rw [b03_length]; decide)]
  exact ⟨b03_canonical,b04_canonical⟩
theorem join3_length : (b05 ++ b06).length = 64 := by rw [List.length_append,b05_length,b06_length]
theorem join3 : canonical (bytesOf (b05 ++ b06)) := by
  rw [bytesOf,List.map_append,MultiproofConeCanonicalAppend.canonical_append _ _ (by change (b05).length % 4 = 0; rw [b05_length]; decide)]
  exact ⟨b05_canonical,b06_canonical⟩
theorem join4_length : ((b03 ++ b04) ++ (b05 ++ b06)).length = 128 := by rw [List.length_append,join2_length,join3_length]
theorem join4 : canonical (bytesOf ((b03 ++ b04) ++ (b05 ++ b06))) := by
  rw [bytesOf,List.map_append,MultiproofConeCanonicalAppend.canonical_append _ _ (by change ((b03 ++ b04)).length % 4 = 0; rw [join2_length]; decide)]
  exact ⟨join2,join3⟩
theorem join5_length : ((b00 ++ (b01 ++ b02)) ++ ((b03 ++ b04) ++ (b05 ++ b06))).length = 224 := by rw [List.length_append,join1_length,join4_length]
theorem join5 : canonical (bytesOf ((b00 ++ (b01 ++ b02)) ++ ((b03 ++ b04) ++ (b05 ++ b06)))) := by
  rw [bytesOf,List.map_append,MultiproofConeCanonicalAppend.canonical_append _ _ (by change ((b00 ++ (b01 ++ b02))).length % 4 = 0; rw [join1_length]; decide)]
  exact ⟨join1,join4⟩
theorem join6_length : (b07 ++ b08).length = 64 := by rw [List.length_append,b07_length,b08_length]
theorem join6 : canonical (bytesOf (b07 ++ b08)) := by
  rw [bytesOf,List.map_append,MultiproofConeCanonicalAppend.canonical_append _ _ (by change (b07).length % 4 = 0; rw [b07_length]; decide)]
  exact ⟨b07_canonical,b08_canonical⟩
theorem join7_length : (b09 ++ b10).length = 64 := by rw [List.length_append,b09_length,b10_length]
theorem join7 : canonical (bytesOf (b09 ++ b10)) := by
  rw [bytesOf,List.map_append,MultiproofConeCanonicalAppend.canonical_append _ _ (by change (b09).length % 4 = 0; rw [b09_length]; decide)]
  exact ⟨b09_canonical,b10_canonical⟩
theorem join8_length : ((b07 ++ b08) ++ (b09 ++ b10)).length = 128 := by rw [List.length_append,join6_length,join7_length]
theorem join8 : canonical (bytesOf ((b07 ++ b08) ++ (b09 ++ b10))) := by
  rw [bytesOf,List.map_append,MultiproofConeCanonicalAppend.canonical_append _ _ (by change ((b07 ++ b08)).length % 4 = 0; rw [join6_length]; decide)]
  exact ⟨join6,join7⟩
theorem join9_length : (b11 ++ b12).length = 64 := by rw [List.length_append,b11_length,b12_length]
theorem join9 : canonical (bytesOf (b11 ++ b12)) := by
  rw [bytesOf,List.map_append,MultiproofConeCanonicalAppend.canonical_append _ _ (by change (b11).length % 4 = 0; rw [b11_length]; decide)]
  exact ⟨b11_canonical,b12_canonical⟩
theorem join10_length : (b13 ++ b14).length = 48 := by rw [List.length_append,b13_length,b14_length]
theorem join10 : canonical (bytesOf (b13 ++ b14)) := by
  rw [bytesOf,List.map_append,MultiproofConeCanonicalAppend.canonical_append _ _ (by change (b13).length % 4 = 0; rw [b13_length]; decide)]
  exact ⟨b13_canonical,b14_canonical⟩
theorem join11_length : ((b11 ++ b12) ++ (b13 ++ b14)).length = 112 := by rw [List.length_append,join9_length,join10_length]
theorem join11 : canonical (bytesOf ((b11 ++ b12) ++ (b13 ++ b14))) := by
  rw [bytesOf,List.map_append,MultiproofConeCanonicalAppend.canonical_append _ _ (by change ((b11 ++ b12)).length % 4 = 0; rw [join9_length]; decide)]
  exact ⟨join9,join10⟩
theorem join12_length : (((b07 ++ b08) ++ (b09 ++ b10)) ++ ((b11 ++ b12) ++ (b13 ++ b14))).length = 240 := by rw [List.length_append,join8_length,join11_length]
theorem join12 : canonical (bytesOf (((b07 ++ b08) ++ (b09 ++ b10)) ++ ((b11 ++ b12) ++ (b13 ++ b14)))) := by
  rw [bytesOf,List.map_append,MultiproofConeCanonicalAppend.canonical_append _ _ (by change (((b07 ++ b08) ++ (b09 ++ b10))).length % 4 = 0; rw [join8_length]; decide)]
  exact ⟨join8,join11⟩
theorem join13_length : (((b00 ++ (b01 ++ b02)) ++ ((b03 ++ b04) ++ (b05 ++ b06))) ++ (((b07 ++ b08) ++ (b09 ++ b10)) ++ ((b11 ++ b12) ++ (b13 ++ b14)))).length = 464 := by rw [List.length_append,join5_length,join12_length]
theorem join13 : canonical (bytesOf (((b00 ++ (b01 ++ b02)) ++ ((b03 ++ b04) ++ (b05 ++ b06))) ++ (((b07 ++ b08) ++ (b09 ++ b10)) ++ ((b11 ++ b12) ++ (b13 ++ b14))))) := by
  rw [bytesOf,List.map_append,MultiproofConeCanonicalAppend.canonical_append _ _ (by change (((b00 ++ (b01 ++ b02)) ++ ((b03 ++ b04) ++ (b05 ++ b06)))).length % 4 = 0; rw [join5_length]; decide)]
  exact ⟨join5,join12⟩
theorem canonical_data : canonical (bytesOf data) := join13
theorem selected : (JFx_NativeBytes.proof.val.drop 7031).take 464 = data := by
  change (JFx_NativeBytes.proofBytes.drop _).take _ = _
  simp only [JFx_NativeBytes.proofBytes,List.drop_append,List.take_append,List.length_append,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  simp only [JFx_DataProof01.bytes,JFx_DataProof01.c00_length,JFx_DataProof01.c01_length,JFx_DataProof01.c02_length,JFx_DataProof01.c03_length,JFx_DataProof01.c04_length,JFx_DataProof01.c05_length,JFx_DataProof01.c06_length,JFx_DataProof01.c07_length,JFx_DataProof01.c08_length,JFx_DataProof01.c09_length,JFx_DataProof01.c10_length,JFx_DataProof01.c11_length,JFx_DataProof01.c12_length,JFx_DataProof01.c13_length,JFx_DataProof01.c14_length,JFx_DataProof01.c15_length,JFx_DataProof01.c16_length,JFx_DataProof01.c17_length,JFx_DataProof01.c18_length,JFx_DataProof01.c19_length,JFx_DataProof01.c20_length,JFx_DataProof01.c21_length,JFx_DataProof01.c22_length,JFx_DataProof01.c23_length,JFx_DataProof01.c24_length,JFx_DataProof01.c25_length,JFx_DataProof01.c26_length,JFx_DataProof01.c27_length,JFx_DataProof01.c28_length,JFx_DataProof01.c29_length,JFx_DataProof01.c30_length,JFx_DataProof01.c31_length,JFx_DataProof01.c32_length,JFx_DataProof01.c33_length,JFx_DataProof01.c34_length,JFx_DataProof01.c35_length,JFx_DataProof01.c36_length,JFx_DataProof01.c37_length,JFx_DataProof01.c38_length,JFx_DataProof01.c39_length,JFx_DataProof01.c40_length,JFx_DataProof01.c41_length,JFx_DataProof01.c42_length,JFx_DataProof01.c43_length,JFx_DataProof01.c44_length,JFx_DataProof01.c45_length,JFx_DataProof01.c46_length,JFx_DataProof01.c47_length,JFx_DataProof01.c48_length,JFx_DataProof01.c49_length,JFx_DataProof01.c50_length,JFx_DataProof01.c51_length,JFx_DataProof01.c52_length,JFx_DataProof01.c53_length,JFx_DataProof01.c54_length,JFx_DataProof01.c55_length,JFx_DataProof01.c56_length,JFx_DataProof01.c57_length,JFx_DataProof01.c58_length,JFx_DataProof01.c59_length,JFx_DataProof01.c60_length,JFx_DataProof01.c61_length,JFx_DataProof01.c62_length,JFx_DataProof01.c63_length,JFx_DataProof01.c64_length,JFx_DataProof01.c65_length,JFx_DataProof01.c66_length,JFx_DataProof01.c67_length,JFx_DataProof01.c68_length,JFx_DataProof01.c69_length,JFx_DataProof01.c70_length,JFx_DataProof01.c71_length,JFx_DataProof01.c72_length,JFx_DataProof01.c73_length,JFx_DataProof01.c74_length,JFx_DataProof01.c75_length,JFx_DataProof01.c76_length,JFx_DataProof01.c77_length,JFx_DataProof01.c78_length,JFx_DataProof01.c79_length,JFx_DataProof01.c80_length,JFx_DataProof01.c81_length,JFx_DataProof01.c82_length,JFx_DataProof01.c83_length,JFx_DataProof01.c84_length,JFx_DataProof01.c85_length,JFx_DataProof01.c86_length,JFx_DataProof01.c87_length,JFx_DataProof01.c88_length,JFx_DataProof01.c89_length,JFx_DataProof01.c90_length,JFx_DataProof01.c91_length,JFx_DataProof01.c92_length,JFx_DataProof01.c93_length,JFx_DataProof01.c94_length,JFx_DataProof01.c95_length,JFx_DataProof01.c96_length,JFx_DataProof01.c97_length,JFx_DataProof01.c98_length,JFx_DataProof01.c99_length,JFx_DataProof01.c100_length,JFx_DataProof01.c101_length,JFx_DataProof01.c102_length,JFx_DataProof01.c103_length,JFx_DataProof01.c104_length,JFx_DataProof01.c105_length,JFx_DataProof01.c106_length,JFx_DataProof01.c107_length,JFx_DataProof01.c108_length,JFx_DataProof01.c109_length,JFx_DataProof01.c110_length,JFx_DataProof01.c111_length,JFx_DataProof01.c112_length,JFx_DataProof01.c113_length,JFx_DataProof01.c114_length,JFx_DataProof01.c115_length,JFx_DataProof01.c116_length,JFx_DataProof01.c117_length,JFx_DataProof01.c118_length,JFx_DataProof01.c119_length,JFx_DataProof01.c120_length,JFx_DataProof01.c121_length,JFx_DataProof01.c122_length,JFx_DataProof01.c123_length,JFx_DataProof01.c124_length,JFx_DataProof01.c125_length,JFx_DataProof01.c126_length,JFx_DataProof01.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
theorem canonical_selected : canonical (slice (bytesOf JFx_NativeBytes.proof.val) 7031 464) := by
  simp only [slice,bytesOf, ← List.map_drop, ← List.map_take,selected]
  exact canonical_data
#print axioms length
#print axioms canonical_data
#print axioms selected
#print axioms canonical_selected
end AspisR1.JFz_Scan00
end
