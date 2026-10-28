import NDO_JGe_Payload31
import NDO_JGe_Q31Absorb
import NDO_JGe_OpeningInit
import NDO_JGe_Q30Ratchet0
set_option autoImplicit false
namespace AspisR1.JGg_Input31
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open JGe_Window31
def before : State := JFp_SHADigest.output JGe_Q30Ratchet0.result
def payload : Slice U8 := JGe_Payload31.value
def n00 : List Nat := [219,150,241,213,245,37,196,162,119,39,151,176,79,1,28,104,231,245,171,60,175,54,235,164,136,31,43,140,254,45,2,196,0,191,0,8,0,0]
def n01 : List Nat := [217,140,103,105,77,42,182,88,100,143,152,89,242,85,110,93,40,66,154,84,93,202,248,25,75,119,77,81,199,223,235,98]
def n02 : List Nat := [113,92,103,13,127,237,168,90,154,230,192,23,111,116,118,61,198,108,244,41,36,62,85,4,195,26,27,78,171,161,57,67]
def n03 : List Nat := [216,23,149,104,38,117,157,116,128,9,143,83,201,190,254,47,31,201,249,6,7,179,95,47,237,37,24,35,169,48,30,15]
def n04 : List Nat := [177,75,169,102,11,35,145,88,244,178,166,54,128,232,120,51,46,223,148,92,255,144,224,41,8,134,215,5,193,125,106,123]
def n05 : List Nat := [109,44,130,123,31,226,113,63,72,130,13,99,189,134,65,59,3,114,164,75,21,216,65,18,168,10,55,15,111,98,79,41]
def n06 : List Nat := [26,231,61,31,32,95,205,81,224,90,199,90,247,218,58,42,147,44,191,19,68,151,136,68,135,242,54,75,169,49,100,17]
def n07 : List Nat := [242,12,39,60,184,202,206,32,184,226,24,14,45,215,146,52,36,166,108,13,227,143,118,109,140,172,125,18,113,59,126,79]
def n08 : List Nat := [241,249,102,112,122,159,203,121,245,164,142,86,1,219,229,126,60,3,221,76,207,34,77,70,218,14,48,95,97,27,176,21]
def n09 : List Nat := [184,79,208,11,76,69,58,89,224,69,221,97,44,245,244,90,1,104,150,80,11,58,254,6,5,44,221,6,155,200,29,125]
def n10 : List Nat := [143,194,181,27,77,181,171,91,249,243,204,64,237,139,168,101,97,62,75,63,53,120,74,43,85,209,24,20,52,73,119,39]
def n11 : List Nat := [58,188,10,1,114,7,37,105,10,17,202,19,170,52,148,13,238,126,143,64,221,18,66,21,171,64,16,34,243,206,78,4]
def n12 : List Nat := [71,78,199,122,149,196,83,96,17,233,217,57,42,153,60,16,12,69,233,27,116,115,84,45,190,155,251,93,102,76,247,81]
def n13 : List Nat := [102,162,55,21,24,186,199,94,198,57,28,19,124,177,132,86,255,24,111,85,86,187,68,116,56,156,211,70,252,212,209,62]
def n14 : List Nat := [113,3,25,117,170,73,221,84,114,229,132,116,26,85,160,99,54,71,250,89,232,14,118,115,148,167,18,32,196,230,242,36]
def n15 : List Nat := [112,34,187,69,104,94,192,112,64,197,27,123,141,195,42,29,230,50,185,56,154,33,180,54,187,9,162,27,59,238,213,94]
def n16 : List Nat := [189,192,255,86,189,68,187,21,111,215,64,99,222,14,45,100,240,93,84,51,64,209,94,101,24,57,13,6,21,134,254,119]
def n17 : List Nat := [230,21,234,47,209,218,179,85,139,59,107,65,73,70,130,28,242,115,171,67,39,178,213,36,24,109,202,28,53,175,252,78]
def n18 : List Nat := [255,241,159,104,47,225,187,24,81,49,20,64,231,43,19,98,186,92,53,16,4,163,147,17,91,246,117,61,126,108,31,70]
def n19 : List Nat := [132,23,137,6,212,68,254,11,127,155,3,33,106,36,90,83,46,82,87,9,47,113,184,124,67,134,106,68,128,40,25,3]
def n20 : List Nat := [76,16,24,47,94,244,111,42,107,139,53,80,47,153,84,7,88,159,161,92,168,159,68,127,74,0,227,9,129,72,228,97]
def n21 : List Nat := [21,38,4,34,87,111,191,8,118,74,104,10,160,105,213,40,97,38,150,62,180,142,141,8,84,3,4,77,118,168,241,64]
def n22 : List Nat := [15,126,178,19,192,219,16,97,15,34,176,89,32,220,20,50,46,208,83,7,90,40,153,120,132,118,183,74,37,190,168,20]
def n23 : List Nat := [79,249,140,37,163,72,117,90,231,160,217,119,51,89,105,40,190,154,107,46,40,64,169,23,154,139,130,118,204,178,127,92]
def n24 : List Nat := [71,250,253,71,104,66,144,18,87,144,50,103,161,213,190,100,103,23,214,74,174,227,149,28,96,65,15,40,175,11,158,100]
def n25 : List Nat := [26,158,43,78,50,204,91,123,47,5,192,121,230,151,229,94,199,219,172,70,106,136,175,107,127,210,88,24,71,60,215,121]
def n26 : List Nat := [28,183,117,49,142,67,137,110,123,35,233,5,64,50,241,122,66,22,203,99,75,22,239,42,20,83,213,45,209,154,98,44]
def n27 : List Nat := [85,7,187,113,131,177,45,110,148,129,234,87,132,62,37,90,195,215,238,34,219,133,76,83,254,46,244,17,154,71,253,110]
def n28 : List Nat := [126,18,56,100,225,32,88,49,66,156,126,78,128,214,67,103,73,226,5,24,88,86,30,107,23,40,6,111,210,64,100,37]
def n29 : List Nat := [12,228,50,47,247,27,101,22,174,178,36,50,8,241,16,74,16,6,175,78,95,103,56,95,47,18,191,67,211,160,249,83]
def n30 : List Nat := [188,142,21,100,253,168,242,64,204,204,233,47,201,245,126,57,200,133,147,59,172,134,239,98,150,218,226,13,40,241,198,67]
def n31 : List Nat := [22,103,60,78,116,64,221,42,248,29,174,109,87,95,22,113,193,104,140,99,130,169,95,65,68,115,23,69,145,83,106,105]
def n32 : List Nat := [65,55,171,112,0,7,89,115,140,249,9,33,213,221,63,94,205,213,83,38,157,234,220,39,112,23,232,2,24,213,36,5]
def n33 : List Nat := [199,10,18,80,164,148,11,87,168,251,197,33,140,109,48,1,156,214,5,34,231,64,227,43,28,80,88,71,84,192,178,103]
def n34 : List Nat := [128,246,223,73,4,12,112,86,163,224,220,77,118,81,116,74,13,121,103,10,220,202,100,93,19,220,50,68,148,103,6,39]
def n35 : List Nat := [78,64,147,7,90,135,91,39,83,18,40,44,79,214,207,118,7,81,52,34,181,230,155,89,41,156,243,106,103,39,177,53]
def n36 : List Nat := [231,168,150,18,255,91,1,53,84,74,255,8,217,222,39,121,136,246,117,94,121,47,173,47,42,168,202,4,219,169,29,110]
def n37 : List Nat := [0,177,192,58,229,203,99,27,188,201,48,117,112,208,243,18,156,248,51,6,38,70,116,79,200,75,226,24,140,214,163,66]
def n38 : List Nat := [45,126,213,1,145,247,252,89,47,250,136,92,146,202,35,125,219,55,99,12,255,173,147,10,40,56,225,111,36,71,183,127]
def n39 : List Nat := [57,187,112,7,235,46,47,2,0,112,118,18,108,253,189,108,213,56,87,91,126,147,220,65,238,250,78,92,39,84,221,43]
def n40 : List Nat := [66,94,244,68,188,185,117,105,0,28,59,87,200,222,77,41,12,25,167,41,212,129,88,80,63,105,183,43,155,214,49,81]
def n41 : List Nat := [240,37,31,47,0,189,16,13,170,34,146,27,113,104,227,109,103,1,154,125,106,80,166,30,97,176,152,65,192,65,1,108]
def n42 : List Nat := [87,2,199,54,79,247,144,111,245,73,133,65,247,31,58,54,104,172,156,114,233,142,200,8,143,112,176,21,60,180,218,20]
def n43 : List Nat := [2,119,208,81,210,148,146,31,48,249,216,6,248,182,143,99,62,194,66,14,55,80,95,63,7,145,143,41,39,203,183,111]
def n44 : List Nat := [228,5,163,26,182,76,46,103,102,105,150,22,216,237,99,91,177,172,1,98,215,54,64,113,28,2,142,99,217,39,42,24]
def n45 : List Nat := [47,83,111,109,58,104,159,113,82,32,132,113,41,144,155,98,183,34,164,109,239,187,204,60,156,121,82,78,211,49,160,19]
def n46 : List Nat := [230,251,175,28,24,219,251,11,210,232,3,42,110,61,246,22,29,12,105,11,67,148,12,31,151,95,164,72,154,182,62,85]
def n47 : List Nat := [171,208,49,3,235,1,68,53,88,251,22,108,199,190,74,110,135,209,159,52,10,213,58,8,80,167,117,36,213,149,108,121]
def n48 : List Nat := [3,181,227,50,156,4,137,39,251,147,139,95,62,76,236,5,164,157,14,96,141,224,84,74,217,218,143,64,133,98,93,109]
def n49 : List Nat := [136,199,234,94,177,195,85,96,138,73,24,18,218,186,17,35,244,65,203,87,74,254,160,100,81,11,87,3,38,91,215,51]
def n50 : List Nat := [207,209,90,79,34,248,77,5,198,245,102,6,145,229,122,65,226,164,48,13,36,202,53,99,135,231,135,31,254,213,109,105]
def n51 : List Nat := [244,20,80,29,63,239,186,95,200,11,245,88,63,46,41,111,48,254,8,11,170,91,72,102,219,73,12,122,223,173,188,1]
def n52 : List Nat := [234,138,105,20,127,55,33,3,76,95,106,96,24,33,193,85,171,12,252,43,35,49,208,105,155,42,42,34,122,229,248,73]
def n53 : List Nat := [173,67,185,39,17,35,62,16,198,195,36,13,74,65,146,97,162,138,132,48,209,48,113,88,53,255,191,75,220,138,88,7]
def n54 : List Nat := [3,215,87,33,75,121,22,121,234,179,151,85,136,144,73,10,9,159,154,123,242,125,182,120,69,226,100,76,152,74,24,13]
def n55 : List Nat := [190,136,209,46,192,110,193,77,41,131,201,122,39,123,79,19,20,237,1,58,158,154,51,66,125,54,255,52,170,241,125,4]
def n56 : List Nat := [93,72,183,56,110,123,225,110,173,158,201,56,188,30,204,30,12,54,32,46,120,177,73,66,197,92,112,104,171,116,163,103]
def n57 : List Nat := [56,121,55,124,133,92,231,76,115,74,81,12,205,165,195,100,89,142,230,54,155,216,79,80,165,85,25,88,85,17,71,5]
def n58 : List Nat := [38,31,132,63,185,37,201,49,168,254,48,61,65,109,65,28,60,135,221,69,37,158,6,33,72,29,190,2,195,184,223,90]
def n59 : List Nat := [204,103,189,45,212,37,160,62,202,194,164,74,175,216,126,13,239,141,60,8,141,160,44,16,221,218,4,53,134,230,146,123]
def n60 : List Nat := [58,247,172,61,39,158,203,67,1,118,10,120,23,120,40,110,105,228,141,18,112,46,5,73,10,118,108,5,146,128,16,107]
def n61 : List Nat := [216,18,168,74,230,124,130,124,0,47,8,121,36,236,133,10,116,8,233,89,28,94,203,88,135,37,200,92,153,79,57,76]
def n62 : List Nat := [179,157,200,29,188,209,42,75,166,1,0,19,219,187,18,95,14,207,25,90,82,234,23,34,56,178,183,98,18,36,156,49]
def n63 : List Nat := [253,210,31,116,205,162,105,12,180,207,86,61,87,2,11,90,7,90,138,110,94,167,146,112,182,134,233,12,170,48,217,44]
def n64 : List Nat := [199,192,198,96,231,176,100,6,217,4,182,122,215,146,102,35,118,237,182,35,159,49,31,48,242,144,115,44,147,108,158,65]
theorem cast00 : c00.map (fun x=>x.val)=n01 := by rfl
#print axioms cast00
theorem cast01 : c01.map (fun x=>x.val)=n02 := by rfl
#print axioms cast01
theorem cast02 : c02.map (fun x=>x.val)=n03 := by rfl
#print axioms cast02
theorem cast03 : c03.map (fun x=>x.val)=n04 := by rfl
#print axioms cast03
theorem cast04 : c04.map (fun x=>x.val)=n05 := by rfl
#print axioms cast04
theorem cast05 : c05.map (fun x=>x.val)=n06 := by rfl
#print axioms cast05
theorem cast06 : c06.map (fun x=>x.val)=n07 := by rfl
#print axioms cast06
theorem cast07 : c07.map (fun x=>x.val)=n08 := by rfl
#print axioms cast07
theorem cast08 : c08.map (fun x=>x.val)=n09 := by rfl
#print axioms cast08
theorem cast09 : c09.map (fun x=>x.val)=n10 := by rfl
#print axioms cast09
theorem cast10 : c10.map (fun x=>x.val)=n11 := by rfl
#print axioms cast10
theorem cast11 : c11.map (fun x=>x.val)=n12 := by rfl
#print axioms cast11
theorem cast12 : c12.map (fun x=>x.val)=n13 := by rfl
#print axioms cast12
theorem cast13 : c13.map (fun x=>x.val)=n14 := by rfl
#print axioms cast13
theorem cast14 : c14.map (fun x=>x.val)=n15 := by rfl
#print axioms cast14
theorem cast15 : c15.map (fun x=>x.val)=n16 := by rfl
#print axioms cast15
theorem cast16 : c16.map (fun x=>x.val)=n17 := by rfl
#print axioms cast16
theorem cast17 : c17.map (fun x=>x.val)=n18 := by rfl
#print axioms cast17
theorem cast18 : c18.map (fun x=>x.val)=n19 := by rfl
#print axioms cast18
theorem cast19 : c19.map (fun x=>x.val)=n20 := by rfl
#print axioms cast19
theorem cast20 : c20.map (fun x=>x.val)=n21 := by rfl
#print axioms cast20
theorem cast21 : c21.map (fun x=>x.val)=n22 := by rfl
#print axioms cast21
theorem cast22 : c22.map (fun x=>x.val)=n23 := by rfl
#print axioms cast22
theorem cast23 : c23.map (fun x=>x.val)=n24 := by rfl
#print axioms cast23
theorem cast24 : c24.map (fun x=>x.val)=n25 := by rfl
#print axioms cast24
theorem cast25 : c25.map (fun x=>x.val)=n26 := by rfl
#print axioms cast25
theorem cast26 : c26.map (fun x=>x.val)=n27 := by rfl
#print axioms cast26
theorem cast27 : c27.map (fun x=>x.val)=n28 := by rfl
#print axioms cast27
theorem cast28 : c28.map (fun x=>x.val)=n29 := by rfl
#print axioms cast28
theorem cast29 : c29.map (fun x=>x.val)=n30 := by rfl
#print axioms cast29
theorem cast30 : c30.map (fun x=>x.val)=n31 := by rfl
#print axioms cast30
theorem cast31 : c31.map (fun x=>x.val)=n32 := by rfl
#print axioms cast31
theorem cast32 : c32.map (fun x=>x.val)=n33 := by rfl
#print axioms cast32
theorem cast33 : c33.map (fun x=>x.val)=n34 := by rfl
#print axioms cast33
theorem cast34 : c34.map (fun x=>x.val)=n35 := by rfl
#print axioms cast34
theorem cast35 : c35.map (fun x=>x.val)=n36 := by rfl
#print axioms cast35
theorem cast36 : c36.map (fun x=>x.val)=n37 := by rfl
#print axioms cast36
theorem cast37 : c37.map (fun x=>x.val)=n38 := by rfl
#print axioms cast37
theorem cast38 : c38.map (fun x=>x.val)=n39 := by rfl
#print axioms cast38
theorem cast39 : c39.map (fun x=>x.val)=n40 := by rfl
#print axioms cast39
theorem cast40 : c40.map (fun x=>x.val)=n41 := by rfl
#print axioms cast40
theorem cast41 : c41.map (fun x=>x.val)=n42 := by rfl
#print axioms cast41
theorem cast42 : c42.map (fun x=>x.val)=n43 := by rfl
#print axioms cast42
theorem cast43 : c43.map (fun x=>x.val)=n44 := by rfl
#print axioms cast43
theorem cast44 : c44.map (fun x=>x.val)=n45 := by rfl
#print axioms cast44
theorem cast45 : c45.map (fun x=>x.val)=n46 := by rfl
#print axioms cast45
theorem cast46 : c46.map (fun x=>x.val)=n47 := by rfl
#print axioms cast46
theorem cast47 : c47.map (fun x=>x.val)=n48 := by rfl
#print axioms cast47
theorem cast48 : c48.map (fun x=>x.val)=n49 := by rfl
#print axioms cast48
theorem cast49 : c49.map (fun x=>x.val)=n50 := by rfl
#print axioms cast49
theorem cast50 : c50.map (fun x=>x.val)=n51 := by rfl
#print axioms cast50
theorem cast51 : c51.map (fun x=>x.val)=n52 := by rfl
#print axioms cast51
theorem cast52 : c52.map (fun x=>x.val)=n53 := by rfl
#print axioms cast52
theorem cast53 : c53.map (fun x=>x.val)=n54 := by rfl
#print axioms cast53
theorem cast54 : c54.map (fun x=>x.val)=n55 := by rfl
#print axioms cast54
theorem cast55 : c55.map (fun x=>x.val)=n56 := by rfl
#print axioms cast55
theorem cast56 : c56.map (fun x=>x.val)=n57 := by rfl
#print axioms cast56
theorem cast57 : c57.map (fun x=>x.val)=n58 := by rfl
#print axioms cast57
theorem cast58 : c58.map (fun x=>x.val)=n59 := by rfl
#print axioms cast58
theorem cast59 : c59.map (fun x=>x.val)=n60 := by rfl
#print axioms cast59
theorem cast60 : c60.map (fun x=>x.val)=n61 := by rfl
#print axioms cast60
theorem cast61 : c61.map (fun x=>x.val)=n62 := by rfl
#print axioms cast61
theorem cast62 : c62.map (fun x=>x.val)=n63 := by rfl
#print axioms cast62
theorem cast63 : c63.map (fun x=>x.val)=n64 := by rfl
#print axioms cast63
theorem payloadNat : payload.val.map (fun x=>x.val)=n01 ++ n02 ++ n03 ++ n04 ++ n05 ++ n06 ++ n07 ++ n08 ++ n09 ++ n10 ++ n11 ++ n12 ++ n13 ++ n14 ++ n15 ++ n16 ++ n17 ++ n18 ++ n19 ++ n20 ++ n21 ++ n22 ++ n23 ++ n24 ++ n25 ++ n26 ++ n27 ++ n28 ++ n29 ++ n30 ++ n31 ++ n32 ++ n33 ++ n34 ++ n35 ++ n36 ++ n37 ++ n38 ++ n39 ++ n40 ++ n41 ++ n42 ++ n43 ++ n44 ++ n45 ++ n46 ++ n47 ++ n48 ++ n49 ++ n50 ++ n51 ++ n52 ++ n53 ++ n54 ++ n55 ++ n56 ++ n57 ++ n58 ++ n59 ++ n60 ++ n61 ++ n62 ++ n63 ++ n64 := by
  rw [show payload.val=JGe_Payload31.rawChunks.flatten from JGe_Payload31.retained]
  simp only [JGe_Payload31.rawChunks]
  simp only [List.flatten_cons,List.flatten_nil,List.map_append,List.map_nil,List.append_nil,cast00,cast01,cast02,cast03,cast04,cast05,cast06,cast07,cast08,cast09,cast10,cast11,cast12,cast13,cast14,cast15,cast16,cast17,cast18,cast19,cast20,cast21,cast22,cast23,cast24,cast25,cast26,cast27,cast28,cast29,cast30,cast31,cast32,cast33,cast34,cast35,cast36,cast37,cast38,cast39,cast40,cast41,cast42,cast43,cast44,cast45,cast46,cast47,cast48,cast49,cast50,cast51,cast52,cast53,cast54,cast55,cast56,cast57,cast58,cast59,cast60,cast61,cast62,cast63]
  <;> simp only [List.append_assoc]
#print axioms payloadNat
theorem prefixCast : (encodeState before).val.map (fun x=>x.val) ++ [0,191] ++ [0,8,0,0]=n00 := by rfl
#print axioms prefixCast
def numeric : List Nat := n00 ++ n01 ++ n02 ++ n03 ++ n04 ++ n05 ++ n06 ++ n07 ++ n08 ++ n09 ++ n10 ++ n11 ++ n12 ++ n13 ++ n14 ++ n15 ++ n16 ++ n17 ++ n18 ++ n19 ++ n20 ++ n21 ++ n22 ++ n23 ++ n24 ++ n25 ++ n26 ++ n27 ++ n28 ++ n29 ++ n30 ++ n31 ++ n32 ++ n33 ++ n34 ++ n35 ++ n36 ++ n37 ++ n38 ++ n39 ++ n40 ++ n41 ++ n42 ++ n43 ++ n44 ++ n45 ++ n46 ++ n47 ++ n48 ++ n49 ++ n50 ++ n51 ++ n52 ++ n53 ++ n54 ++ n55 ++ n56 ++ n57 ++ n58 ++ n59 ++ n60 ++ n61 ++ n62 ++ n63 ++ n64
def suffix065 : List Nat := []
def suffix064 : List Nat := n64 ++ suffix065
def suffix063 : List Nat := n63 ++ suffix064
def suffix062 : List Nat := n62 ++ suffix063
def suffix061 : List Nat := n61 ++ suffix062
def suffix060 : List Nat := n60 ++ suffix061
def suffix059 : List Nat := n59 ++ suffix060
def suffix058 : List Nat := n58 ++ suffix059
def suffix057 : List Nat := n57 ++ suffix058
def suffix056 : List Nat := n56 ++ suffix057
def suffix055 : List Nat := n55 ++ suffix056
def suffix054 : List Nat := n54 ++ suffix055
def suffix053 : List Nat := n53 ++ suffix054
def suffix052 : List Nat := n52 ++ suffix053
def suffix051 : List Nat := n51 ++ suffix052
def suffix050 : List Nat := n50 ++ suffix051
def suffix049 : List Nat := n49 ++ suffix050
def suffix048 : List Nat := n48 ++ suffix049
def suffix047 : List Nat := n47 ++ suffix048
def suffix046 : List Nat := n46 ++ suffix047
def suffix045 : List Nat := n45 ++ suffix046
def suffix044 : List Nat := n44 ++ suffix045
def suffix043 : List Nat := n43 ++ suffix044
def suffix042 : List Nat := n42 ++ suffix043
def suffix041 : List Nat := n41 ++ suffix042
def suffix040 : List Nat := n40 ++ suffix041
def suffix039 : List Nat := n39 ++ suffix040
def suffix038 : List Nat := n38 ++ suffix039
def suffix037 : List Nat := n37 ++ suffix038
def suffix036 : List Nat := n36 ++ suffix037
def suffix035 : List Nat := n35 ++ suffix036
def suffix034 : List Nat := n34 ++ suffix035
def suffix033 : List Nat := n33 ++ suffix034
def suffix032 : List Nat := n32 ++ suffix033
def suffix031 : List Nat := n31 ++ suffix032
def suffix030 : List Nat := n30 ++ suffix031
def suffix029 : List Nat := n29 ++ suffix030
def suffix028 : List Nat := n28 ++ suffix029
def suffix027 : List Nat := n27 ++ suffix028
def suffix026 : List Nat := n26 ++ suffix027
def suffix025 : List Nat := n25 ++ suffix026
def suffix024 : List Nat := n24 ++ suffix025
def suffix023 : List Nat := n23 ++ suffix024
def suffix022 : List Nat := n22 ++ suffix023
def suffix021 : List Nat := n21 ++ suffix022
def suffix020 : List Nat := n20 ++ suffix021
def suffix019 : List Nat := n19 ++ suffix020
def suffix018 : List Nat := n18 ++ suffix019
def suffix017 : List Nat := n17 ++ suffix018
def suffix016 : List Nat := n16 ++ suffix017
def suffix015 : List Nat := n15 ++ suffix016
def suffix014 : List Nat := n14 ++ suffix015
def suffix013 : List Nat := n13 ++ suffix014
def suffix012 : List Nat := n12 ++ suffix013
def suffix011 : List Nat := n11 ++ suffix012
def suffix010 : List Nat := n10 ++ suffix011
def suffix009 : List Nat := n09 ++ suffix010
def suffix008 : List Nat := n08 ++ suffix009
def suffix007 : List Nat := n07 ++ suffix008
def suffix006 : List Nat := n06 ++ suffix007
def suffix005 : List Nat := n05 ++ suffix006
def suffix004 : List Nat := n04 ++ suffix005
def suffix003 : List Nat := n03 ++ suffix004
def suffix002 : List Nat := n02 ++ suffix003
def suffix001 : List Nat := n01 ++ suffix002
def suffix000 : List Nat := n00 ++ suffix001
attribute [local irreducible] suffix000 suffix001 suffix002 suffix003 suffix004 suffix005 suffix006 suffix007 suffix008 suffix009 suffix010 suffix011 suffix012 suffix013 suffix014 suffix015 suffix016 suffix017 suffix018 suffix019 suffix020 suffix021 suffix022 suffix023 suffix024 suffix025 suffix026 suffix027 suffix028 suffix029 suffix030 suffix031 suffix032 suffix033 suffix034 suffix035 suffix036 suffix037 suffix038 suffix039 suffix040 suffix041 suffix042 suffix043 suffix044 suffix045 suffix046 suffix047 suffix048 suffix049 suffix050 suffix051 suffix052 suffix053 suffix054 suffix055 suffix056 suffix057 suffix058 suffix059 suffix060 suffix061 suffix062 suffix063 suffix064 suffix065
def rest00 : List Nat := n00 ++ suffix001
def rest01 : List Nat := n01.drop 26 ++ suffix002
def rest02 : List Nat := n03.drop 26 ++ suffix004
def rest03 : List Nat := n05.drop 26 ++ suffix006
def rest04 : List Nat := n07.drop 26 ++ suffix008
def rest05 : List Nat := n09.drop 26 ++ suffix010
def rest06 : List Nat := n11.drop 26 ++ suffix012
def rest07 : List Nat := n13.drop 26 ++ suffix014
def rest08 : List Nat := n15.drop 26 ++ suffix016
def rest09 : List Nat := n17.drop 26 ++ suffix018
def rest10 : List Nat := n19.drop 26 ++ suffix020
def rest11 : List Nat := n21.drop 26 ++ suffix022
def rest12 : List Nat := n23.drop 26 ++ suffix024
def rest13 : List Nat := n25.drop 26 ++ suffix026
def rest14 : List Nat := n27.drop 26 ++ suffix028
def rest15 : List Nat := n29.drop 26 ++ suffix030
def rest16 : List Nat := n31.drop 26 ++ suffix032
def rest17 : List Nat := n33.drop 26 ++ suffix034
def rest18 : List Nat := n35.drop 26 ++ suffix036
def rest19 : List Nat := n37.drop 26 ++ suffix038
def rest20 : List Nat := n39.drop 26 ++ suffix040
def rest21 : List Nat := n41.drop 26 ++ suffix042
def rest22 : List Nat := n43.drop 26 ++ suffix044
def rest23 : List Nat := n45.drop 26 ++ suffix046
def rest24 : List Nat := n47.drop 26 ++ suffix048
def rest25 : List Nat := n49.drop 26 ++ suffix050
def rest26 : List Nat := n51.drop 26 ++ suffix052
def rest27 : List Nat := n53.drop 26 ++ suffix054
def rest28 : List Nat := n55.drop 26 ++ suffix056
def rest29 : List Nat := n57.drop 26 ++ suffix058
def rest30 : List Nat := n59.drop 26 ++ suffix060
def rest31 : List Nat := n61.drop 26 ++ suffix062
def rest32 : List Nat := n63.drop 26 ++ suffix064
theorem numeric_eq : numeric=rest00 := by
  simp only [numeric,rest00,List.append_assoc,List.append_nil,suffix001,suffix002,suffix003,suffix004,suffix005,suffix006,suffix007,suffix008,suffix009,suffix010,suffix011,suffix012,suffix013,suffix014,suffix015,suffix016,suffix017,suffix018,suffix019,suffix020,suffix021,suffix022,suffix023,suffix024,suffix025,suffix026,suffix027,suffix028,suffix029,suffix030,suffix031,suffix032,suffix033,suffix034,suffix035,suffix036,suffix037,suffix038,suffix039,suffix040,suffix041,suffix042,suffix043,suffix044,suffix045,suffix046,suffix047,suffix048,suffix049,suffix050,suffix051,suffix052,suffix053,suffix054,suffix055,suffix056,suffix057,suffix058,suffix059,suffix060,suffix061,suffix062,suffix063,suffix064,suffix065]
#print axioms numeric_eq
theorem step00 : rest00=JGe_Q31Absorb.B00.input ++ rest01 := by
  have cell : n00 ++ n01=JGe_Q31Absorb.B00.input ++ (n01.drop 26) := by rfl
  simpa only [rest00,rest01,suffix001,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix002) cell
#print axioms step00
theorem step01 : rest01=JGe_Q31Absorb.B01.input ++ rest02 := by
  have cell : (n01.drop 26) ++ n02 ++ n03=JGe_Q31Absorb.B01.input ++ (n03.drop 26) := by rfl
  simpa only [rest01,rest02,suffix002,suffix003,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix004) cell
#print axioms step01
theorem step02 : rest02=JGe_Q31Absorb.B02.input ++ rest03 := by
  have cell : (n03.drop 26) ++ n04 ++ n05=JGe_Q31Absorb.B02.input ++ (n05.drop 26) := by rfl
  simpa only [rest02,rest03,suffix004,suffix005,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix006) cell
#print axioms step02
theorem step03 : rest03=JGe_Q31Absorb.B03.input ++ rest04 := by
  have cell : (n05.drop 26) ++ n06 ++ n07=JGe_Q31Absorb.B03.input ++ (n07.drop 26) := by rfl
  simpa only [rest03,rest04,suffix006,suffix007,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix008) cell
#print axioms step03
theorem step04 : rest04=JGe_Q31Absorb.B04.input ++ rest05 := by
  have cell : (n07.drop 26) ++ n08 ++ n09=JGe_Q31Absorb.B04.input ++ (n09.drop 26) := by rfl
  simpa only [rest04,rest05,suffix008,suffix009,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix010) cell
#print axioms step04
theorem step05 : rest05=JGe_Q31Absorb.B05.input ++ rest06 := by
  have cell : (n09.drop 26) ++ n10 ++ n11=JGe_Q31Absorb.B05.input ++ (n11.drop 26) := by rfl
  simpa only [rest05,rest06,suffix010,suffix011,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix012) cell
#print axioms step05
theorem step06 : rest06=JGe_Q31Absorb.B06.input ++ rest07 := by
  have cell : (n11.drop 26) ++ n12 ++ n13=JGe_Q31Absorb.B06.input ++ (n13.drop 26) := by rfl
  simpa only [rest06,rest07,suffix012,suffix013,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix014) cell
#print axioms step06
theorem step07 : rest07=JGe_Q31Absorb.B07.input ++ rest08 := by
  have cell : (n13.drop 26) ++ n14 ++ n15=JGe_Q31Absorb.B07.input ++ (n15.drop 26) := by rfl
  simpa only [rest07,rest08,suffix014,suffix015,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix016) cell
#print axioms step07
theorem step08 : rest08=JGe_Q31Absorb.B08.input ++ rest09 := by
  have cell : (n15.drop 26) ++ n16 ++ n17=JGe_Q31Absorb.B08.input ++ (n17.drop 26) := by rfl
  simpa only [rest08,rest09,suffix016,suffix017,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix018) cell
#print axioms step08
theorem step09 : rest09=JGe_Q31Absorb.B09.input ++ rest10 := by
  have cell : (n17.drop 26) ++ n18 ++ n19=JGe_Q31Absorb.B09.input ++ (n19.drop 26) := by rfl
  simpa only [rest09,rest10,suffix018,suffix019,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix020) cell
#print axioms step09
theorem step10 : rest10=JGe_Q31Absorb.B10.input ++ rest11 := by
  have cell : (n19.drop 26) ++ n20 ++ n21=JGe_Q31Absorb.B10.input ++ (n21.drop 26) := by rfl
  simpa only [rest10,rest11,suffix020,suffix021,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix022) cell
#print axioms step10
theorem step11 : rest11=JGe_Q31Absorb.B11.input ++ rest12 := by
  have cell : (n21.drop 26) ++ n22 ++ n23=JGe_Q31Absorb.B11.input ++ (n23.drop 26) := by rfl
  simpa only [rest11,rest12,suffix022,suffix023,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix024) cell
#print axioms step11
theorem step12 : rest12=JGe_Q31Absorb.B12.input ++ rest13 := by
  have cell : (n23.drop 26) ++ n24 ++ n25=JGe_Q31Absorb.B12.input ++ (n25.drop 26) := by rfl
  simpa only [rest12,rest13,suffix024,suffix025,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix026) cell
#print axioms step12
theorem step13 : rest13=JGe_Q31Absorb.B13.input ++ rest14 := by
  have cell : (n25.drop 26) ++ n26 ++ n27=JGe_Q31Absorb.B13.input ++ (n27.drop 26) := by rfl
  simpa only [rest13,rest14,suffix026,suffix027,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix028) cell
#print axioms step13
theorem step14 : rest14=JGe_Q31Absorb.B14.input ++ rest15 := by
  have cell : (n27.drop 26) ++ n28 ++ n29=JGe_Q31Absorb.B14.input ++ (n29.drop 26) := by rfl
  simpa only [rest14,rest15,suffix028,suffix029,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix030) cell
#print axioms step14
theorem step15 : rest15=JGe_Q31Absorb.B15.input ++ rest16 := by
  have cell : (n29.drop 26) ++ n30 ++ n31=JGe_Q31Absorb.B15.input ++ (n31.drop 26) := by rfl
  simpa only [rest15,rest16,suffix030,suffix031,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix032) cell
#print axioms step15
theorem step16 : rest16=JGe_Q31Absorb.B16.input ++ rest17 := by
  have cell : (n31.drop 26) ++ n32 ++ n33=JGe_Q31Absorb.B16.input ++ (n33.drop 26) := by rfl
  simpa only [rest16,rest17,suffix032,suffix033,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix034) cell
#print axioms step16
theorem step17 : rest17=JGe_Q31Absorb.B17.input ++ rest18 := by
  have cell : (n33.drop 26) ++ n34 ++ n35=JGe_Q31Absorb.B17.input ++ (n35.drop 26) := by rfl
  simpa only [rest17,rest18,suffix034,suffix035,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix036) cell
#print axioms step17
theorem step18 : rest18=JGe_Q31Absorb.B18.input ++ rest19 := by
  have cell : (n35.drop 26) ++ n36 ++ n37=JGe_Q31Absorb.B18.input ++ (n37.drop 26) := by rfl
  simpa only [rest18,rest19,suffix036,suffix037,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix038) cell
#print axioms step18
theorem step19 : rest19=JGe_Q31Absorb.B19.input ++ rest20 := by
  have cell : (n37.drop 26) ++ n38 ++ n39=JGe_Q31Absorb.B19.input ++ (n39.drop 26) := by rfl
  simpa only [rest19,rest20,suffix038,suffix039,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix040) cell
#print axioms step19
theorem step20 : rest20=JGe_Q31Absorb.B20.input ++ rest21 := by
  have cell : (n39.drop 26) ++ n40 ++ n41=JGe_Q31Absorb.B20.input ++ (n41.drop 26) := by rfl
  simpa only [rest20,rest21,suffix040,suffix041,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix042) cell
#print axioms step20
theorem step21 : rest21=JGe_Q31Absorb.B21.input ++ rest22 := by
  have cell : (n41.drop 26) ++ n42 ++ n43=JGe_Q31Absorb.B21.input ++ (n43.drop 26) := by rfl
  simpa only [rest21,rest22,suffix042,suffix043,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix044) cell
#print axioms step21
theorem step22 : rest22=JGe_Q31Absorb.B22.input ++ rest23 := by
  have cell : (n43.drop 26) ++ n44 ++ n45=JGe_Q31Absorb.B22.input ++ (n45.drop 26) := by rfl
  simpa only [rest22,rest23,suffix044,suffix045,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix046) cell
#print axioms step22
theorem step23 : rest23=JGe_Q31Absorb.B23.input ++ rest24 := by
  have cell : (n45.drop 26) ++ n46 ++ n47=JGe_Q31Absorb.B23.input ++ (n47.drop 26) := by rfl
  simpa only [rest23,rest24,suffix046,suffix047,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix048) cell
#print axioms step23
theorem step24 : rest24=JGe_Q31Absorb.B24.input ++ rest25 := by
  have cell : (n47.drop 26) ++ n48 ++ n49=JGe_Q31Absorb.B24.input ++ (n49.drop 26) := by rfl
  simpa only [rest24,rest25,suffix048,suffix049,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix050) cell
#print axioms step24
theorem step25 : rest25=JGe_Q31Absorb.B25.input ++ rest26 := by
  have cell : (n49.drop 26) ++ n50 ++ n51=JGe_Q31Absorb.B25.input ++ (n51.drop 26) := by rfl
  simpa only [rest25,rest26,suffix050,suffix051,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix052) cell
#print axioms step25
theorem step26 : rest26=JGe_Q31Absorb.B26.input ++ rest27 := by
  have cell : (n51.drop 26) ++ n52 ++ n53=JGe_Q31Absorb.B26.input ++ (n53.drop 26) := by rfl
  simpa only [rest26,rest27,suffix052,suffix053,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix054) cell
#print axioms step26
theorem step27 : rest27=JGe_Q31Absorb.B27.input ++ rest28 := by
  have cell : (n53.drop 26) ++ n54 ++ n55=JGe_Q31Absorb.B27.input ++ (n55.drop 26) := by rfl
  simpa only [rest27,rest28,suffix054,suffix055,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix056) cell
#print axioms step27
theorem step28 : rest28=JGe_Q31Absorb.B28.input ++ rest29 := by
  have cell : (n55.drop 26) ++ n56 ++ n57=JGe_Q31Absorb.B28.input ++ (n57.drop 26) := by rfl
  simpa only [rest28,rest29,suffix056,suffix057,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix058) cell
#print axioms step28
theorem step29 : rest29=JGe_Q31Absorb.B29.input ++ rest30 := by
  have cell : (n57.drop 26) ++ n58 ++ n59=JGe_Q31Absorb.B29.input ++ (n59.drop 26) := by rfl
  simpa only [rest29,rest30,suffix058,suffix059,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix060) cell
#print axioms step29
theorem step30 : rest30=JGe_Q31Absorb.B30.input ++ rest31 := by
  have cell : (n59.drop 26) ++ n60 ++ n61=JGe_Q31Absorb.B30.input ++ (n61.drop 26) := by rfl
  simpa only [rest30,rest31,suffix060,suffix061,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix062) cell
#print axioms step30
theorem step31 : rest31=JGe_Q31Absorb.B31.input ++ rest32 := by
  have cell : (n61.drop 26) ++ n62 ++ n63=JGe_Q31Absorb.B31.input ++ (n63.drop 26) := by rfl
  simpa only [rest31,rest32,suffix062,suffix063,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix064) cell
#print axioms step31
theorem last : rest32=JGe_Q31Absorb.tail := by
  simp only [rest32,suffix064,suffix065,n63]
  rfl
#print axioms last
theorem regroup : numeric=JGe_Q31Absorb.message := by
  rw [numeric_eq]
  rw [step00,step01,step02,step03,step04,step05,step06,step07,step08,step09,step10,step11,step12,step13,step14,step15,step16,step17,step18,step19,step20,step21,step22,step23,step24,step25,step26,step27,step28,step29,step30,step31,last]
  simp only [JGe_Q31Absorb.message,JGe_Q31Absorb.head,List.flatten_cons,List.flatten_nil,List.append_nil,List.append_assoc]
#print axioms regroup
theorem lengthCast : (core.num.U32.to_le_bytes 2048#u32).val.map (fun x=>x.val)=[0,8,0,0] := by
  simp [core.num.U32.to_le_bytes,BitVec.toLEBytes] <;> (repeat' constructor) <;> scalar_tac
#print axioms lengthCast
theorem native : (flatten (CallerStep.openingAbsorbParts (encodeState before) 191#u8 2048#u32 payload)).map Fin.val=JGe_Q31Absorb.message := by
  rw [←regroup]
  simp only [flatten,CallerStep.openingAbsorbParts,Array.to_slice,Array.make,List.flatMap_cons,List.flatMap_nil,List.map_append,List.append_nil,List.map_map,Function.comp_def,decodeByte,payloadNat,lengthCast,List.map_cons,List.map_nil]
  change (encodeState before).val.map (fun x=>x.val) ++ ([0,191] ++ ([0,8,0,0] ++ (n01 ++ n02 ++ n03 ++ n04 ++ n05 ++ n06 ++ n07 ++ n08 ++ n09 ++ n10 ++ n11 ++ n12 ++ n13 ++ n14 ++ n15 ++ n16 ++ n17 ++ n18 ++ n19 ++ n20 ++ n21 ++ n22 ++ n23 ++ n24 ++ n25 ++ n26 ++ n27 ++ n28 ++ n29 ++ n30 ++ n31 ++ n32 ++ n33 ++ n34 ++ n35 ++ n36 ++ n37 ++ n38 ++ n39 ++ n40 ++ n41 ++ n42 ++ n43 ++ n44 ++ n45 ++ n46 ++ n47 ++ n48 ++ n49 ++ n50 ++ n51 ++ n52 ++ n53 ++ n54 ++ n55 ++ n56 ++ n57 ++ n58 ++ n59 ++ n60 ++ n61 ++ n62 ++ n63 ++ n64)))=numeric
  have h := congrArg (fun lead => lead ++ (n01 ++ n02 ++ n03 ++ n04 ++ n05 ++ n06 ++ n07 ++ n08 ++ n09 ++ n10 ++ n11 ++ n12 ++ n13 ++ n14 ++ n15 ++ n16 ++ n17 ++ n18 ++ n19 ++ n20 ++ n21 ++ n22 ++ n23 ++ n24 ++ n25 ++ n26 ++ n27 ++ n28 ++ n29 ++ n30 ++ n31 ++ n32 ++ n33 ++ n34 ++ n35 ++ n36 ++ n37 ++ n38 ++ n39 ++ n40 ++ n41 ++ n42 ++ n43 ++ n44 ++ n45 ++ n46 ++ n47 ++ n48 ++ n49 ++ n50 ++ n51 ++ n52 ++ n53 ++ n54 ++ n55 ++ n56 ++ n57 ++ n58 ++ n59 ++ n60 ++ n61 ++ n62 ++ n63 ++ n64)) prefixCast
  simpa only [numeric,List.append_assoc] using h
#print axioms native
end AspisR1.JGg_Input31
