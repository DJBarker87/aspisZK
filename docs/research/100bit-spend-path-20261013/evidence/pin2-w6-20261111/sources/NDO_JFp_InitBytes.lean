import NDO_JFs_ExactInitialization
import NDO_JFp_SeedHash
set_option autoImplicit false
namespace AspisR1.JFp_InitBytes
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisR1PublicPreparation
def root : Array U8 32#usize := ⟨[35#u8,84#u8,252#u8,170#u8,237#u8,249#u8,91#u8,67#u8,118#u8,98#u8,250#u8,35#u8,47#u8,53#u8,170#u8,242#u8,180#u8,167#u8,245#u8,80#u8,27#u8,213#u8,106#u8,60#u8,70#u8,25#u8,157#u8,233#u8,56#u8,202#u8,185#u8,163#u8],by rfl⟩
def n00 : List Nat := [85,78,80,82,79,86,69,68,58,82,49,58,80,82,73,86,65,84,69,45,83,65,76,84,69,68,58,83,69,77,65,78,84,73,67,58,80,51]
theorem cast00 : (AspisR1PublicPreparation.r1_wire.DOMAIN.val).map (fun x => x.val)=n00 := by
  simp only [r1_wire.DOMAIN,Array.make]
  rfl
#print axioms cast00
def n01 : List Nat := [0]
theorem cast01 : ([0#u8]).map (fun x => x.val)=n01 := by rfl
#print axioms cast01
def n02 : List Nat := [240,5,0,0]
theorem cast02 : ((core.num.U32.to_le_bytes 1520#u32).val).map (fun x => x.val)=n02 := by
  simp [core.num.U32.to_le_bytes,BitVec.toLEBytes,n02] <;> (repeat' constructor) <;> scalar_tac
#print axioms cast02
def n03 : List Nat := [0]
theorem cast03 : ([0#u8]).map (fun x => x.val)=n03 := by rfl
#print axioms cast03
def n04 : List Nat := [207,86,58,107,27,24,53,0,47,125,130,125,236,74,149,108,193,59,224,39,39,50,183,114,26,96,61,17,126,222,163,6]
theorem cast04 : (JFu_PublicDigest43.bytes).map (fun x => x.val)=n04 := by rfl
#print axioms cast04
def n05 : List Nat := [74,235,13,67,63,204,126,28,128,147,128,70,82,120,58,67,228,4,19,122,78,187,40,8,92,228,95,7,247,244,208,96]
theorem cast05 : (JFu_PublicDigest44.bytes).map (fun x => x.val)=n05 := by rfl
#print axioms cast05
def n06 : List Nat := [77,0,0,0]
theorem cast06 : ([77#u8,0#u8,0#u8,0#u8]).map (fun x => x.val)=n06 := by rfl
#print axioms cast06
def n07 : List Nat := [1]
theorem cast07 : ([1#u8]).map (fun x => x.val)=n07 := by rfl
#print axioms cast07
def n08 : List Nat := [98,235,242,88,34,61,120,62,229,254,204,35,44,143,136,70,90,56,197,41,180,240,143,18,216,130,197,88,155,112,209,46]
theorem cast08 : (JFu_PublicDigest45.bytes).map (fun x => x.val)=n08 := by rfl
#print axioms cast08
def n09 : List Nat := [47,66,212,42,38,217,93,75,148,190,138,9,60,235,219,6,16,209,200,13,99,59,150,100,156,71,122,81,104,184,85,78]
theorem cast09 : (JFu_PublicDigest46.bytes).map (fun x => x.val)=n09 := by rfl
#print axioms cast09
def n10 : List Nat := [0]
theorem cast10 : ([0#u8]).map (fun x => x.val)=n10 := by rfl
#print axioms cast10
def n11 : List Nat := [1,0,0,0,0,0,0,0]
theorem cast11 : ([1#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]).map (fun x => x.val)=n11 := by rfl
#print axioms cast11
def n12 : List Nat := [43,199,218,42,70,154,47,41,109,167,75,93,185,58,91,97,36,65,187,99,81,197,88,43,1,122,61,36,28,50,133,110]
theorem cast12 : (JFu_PublicDigest02.bytes).map (fun x => x.val)=n12 := by rfl
#print axioms cast12
def n13 : List Nat := [235,242,112,8,230,167,79,86,213,99,65,31,155,22,230,115,109,214,51,109,67,248,134,34,158,228,215,44,40,233,227,61]
theorem cast13 : (JFu_PublicDigest03.bytes).map (fun x => x.val)=n13 := by rfl
#print axioms cast13
def n14 : List Nat := [106,175,191,66,37,158,165,7,90,100,249,55,169,196,73,39,208,105,65,115,225,12,221,53,127,165,125,70,2,139,87,83]
theorem cast14 : (JFu_PublicDigest04.bytes).map (fun x => x.val)=n14 := by rfl
#print axioms cast14
def n15 : List Nat := [91,58,14,63,187,99,135,67,119,59,89,47,101,175,131,117,35,205,216,74,41,157,59,55,25,182,25,121,21,85,177,120]
theorem cast15 : (JFu_PublicDigest05.bytes).map (fun x => x.val)=n15 := by rfl
#print axioms cast15
def n16 : List Nat := [62,185,11,84,185,239,40,40,161,49,20,56,246,242,89,16,87,146,125,102,5,17,194,100,139,155,28,12,232,192,152,110]
theorem cast16 : (JFu_PublicDigest06.bytes).map (fun x => x.val)=n16 := by rfl
#print axioms cast16
def n17 : List Nat := [72,196,254,85,234,129,207,91,207,92,67,11,242,147,17,6,34,176,68,112,15,75,197,105,67,238,226,77,176,120,113,33]
theorem cast17 : (JFu_PublicDigest07.bytes).map (fun x => x.val)=n17 := by rfl
#print axioms cast17
def n18 : List Nat := [75,25,142,14,189,74,171,58,248,40,123,87,29,243,253,122,132,18,67,105,55,43,137,77,171,212,28,94,67,3,118,44]
theorem cast18 : (JFu_PublicDigest08.bytes).map (fun x => x.val)=n18 := by rfl
#print axioms cast18
def n19 : List Nat := [52,27,32,40,28,234,68,2,163,38,163,86,127,150,231,79,106,166,245,21,72,207,86,109,247,208,24,16,151,176,107,42]
theorem cast19 : (JFu_PublicDigest09.bytes).map (fun x => x.val)=n19 := by rfl
#print axioms cast19
def n20 : List Nat := [251,100,157,1,108,224,214,75,57,61,127,59,232,158,237,86,69,185,229,52,82,167,210,71,84,131,134,51,14,221,0,33]
theorem cast20 : (JFu_PublicDigest10.bytes).map (fun x => x.val)=n20 := by rfl
#print axioms cast20
def n21 : List Nat := [56,88,152,117,59,185,142,73,83,82,62,58,162,134,152,101,189,172,106,96,112,205,110,108,214,96,7,54,101,209,142,98]
theorem cast21 : (JFu_PublicDigest11.bytes).map (fun x => x.val)=n21 := by rfl
#print axioms cast21
def n22 : List Nat := [172,172,239,24,212,157,35,28,253,213,245,51,223,50,229,5,168,87,206,120,18,119,176,89,46,133,70,24,221,119,86,107]
theorem cast22 : (JFu_PublicDigest12.bytes).map (fun x => x.val)=n22 := by rfl
#print axioms cast22
def n23 : List Nat := [56,89,202,58,185,34,92,39,7,78,84,60,134,220,15,27,200,114,222,58,99,41,32,37,26,85,146,68,78,228,75,76]
theorem cast23 : (JFu_PublicDigest13.bytes).map (fun x => x.val)=n23 := by rfl
#print axioms cast23
def n24 : List Nat := [37,76,69,126,125,129,184,101,165,135,222,126,89,61,248,9,14,31,105,24,136,30,222,78,213,153,15,112,216,86,100,122]
theorem cast24 : (JFu_PublicDigest14.bytes).map (fun x => x.val)=n24 := by rfl
#print axioms cast24
def n25 : List Nat := [157,161,135,15,109,191,246,81,23,128,109,94,214,254,99,65,176,172,116,100,254,254,213,63,149,255,253,125,238,33,29,57]
theorem cast25 : (JFu_PublicDigest15.bytes).map (fun x => x.val)=n25 := by rfl
#print axioms cast25
def n26 : List Nat := [17,99,232,73,51,32,40,59,154,101,76,83,245,164,208,27,117,211,126,123,26,114,127,42,70,166,9,122,215,50,38,100]
theorem cast26 : (JFu_PublicDigest16.bytes).map (fun x => x.val)=n26 := by rfl
#print axioms cast26
def n27 : List Nat := [0,105,16,107,224,25,1,111,168,192,126,116,58,110,248,70,121,225,188,21,129,142,204,2,240,239,1,40,149,53,103,72]
theorem cast27 : (JFu_PublicDigest17.bytes).map (fun x => x.val)=n27 := by rfl
#print axioms cast27
def n28 : List Nat := [144,141,57,67,64,122,130,39,252,17,2,5,94,184,79,59,43,116,158,84,243,18,51,117,18,243,231,49,249,200,45,124]
theorem cast28 : (JFu_PublicDigest18.bytes).map (fun x => x.val)=n28 := by rfl
#print axioms cast28
def n29 : List Nat := [182,57,199,78,108,219,165,46,232,179,99,84,222,207,111,4,217,42,70,46,60,243,66,19,57,207,146,25,125,32,124,77]
theorem cast29 : (JFu_PublicDigest19.bytes).map (fun x => x.val)=n29 := by rfl
#print axioms cast29
def n30 : List Nat := [116,183,140,90,100,144,165,73,16,243,160,99,14,89,103,86,213,51,160,32,201,207,159,96,34,247,231,15,83,126,218,26]
theorem cast30 : (JFu_PublicDigest20.bytes).map (fun x => x.val)=n30 := by rfl
#print axioms cast30
def n31 : List Nat := [123,190,39,1,217,63,5,78,38,224,4,15,229,231,69,28,172,155,93,123,197,163,23,111,35,173,17,9,211,192,171,39]
theorem cast31 : (JFu_PublicDigest21.bytes).map (fun x => x.val)=n31 := by rfl
#print axioms cast31
def n32 : List Nat := [88,32,216,66,236,216,234,71,5,245,72,35,129,18,71,20,172,123,6,71,140,38,43,116,171,126,113,15,191,175,154,22]
theorem cast32 : (JFu_PublicDigest22.bytes).map (fun x => x.val)=n32 := by rfl
#print axioms cast32
def n33 : List Nat := [160,226,195,85,172,238,159,46,125,115,20,92,110,239,32,53,237,202,209,58,197,93,226,17,2,64,220,15,44,79,216,68]
theorem cast33 : (JFu_PublicDigest23.bytes).map (fun x => x.val)=n33 := by rfl
#print axioms cast33
def n34 : List Nat := [200,30,70,52,243,39,23,26,152,166,82,94,13,218,247,91,220,133,34,53,173,98,242,48,30,39,144,31,198,63,59,2]
theorem cast34 : (JFu_PublicDigest24.bytes).map (fun x => x.val)=n34 := by rfl
#print axioms cast34
def n35 : List Nat := [106,175,191,66,37,158,165,7,90,100,249,55,169,196,73,39,208,105,65,115,225,12,221,53,127,165,125,70,2,139,87,83]
theorem cast35 : (JFu_PublicDigest25.bytes).map (fun x => x.val)=n35 := by rfl
#print axioms cast35
def n36 : List Nat := [91,58,14,63,187,99,135,67,119,59,89,47,101,175,131,117,35,205,216,74,41,157,59,55,25,182,25,121,21,85,177,120]
theorem cast36 : (JFu_PublicDigest26.bytes).map (fun x => x.val)=n36 := by rfl
#print axioms cast36
def n37 : List Nat := [62,185,11,84,185,239,40,40,161,49,20,56,246,242,89,16,87,146,125,102,5,17,194,100,139,155,28,12,232,192,152,110]
theorem cast37 : (JFu_PublicDigest27.bytes).map (fun x => x.val)=n37 := by rfl
#print axioms cast37
def n38 : List Nat := [72,196,254,85,234,129,207,91,207,92,67,11,242,147,17,6,34,176,68,112,15,75,197,105,67,238,226,77,176,120,113,33]
theorem cast38 : (JFu_PublicDigest28.bytes).map (fun x => x.val)=n38 := by rfl
#print axioms cast38
def n39 : List Nat := [75,25,142,14,189,74,171,58,248,40,123,87,29,243,253,122,132,18,67,105,55,43,137,77,171,212,28,94,67,3,118,44]
theorem cast39 : (JFu_PublicDigest29.bytes).map (fun x => x.val)=n39 := by rfl
#print axioms cast39
def n40 : List Nat := [52,27,32,40,28,234,68,2,163,38,163,86,127,150,231,79,106,166,245,21,72,207,86,109,247,208,24,16,151,176,107,42]
theorem cast40 : (JFu_PublicDigest30.bytes).map (fun x => x.val)=n40 := by rfl
#print axioms cast40
def n41 : List Nat := [251,100,157,1,108,224,214,75,57,61,127,59,232,158,237,86,69,185,229,52,82,167,210,71,84,131,134,51,14,221,0,33]
theorem cast41 : (JFu_PublicDigest31.bytes).map (fun x => x.val)=n41 := by rfl
#print axioms cast41
def n42 : List Nat := [56,88,152,117,59,185,142,73,83,82,62,58,162,134,152,101,189,172,106,96,112,205,110,108,214,96,7,54,101,209,142,98]
theorem cast42 : (JFu_PublicDigest32.bytes).map (fun x => x.val)=n42 := by rfl
#print axioms cast42
def n43 : List Nat := [172,172,239,24,212,157,35,28,253,213,245,51,223,50,229,5,168,87,206,120,18,119,176,89,46,133,70,24,221,119,86,107]
theorem cast43 : (JFu_PublicDigest33.bytes).map (fun x => x.val)=n43 := by rfl
#print axioms cast43
def n44 : List Nat := [56,89,202,58,185,34,92,39,7,78,84,60,134,220,15,27,200,114,222,58,99,41,32,37,26,85,146,68,78,228,75,76]
theorem cast44 : (JFu_PublicDigest34.bytes).map (fun x => x.val)=n44 := by rfl
#print axioms cast44
def n45 : List Nat := [37,76,69,126,125,129,184,101,165,135,222,126,89,61,248,9,14,31,105,24,136,30,222,78,213,153,15,112,216,86,100,122]
theorem cast45 : (JFu_PublicDigest35.bytes).map (fun x => x.val)=n45 := by rfl
#print axioms cast45
def n46 : List Nat := [157,161,135,15,109,191,246,81,23,128,109,94,214,254,99,65,176,172,116,100,254,254,213,63,149,255,253,125,238,33,29,57]
theorem cast46 : (JFu_PublicDigest36.bytes).map (fun x => x.val)=n46 := by rfl
#print axioms cast46
def n47 : List Nat := [17,99,232,73,51,32,40,59,154,101,76,83,245,164,208,27,117,211,126,123,26,114,127,42,70,166,9,122,215,50,38,100]
theorem cast47 : (JFu_PublicDigest37.bytes).map (fun x => x.val)=n47 := by rfl
#print axioms cast47
def n48 : List Nat := [0,105,16,107,224,25,1,111,168,192,126,116,58,110,248,70,121,225,188,21,129,142,204,2,240,239,1,40,149,53,103,72]
theorem cast48 : (JFu_PublicDigest38.bytes).map (fun x => x.val)=n48 := by rfl
#print axioms cast48
def n49 : List Nat := [144,141,57,67,64,122,130,39,252,17,2,5,94,184,79,59,43,116,158,84,243,18,51,117,18,243,231,49,249,200,45,124]
theorem cast49 : (JFu_PublicDigest39.bytes).map (fun x => x.val)=n49 := by rfl
#print axioms cast49
def n50 : List Nat := [182,57,199,78,108,219,165,46,232,179,99,84,222,207,111,4,217,42,70,46,60,243,66,19,57,207,146,25,125,32,124,77]
theorem cast50 : (JFu_PublicDigest40.bytes).map (fun x => x.val)=n50 := by rfl
#print axioms cast50
def n51 : List Nat := [116,183,140,90,100,144,165,73,16,243,160,99,14,89,103,86,213,51,160,32,201,207,159,96,34,247,231,15,83,126,218,26]
theorem cast51 : (JFu_PublicDigest41.bytes).map (fun x => x.val)=n51 := by rfl
#print axioms cast51
def n52 : List Nat := [123,190,39,1,217,63,5,78,38,224,4,15,229,231,69,28,172,155,93,123,197,163,23,111,35,173,17,9,211,192,171,39]
theorem cast52 : (JFu_PublicDigest42.bytes).map (fun x => x.val)=n52 := by rfl
#print axioms cast52
def n53 : List Nat := [28,231,71,207,194,7,229,174,217,138,72,96,252,75,43,9,128,237,40,156,145,10,203,186,121,184,93,22,143,224,121,136]
theorem cast53 : (JFs_Cell04.bytes).map (fun x => x.val)=n53 := by rfl
#print axioms cast53
def n54 : List Nat := [5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5]
theorem cast54 : (JFs_Cell05.bytes).map (fun x => x.val)=n54 := by rfl
#print axioms cast54
def n55 : List Nat := [0]
theorem cast55 : ([0#u8]).map (fun x => x.val)=n55 := by rfl
#print axioms cast55
def n56 : List Nat := [35,84,252,170,237,249,91,67,118,98,250,35,47,53,170,242,180,167,245,80,27,213,106,60,70,25,157,233,56,202,185,163]
theorem cast56 : (root.val).map (fun x => x.val)=n56 := by rfl
#print axioms cast56
def numeric : List Nat := n00 ++ n01 ++ n02 ++ n03 ++ n04 ++ n05 ++ n06 ++ n07 ++ n08 ++ n09 ++ n10 ++ n11 ++ n12 ++ n13 ++ n14 ++ n15 ++ n16 ++ n17 ++ n18 ++ n19 ++ n20 ++ n21 ++ n22 ++ n23 ++ n24 ++ n25 ++ n26 ++ n27 ++ n28 ++ n29 ++ n30 ++ n31 ++ n32 ++ n33 ++ n34 ++ n35 ++ n36 ++ n37 ++ n38 ++ n39 ++ n40 ++ n41 ++ n42 ++ n43 ++ n44 ++ n45 ++ n46 ++ n47 ++ n48 ++ n49 ++ n50 ++ n51 ++ n52 ++ n53 ++ n54 ++ n55 ++ n56
def rest00 : List Nat := n00 ++ n01 ++ n02 ++ n03 ++ n04 ++ n05 ++ n06 ++ n07 ++ n08 ++ n09 ++ n10 ++ n11 ++ n12 ++ n13 ++ n14 ++ n15 ++ n16 ++ n17 ++ n18 ++ n19 ++ n20 ++ n21 ++ n22 ++ n23 ++ n24 ++ n25 ++ n26 ++ n27 ++ n28 ++ n29 ++ n30 ++ n31 ++ n32 ++ n33 ++ n34 ++ n35 ++ n36 ++ n37 ++ n38 ++ n39 ++ n40 ++ n41 ++ n42 ++ n43 ++ n44 ++ n45 ++ n46 ++ n47 ++ n48 ++ n49 ++ n50 ++ n51 ++ n52 ++ n53 ++ n54 ++ n55 ++ n56
def rest01 : List Nat := (n04.drop 20) ++ n05 ++ n06 ++ n07 ++ n08 ++ n09 ++ n10 ++ n11 ++ n12 ++ n13 ++ n14 ++ n15 ++ n16 ++ n17 ++ n18 ++ n19 ++ n20 ++ n21 ++ n22 ++ n23 ++ n24 ++ n25 ++ n26 ++ n27 ++ n28 ++ n29 ++ n30 ++ n31 ++ n32 ++ n33 ++ n34 ++ n35 ++ n36 ++ n37 ++ n38 ++ n39 ++ n40 ++ n41 ++ n42 ++ n43 ++ n44 ++ n45 ++ n46 ++ n47 ++ n48 ++ n49 ++ n50 ++ n51 ++ n52 ++ n53 ++ n54 ++ n55 ++ n56
def rest02 : List Nat := (n08.drop 15) ++ n09 ++ n10 ++ n11 ++ n12 ++ n13 ++ n14 ++ n15 ++ n16 ++ n17 ++ n18 ++ n19 ++ n20 ++ n21 ++ n22 ++ n23 ++ n24 ++ n25 ++ n26 ++ n27 ++ n28 ++ n29 ++ n30 ++ n31 ++ n32 ++ n33 ++ n34 ++ n35 ++ n36 ++ n37 ++ n38 ++ n39 ++ n40 ++ n41 ++ n42 ++ n43 ++ n44 ++ n45 ++ n46 ++ n47 ++ n48 ++ n49 ++ n50 ++ n51 ++ n52 ++ n53 ++ n54 ++ n55 ++ n56
def rest03 : List Nat := (n12.drop 6) ++ n13 ++ n14 ++ n15 ++ n16 ++ n17 ++ n18 ++ n19 ++ n20 ++ n21 ++ n22 ++ n23 ++ n24 ++ n25 ++ n26 ++ n27 ++ n28 ++ n29 ++ n30 ++ n31 ++ n32 ++ n33 ++ n34 ++ n35 ++ n36 ++ n37 ++ n38 ++ n39 ++ n40 ++ n41 ++ n42 ++ n43 ++ n44 ++ n45 ++ n46 ++ n47 ++ n48 ++ n49 ++ n50 ++ n51 ++ n52 ++ n53 ++ n54 ++ n55 ++ n56
def rest04 : List Nat := (n14.drop 6) ++ n15 ++ n16 ++ n17 ++ n18 ++ n19 ++ n20 ++ n21 ++ n22 ++ n23 ++ n24 ++ n25 ++ n26 ++ n27 ++ n28 ++ n29 ++ n30 ++ n31 ++ n32 ++ n33 ++ n34 ++ n35 ++ n36 ++ n37 ++ n38 ++ n39 ++ n40 ++ n41 ++ n42 ++ n43 ++ n44 ++ n45 ++ n46 ++ n47 ++ n48 ++ n49 ++ n50 ++ n51 ++ n52 ++ n53 ++ n54 ++ n55 ++ n56
def rest05 : List Nat := (n16.drop 6) ++ n17 ++ n18 ++ n19 ++ n20 ++ n21 ++ n22 ++ n23 ++ n24 ++ n25 ++ n26 ++ n27 ++ n28 ++ n29 ++ n30 ++ n31 ++ n32 ++ n33 ++ n34 ++ n35 ++ n36 ++ n37 ++ n38 ++ n39 ++ n40 ++ n41 ++ n42 ++ n43 ++ n44 ++ n45 ++ n46 ++ n47 ++ n48 ++ n49 ++ n50 ++ n51 ++ n52 ++ n53 ++ n54 ++ n55 ++ n56
def rest06 : List Nat := (n18.drop 6) ++ n19 ++ n20 ++ n21 ++ n22 ++ n23 ++ n24 ++ n25 ++ n26 ++ n27 ++ n28 ++ n29 ++ n30 ++ n31 ++ n32 ++ n33 ++ n34 ++ n35 ++ n36 ++ n37 ++ n38 ++ n39 ++ n40 ++ n41 ++ n42 ++ n43 ++ n44 ++ n45 ++ n46 ++ n47 ++ n48 ++ n49 ++ n50 ++ n51 ++ n52 ++ n53 ++ n54 ++ n55 ++ n56
def rest07 : List Nat := (n20.drop 6) ++ n21 ++ n22 ++ n23 ++ n24 ++ n25 ++ n26 ++ n27 ++ n28 ++ n29 ++ n30 ++ n31 ++ n32 ++ n33 ++ n34 ++ n35 ++ n36 ++ n37 ++ n38 ++ n39 ++ n40 ++ n41 ++ n42 ++ n43 ++ n44 ++ n45 ++ n46 ++ n47 ++ n48 ++ n49 ++ n50 ++ n51 ++ n52 ++ n53 ++ n54 ++ n55 ++ n56
def rest08 : List Nat := (n22.drop 6) ++ n23 ++ n24 ++ n25 ++ n26 ++ n27 ++ n28 ++ n29 ++ n30 ++ n31 ++ n32 ++ n33 ++ n34 ++ n35 ++ n36 ++ n37 ++ n38 ++ n39 ++ n40 ++ n41 ++ n42 ++ n43 ++ n44 ++ n45 ++ n46 ++ n47 ++ n48 ++ n49 ++ n50 ++ n51 ++ n52 ++ n53 ++ n54 ++ n55 ++ n56
def rest09 : List Nat := (n24.drop 6) ++ n25 ++ n26 ++ n27 ++ n28 ++ n29 ++ n30 ++ n31 ++ n32 ++ n33 ++ n34 ++ n35 ++ n36 ++ n37 ++ n38 ++ n39 ++ n40 ++ n41 ++ n42 ++ n43 ++ n44 ++ n45 ++ n46 ++ n47 ++ n48 ++ n49 ++ n50 ++ n51 ++ n52 ++ n53 ++ n54 ++ n55 ++ n56
def rest10 : List Nat := (n26.drop 6) ++ n27 ++ n28 ++ n29 ++ n30 ++ n31 ++ n32 ++ n33 ++ n34 ++ n35 ++ n36 ++ n37 ++ n38 ++ n39 ++ n40 ++ n41 ++ n42 ++ n43 ++ n44 ++ n45 ++ n46 ++ n47 ++ n48 ++ n49 ++ n50 ++ n51 ++ n52 ++ n53 ++ n54 ++ n55 ++ n56
def rest11 : List Nat := (n28.drop 6) ++ n29 ++ n30 ++ n31 ++ n32 ++ n33 ++ n34 ++ n35 ++ n36 ++ n37 ++ n38 ++ n39 ++ n40 ++ n41 ++ n42 ++ n43 ++ n44 ++ n45 ++ n46 ++ n47 ++ n48 ++ n49 ++ n50 ++ n51 ++ n52 ++ n53 ++ n54 ++ n55 ++ n56
def rest12 : List Nat := (n30.drop 6) ++ n31 ++ n32 ++ n33 ++ n34 ++ n35 ++ n36 ++ n37 ++ n38 ++ n39 ++ n40 ++ n41 ++ n42 ++ n43 ++ n44 ++ n45 ++ n46 ++ n47 ++ n48 ++ n49 ++ n50 ++ n51 ++ n52 ++ n53 ++ n54 ++ n55 ++ n56
def rest13 : List Nat := (n32.drop 6) ++ n33 ++ n34 ++ n35 ++ n36 ++ n37 ++ n38 ++ n39 ++ n40 ++ n41 ++ n42 ++ n43 ++ n44 ++ n45 ++ n46 ++ n47 ++ n48 ++ n49 ++ n50 ++ n51 ++ n52 ++ n53 ++ n54 ++ n55 ++ n56
def rest14 : List Nat := (n34.drop 6) ++ n35 ++ n36 ++ n37 ++ n38 ++ n39 ++ n40 ++ n41 ++ n42 ++ n43 ++ n44 ++ n45 ++ n46 ++ n47 ++ n48 ++ n49 ++ n50 ++ n51 ++ n52 ++ n53 ++ n54 ++ n55 ++ n56
def rest15 : List Nat := (n36.drop 6) ++ n37 ++ n38 ++ n39 ++ n40 ++ n41 ++ n42 ++ n43 ++ n44 ++ n45 ++ n46 ++ n47 ++ n48 ++ n49 ++ n50 ++ n51 ++ n52 ++ n53 ++ n54 ++ n55 ++ n56
def rest16 : List Nat := (n38.drop 6) ++ n39 ++ n40 ++ n41 ++ n42 ++ n43 ++ n44 ++ n45 ++ n46 ++ n47 ++ n48 ++ n49 ++ n50 ++ n51 ++ n52 ++ n53 ++ n54 ++ n55 ++ n56
def rest17 : List Nat := (n40.drop 6) ++ n41 ++ n42 ++ n43 ++ n44 ++ n45 ++ n46 ++ n47 ++ n48 ++ n49 ++ n50 ++ n51 ++ n52 ++ n53 ++ n54 ++ n55 ++ n56
def rest18 : List Nat := (n42.drop 6) ++ n43 ++ n44 ++ n45 ++ n46 ++ n47 ++ n48 ++ n49 ++ n50 ++ n51 ++ n52 ++ n53 ++ n54 ++ n55 ++ n56
def rest19 : List Nat := (n44.drop 6) ++ n45 ++ n46 ++ n47 ++ n48 ++ n49 ++ n50 ++ n51 ++ n52 ++ n53 ++ n54 ++ n55 ++ n56
def rest20 : List Nat := (n46.drop 6) ++ n47 ++ n48 ++ n49 ++ n50 ++ n51 ++ n52 ++ n53 ++ n54 ++ n55 ++ n56
def rest21 : List Nat := (n48.drop 6) ++ n49 ++ n50 ++ n51 ++ n52 ++ n53 ++ n54 ++ n55 ++ n56
def rest22 : List Nat := (n50.drop 6) ++ n51 ++ n52 ++ n53 ++ n54 ++ n55 ++ n56
def rest23 : List Nat := (n52.drop 6) ++ n53 ++ n54 ++ n55 ++ n56
def rest24 : List Nat := (n54.drop 6) ++ n55 ++ n56
theorem step00 : rest00=JFp_SHABlock00.input ++ rest01 := by
  simp only [rest00,rest01,n00,n01,n02,n03,n04]
  rfl
#print axioms step00
theorem step01 : rest01=JFp_SHABlock01.input ++ rest02 := by
  simp only [rest01,rest02,n04,n05,n06,n07,n08]
  rfl
#print axioms step01
theorem step02 : rest02=JFp_SHABlock02.input ++ rest03 := by
  simp only [rest02,rest03,n08,n09,n10,n11,n12]
  rfl
#print axioms step02
theorem step03 : rest03=JFp_SHABlock03.input ++ rest04 := by
  simp only [rest03,rest04,n12,n13,n14]
  rfl
#print axioms step03
theorem step04 : rest04=JFp_SHABlock04.input ++ rest05 := by
  simp only [rest04,rest05,n14,n15,n16]
  rfl
#print axioms step04
theorem step05 : rest05=JFp_SHABlock05.input ++ rest06 := by
  simp only [rest05,rest06,n16,n17,n18]
  rfl
#print axioms step05
theorem step06 : rest06=JFp_SHABlock06.input ++ rest07 := by
  simp only [rest06,rest07,n18,n19,n20]
  rfl
#print axioms step06
theorem step07 : rest07=JFp_SHABlock07.input ++ rest08 := by
  simp only [rest07,rest08,n20,n21,n22]
  rfl
#print axioms step07
theorem step08 : rest08=JFp_SHABlock08.input ++ rest09 := by
  simp only [rest08,rest09,n22,n23,n24]
  rfl
#print axioms step08
theorem step09 : rest09=JFp_SHABlock09.input ++ rest10 := by
  simp only [rest09,rest10,n24,n25,n26]
  rfl
#print axioms step09
theorem step10 : rest10=JFp_SHABlock10.input ++ rest11 := by
  simp only [rest10,rest11,n26,n27,n28]
  rfl
#print axioms step10
theorem step11 : rest11=JFp_SHABlock11.input ++ rest12 := by
  simp only [rest11,rest12,n28,n29,n30]
  rfl
#print axioms step11
theorem step12 : rest12=JFp_SHABlock12.input ++ rest13 := by
  simp only [rest12,rest13,n30,n31,n32]
  rfl
#print axioms step12
theorem step13 : rest13=JFp_SHABlock13.input ++ rest14 := by
  simp only [rest13,rest14,n32,n33,n34]
  rfl
#print axioms step13
theorem step14 : rest14=JFp_SHABlock14.input ++ rest15 := by
  simp only [rest14,rest15,n34,n35,n36]
  rfl
#print axioms step14
theorem step15 : rest15=JFp_SHABlock15.input ++ rest16 := by
  simp only [rest15,rest16,n36,n37,n38]
  rfl
#print axioms step15
theorem step16 : rest16=JFp_SHABlock16.input ++ rest17 := by
  simp only [rest16,rest17,n38,n39,n40]
  rfl
#print axioms step16
theorem step17 : rest17=JFp_SHABlock17.input ++ rest18 := by
  simp only [rest17,rest18,n40,n41,n42]
  rfl
#print axioms step17
theorem step18 : rest18=JFp_SHABlock18.input ++ rest19 := by
  simp only [rest18,rest19,n42,n43,n44]
  rfl
#print axioms step18
theorem step19 : rest19=JFp_SHABlock19.input ++ rest20 := by
  simp only [rest19,rest20,n44,n45,n46]
  rfl
#print axioms step19
theorem step20 : rest20=JFp_SHABlock20.input ++ rest21 := by
  simp only [rest20,rest21,n46,n47,n48]
  rfl
#print axioms step20
theorem step21 : rest21=JFp_SHABlock21.input ++ rest22 := by
  simp only [rest21,rest22,n48,n49,n50]
  rfl
#print axioms step21
theorem step22 : rest22=JFp_SHABlock22.input ++ rest23 := by
  simp only [rest22,rest23,n50,n51,n52]
  rfl
#print axioms step22
theorem step23 : rest23=JFp_SHABlock23.input ++ rest24 := by
  simp only [rest23,rest24,n52,n53,n54]
  rfl
#print axioms step23
theorem last : rest24=JFp_SeedHash.tail := by
  simp only [rest24,n54,n55,n56]
  rfl
#print axioms last
theorem regroup : numeric=JFp_SeedHash.raw := by
  change rest00=JFp_SeedHash.raw
  rw [step00,step01,step02,step03,step04,step05,step06,step07,step08,step09,step10,step11,step12,step13,step14,step15,step16,step17,step18,step19,step20,step21,step22,step23,last]
  simp only [JFp_SeedHash.raw,JFp_SeedHash.head,List.flatten_cons,List.flatten_nil,List.append_nil,List.append_assoc]
#print axioms regroup
theorem native :
    (flatten (TranscriptStep.initParts (alloc.vec.Vec.deref JFs_ExactSerialization.encoded) root 1520#u32)).map Fin.val = numeric := by
  simp only [flatten,TranscriptStep.initParts,Array.to_slice,Array.make,List.flatMap_cons,List.flatMap_nil,
    List.map_append,List.append_nil,List.append_assoc,alloc.vec.Vec.deref,JFs_ExactSerialization.encoded,
    JFs_SerializedBytes.bytes,JFs_SerializedBytes.chunks,id_eq,
    List.map_map,Function.comp_def,decodeByte,
    cast00,    cast01,    cast02,    cast03,    cast04,    cast05,    cast06,    cast07,    cast08,    cast09,    cast10,    cast11,    cast12,    cast13,    cast14,    cast15,    cast16,    cast17,    cast18,    cast19,    cast20,    cast21,    cast22,    cast23,    cast24,    cast25,    cast26,    cast27,    cast28,    cast29,    cast30,    cast31,    cast32,    cast33,    cast34,    cast35,    cast36,    cast37,    cast38,    cast39,    cast40,    cast41,    cast42,    cast43,    cast44,    cast45,    cast46,    cast47,    cast48,    cast49,    cast50,    cast51,    cast52,    cast53,    cast54,    cast55,    cast56,numeric]
  simp only [n01,n03,n10]
#print axioms native
end AspisR1.JFp_InitBytes
