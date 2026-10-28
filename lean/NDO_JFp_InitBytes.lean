import NDO_JFs_ExactInitialization
import NDO_JFp_SeedHash
set_option autoImplicit false
namespace AspisR1.JFp_InitBytes
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisR1PublicPreparation
def root : Array U8 32#usize := ⟨[154#u8,186#u8,129#u8,123#u8,118#u8,141#u8,34#u8,107#u8,41#u8,162#u8,65#u8,31#u8,231#u8,186#u8,247#u8,183#u8,176#u8,78#u8,206#u8,66#u8,178#u8,115#u8,221#u8,182#u8,126#u8,10#u8,44#u8,98#u8,98#u8,19#u8,142#u8,75#u8],by rfl⟩
def n00 : List Nat := [85,78,80,82,79,86,69,68,58,82,49,58,80,82,73,86,65,84,69,45,83,65,76,84,69,68,58,83,69,77,65,78,84,73,67,58,80,51]
theorem cast00 : (AspisR1PublicPreparation.r1_wire.DOMAIN.val).map (fun x => x.val)=n00 := by
  simp only [r1_wire.DOMAIN,Array.make]
  rfl
#print axioms cast00
def n01 : List Nat := [0]
theorem cast01 : ([0#u8]).map (fun x => x.val)=n01 := by rfl
#print axioms cast01
def n02 : List Nat := [175,5,0,0]
theorem cast02 : ((core.num.U32.to_le_bytes 1455#u32).val).map (fun x => x.val)=n02 := by
  simp [core.num.U32.to_le_bytes,BitVec.toLEBytes,n02] <;> (repeat' constructor) <;> scalar_tac
#print axioms cast02
def n03 : List Nat := [0]
theorem cast03 : ([0#u8]).map (fun x => x.val)=n03 := by rfl
#print axioms cast03
def n04 : List Nat := [85,246,62,4,159,80,117,33,221,239,128,120,216,131,141,49,99,239,102,35,253,148,147,6,128,120,67,103,86,177,157,56]
theorem cast04 : (JFu_PublicDigest43.bytes).map (fun x => x.val)=n04 := by rfl
#print axioms cast04
def n05 : List Nat := [219,27,130,0,76,144,137,6,20,96,178,97,164,37,6,0,128,143,218,112,162,164,176,20,25,186,192,19,209,175,110,117]
theorem cast05 : (JFu_PublicDigest44.bytes).map (fun x => x.val)=n05 := by rfl
#print axioms cast05
def n06 : List Nat := [77,0,0,0]
theorem cast06 : ([77#u8,0#u8,0#u8,0#u8]).map (fun x => x.val)=n06 := by rfl
#print axioms cast06
def n07 : List Nat := [1]
theorem cast07 : ([1#u8]).map (fun x => x.val)=n07 := by rfl
#print axioms cast07
def n08 : List Nat := [38,95,6,86,21,144,64,23,144,38,14,44,19,44,204,114,34,164,10,25,49,167,186,47,31,240,152,56,72,124,118,4]
theorem cast08 : (JFu_PublicDigest45.bytes).map (fun x => x.val)=n08 := by rfl
#print axioms cast08
def n09 : List Nat := [35,21,136,6,65,19,78,120,113,38,13,70,250,49,224,32,8,134,48,23,1,83,145,33,35,192,81,85,205,25,236,20]
theorem cast09 : (JFu_PublicDigest46.bytes).map (fun x => x.val)=n09 := by rfl
#print axioms cast09
def n10 : List Nat := [0]
theorem cast10 : ([0#u8]).map (fun x => x.val)=n10 := by rfl
#print axioms cast10
def n11 : List Nat := [13,0,0,0,0,0,0,0]
theorem cast11 : ([13#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]).map (fun x => x.val)=n11 := by rfl
#print axioms cast11
def n12 : List Nat := [160,79,0,0,177,79,0,0,194,79,0,0,211,79,0,0,228,79,0,0,245,79,0,0,6,80,0,0,23,80,0,0]
theorem cast12 : (JFu_PublicDigest02.bytes).map (fun x => x.val)=n12 := by rfl
#print axioms cast12
def n13 : List Nat := [235,242,112,8,230,167,79,86,213,99,65,31,155,22,230,115,109,214,51,109,67,248,134,34,158,228,215,44,40,233,227,61]
theorem cast13 : (JFu_PublicDigest03.bytes).map (fun x => x.val)=n13 := by rfl
#print axioms cast13
def n14 : List Nat := [255,87,97,33,138,206,138,6,157,239,19,123,225,92,150,20,2,84,103,72,62,69,216,21,199,140,96,27,54,40,170,28]
theorem cast14 : (JFu_PublicDigest04.bytes).map (fun x => x.val)=n14 := by rfl
#print axioms cast14
def n15 : List Nat := [220,22,145,95,145,152,13,74,123,196,190,68,229,88,119,23,151,91,145,42,200,68,213,124,141,247,83,3,10,128,152,39]
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
def n32 : List Nat := [167,109,5,4,105,45,206,127,141,222,107,69,19,82,79,119,84,239,213,5,32,122,227,48,149,245,183,42,194,74,254,7]
theorem cast32 : (JFu_PublicDigest22.bytes).map (fun x => x.val)=n32 := by rfl
#print axioms cast32
def n33 : List Nat := [160,226,195,85,172,238,159,46,125,115,20,92,110,239,32,53,237,202,209,58,197,93,226,17,2,64,220,15,44,79,216,68]
theorem cast33 : (JFu_PublicDigest23.bytes).map (fun x => x.val)=n33 := by rfl
#print axioms cast33
def n34 : List Nat := [69,94,200,14,78,105,149,11,53,53,173,25,27,249,226,29,214,163,151,37,15,219,131,114,62,124,191,72,119,170,167,59]
theorem cast34 : (JFu_PublicDigest24.bytes).map (fun x => x.val)=n34 := by rfl
#print axioms cast34
def n35 : List Nat := [255,87,97,33,138,206,138,6,157,239,19,123,225,92,150,20,2,84,103,72,62,69,216,21,199,140,96,27,54,40,170,28]
theorem cast35 : (JFu_PublicDigest25.bytes).map (fun x => x.val)=n35 := by rfl
#print axioms cast35
def n36 : List Nat := [220,22,145,95,145,152,13,74,123,196,190,68,229,88,119,23,151,91,145,42,200,68,213,124,141,247,83,3,10,128,152,39]
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
def n53 : List Nat := [154,186,129,123,118,141,34,107,41,162,65,31,231,186,247,183,176,78,206,66,178,115,221,182,126,10,44,98,98,19,142,75]
theorem cast53 : (root.val).map (fun x => x.val)=n53 := by rfl
#print axioms cast53
def numeric : List Nat := n00 ++ n01 ++ n02 ++ n03 ++ n04 ++ n05 ++ n06 ++ n07 ++ n08 ++ n09 ++ n10 ++ n11 ++ n12 ++ n13 ++ n14 ++ n15 ++ n16 ++ n17 ++ n18 ++ n19 ++ n20 ++ n21 ++ n22 ++ n23 ++ n24 ++ n25 ++ n26 ++ n27 ++ n28 ++ n29 ++ n30 ++ n31 ++ n32 ++ n33 ++ n34 ++ n35 ++ n36 ++ n37 ++ n38 ++ n39 ++ n40 ++ n41 ++ n42 ++ n43 ++ n44 ++ n45 ++ n46 ++ n47 ++ n48 ++ n49 ++ n50 ++ n51 ++ n52 ++ n53
def rest00 : List Nat := n00 ++ n01 ++ n02 ++ n03 ++ n04 ++ n05 ++ n06 ++ n07 ++ n08 ++ n09 ++ n10 ++ n11 ++ n12 ++ n13 ++ n14 ++ n15 ++ n16 ++ n17 ++ n18 ++ n19 ++ n20 ++ n21 ++ n22 ++ n23 ++ n24 ++ n25 ++ n26 ++ n27 ++ n28 ++ n29 ++ n30 ++ n31 ++ n32 ++ n33 ++ n34 ++ n35 ++ n36 ++ n37 ++ n38 ++ n39 ++ n40 ++ n41 ++ n42 ++ n43 ++ n44 ++ n45 ++ n46 ++ n47 ++ n48 ++ n49 ++ n50 ++ n51 ++ n52 ++ n53
def rest01 : List Nat := (n04.drop 20) ++ n05 ++ n06 ++ n07 ++ n08 ++ n09 ++ n10 ++ n11 ++ n12 ++ n13 ++ n14 ++ n15 ++ n16 ++ n17 ++ n18 ++ n19 ++ n20 ++ n21 ++ n22 ++ n23 ++ n24 ++ n25 ++ n26 ++ n27 ++ n28 ++ n29 ++ n30 ++ n31 ++ n32 ++ n33 ++ n34 ++ n35 ++ n36 ++ n37 ++ n38 ++ n39 ++ n40 ++ n41 ++ n42 ++ n43 ++ n44 ++ n45 ++ n46 ++ n47 ++ n48 ++ n49 ++ n50 ++ n51 ++ n52 ++ n53
def rest02 : List Nat := (n08.drop 15) ++ n09 ++ n10 ++ n11 ++ n12 ++ n13 ++ n14 ++ n15 ++ n16 ++ n17 ++ n18 ++ n19 ++ n20 ++ n21 ++ n22 ++ n23 ++ n24 ++ n25 ++ n26 ++ n27 ++ n28 ++ n29 ++ n30 ++ n31 ++ n32 ++ n33 ++ n34 ++ n35 ++ n36 ++ n37 ++ n38 ++ n39 ++ n40 ++ n41 ++ n42 ++ n43 ++ n44 ++ n45 ++ n46 ++ n47 ++ n48 ++ n49 ++ n50 ++ n51 ++ n52 ++ n53
def rest03 : List Nat := (n12.drop 6) ++ n13 ++ n14 ++ n15 ++ n16 ++ n17 ++ n18 ++ n19 ++ n20 ++ n21 ++ n22 ++ n23 ++ n24 ++ n25 ++ n26 ++ n27 ++ n28 ++ n29 ++ n30 ++ n31 ++ n32 ++ n33 ++ n34 ++ n35 ++ n36 ++ n37 ++ n38 ++ n39 ++ n40 ++ n41 ++ n42 ++ n43 ++ n44 ++ n45 ++ n46 ++ n47 ++ n48 ++ n49 ++ n50 ++ n51 ++ n52 ++ n53
def rest04 : List Nat := (n14.drop 6) ++ n15 ++ n16 ++ n17 ++ n18 ++ n19 ++ n20 ++ n21 ++ n22 ++ n23 ++ n24 ++ n25 ++ n26 ++ n27 ++ n28 ++ n29 ++ n30 ++ n31 ++ n32 ++ n33 ++ n34 ++ n35 ++ n36 ++ n37 ++ n38 ++ n39 ++ n40 ++ n41 ++ n42 ++ n43 ++ n44 ++ n45 ++ n46 ++ n47 ++ n48 ++ n49 ++ n50 ++ n51 ++ n52 ++ n53
def rest05 : List Nat := (n16.drop 6) ++ n17 ++ n18 ++ n19 ++ n20 ++ n21 ++ n22 ++ n23 ++ n24 ++ n25 ++ n26 ++ n27 ++ n28 ++ n29 ++ n30 ++ n31 ++ n32 ++ n33 ++ n34 ++ n35 ++ n36 ++ n37 ++ n38 ++ n39 ++ n40 ++ n41 ++ n42 ++ n43 ++ n44 ++ n45 ++ n46 ++ n47 ++ n48 ++ n49 ++ n50 ++ n51 ++ n52 ++ n53
def rest06 : List Nat := (n18.drop 6) ++ n19 ++ n20 ++ n21 ++ n22 ++ n23 ++ n24 ++ n25 ++ n26 ++ n27 ++ n28 ++ n29 ++ n30 ++ n31 ++ n32 ++ n33 ++ n34 ++ n35 ++ n36 ++ n37 ++ n38 ++ n39 ++ n40 ++ n41 ++ n42 ++ n43 ++ n44 ++ n45 ++ n46 ++ n47 ++ n48 ++ n49 ++ n50 ++ n51 ++ n52 ++ n53
def rest07 : List Nat := (n20.drop 6) ++ n21 ++ n22 ++ n23 ++ n24 ++ n25 ++ n26 ++ n27 ++ n28 ++ n29 ++ n30 ++ n31 ++ n32 ++ n33 ++ n34 ++ n35 ++ n36 ++ n37 ++ n38 ++ n39 ++ n40 ++ n41 ++ n42 ++ n43 ++ n44 ++ n45 ++ n46 ++ n47 ++ n48 ++ n49 ++ n50 ++ n51 ++ n52 ++ n53
def rest08 : List Nat := (n22.drop 6) ++ n23 ++ n24 ++ n25 ++ n26 ++ n27 ++ n28 ++ n29 ++ n30 ++ n31 ++ n32 ++ n33 ++ n34 ++ n35 ++ n36 ++ n37 ++ n38 ++ n39 ++ n40 ++ n41 ++ n42 ++ n43 ++ n44 ++ n45 ++ n46 ++ n47 ++ n48 ++ n49 ++ n50 ++ n51 ++ n52 ++ n53
def rest09 : List Nat := (n24.drop 6) ++ n25 ++ n26 ++ n27 ++ n28 ++ n29 ++ n30 ++ n31 ++ n32 ++ n33 ++ n34 ++ n35 ++ n36 ++ n37 ++ n38 ++ n39 ++ n40 ++ n41 ++ n42 ++ n43 ++ n44 ++ n45 ++ n46 ++ n47 ++ n48 ++ n49 ++ n50 ++ n51 ++ n52 ++ n53
def rest10 : List Nat := (n26.drop 6) ++ n27 ++ n28 ++ n29 ++ n30 ++ n31 ++ n32 ++ n33 ++ n34 ++ n35 ++ n36 ++ n37 ++ n38 ++ n39 ++ n40 ++ n41 ++ n42 ++ n43 ++ n44 ++ n45 ++ n46 ++ n47 ++ n48 ++ n49 ++ n50 ++ n51 ++ n52 ++ n53
def rest11 : List Nat := (n28.drop 6) ++ n29 ++ n30 ++ n31 ++ n32 ++ n33 ++ n34 ++ n35 ++ n36 ++ n37 ++ n38 ++ n39 ++ n40 ++ n41 ++ n42 ++ n43 ++ n44 ++ n45 ++ n46 ++ n47 ++ n48 ++ n49 ++ n50 ++ n51 ++ n52 ++ n53
def rest12 : List Nat := (n30.drop 6) ++ n31 ++ n32 ++ n33 ++ n34 ++ n35 ++ n36 ++ n37 ++ n38 ++ n39 ++ n40 ++ n41 ++ n42 ++ n43 ++ n44 ++ n45 ++ n46 ++ n47 ++ n48 ++ n49 ++ n50 ++ n51 ++ n52 ++ n53
def rest13 : List Nat := (n32.drop 6) ++ n33 ++ n34 ++ n35 ++ n36 ++ n37 ++ n38 ++ n39 ++ n40 ++ n41 ++ n42 ++ n43 ++ n44 ++ n45 ++ n46 ++ n47 ++ n48 ++ n49 ++ n50 ++ n51 ++ n52 ++ n53
def rest14 : List Nat := (n34.drop 6) ++ n35 ++ n36 ++ n37 ++ n38 ++ n39 ++ n40 ++ n41 ++ n42 ++ n43 ++ n44 ++ n45 ++ n46 ++ n47 ++ n48 ++ n49 ++ n50 ++ n51 ++ n52 ++ n53
def rest15 : List Nat := (n36.drop 6) ++ n37 ++ n38 ++ n39 ++ n40 ++ n41 ++ n42 ++ n43 ++ n44 ++ n45 ++ n46 ++ n47 ++ n48 ++ n49 ++ n50 ++ n51 ++ n52 ++ n53
def rest16 : List Nat := (n38.drop 6) ++ n39 ++ n40 ++ n41 ++ n42 ++ n43 ++ n44 ++ n45 ++ n46 ++ n47 ++ n48 ++ n49 ++ n50 ++ n51 ++ n52 ++ n53
def rest17 : List Nat := (n40.drop 6) ++ n41 ++ n42 ++ n43 ++ n44 ++ n45 ++ n46 ++ n47 ++ n48 ++ n49 ++ n50 ++ n51 ++ n52 ++ n53
def rest18 : List Nat := (n42.drop 6) ++ n43 ++ n44 ++ n45 ++ n46 ++ n47 ++ n48 ++ n49 ++ n50 ++ n51 ++ n52 ++ n53
def rest19 : List Nat := (n44.drop 6) ++ n45 ++ n46 ++ n47 ++ n48 ++ n49 ++ n50 ++ n51 ++ n52 ++ n53
def rest20 : List Nat := (n46.drop 6) ++ n47 ++ n48 ++ n49 ++ n50 ++ n51 ++ n52 ++ n53
def rest21 : List Nat := (n48.drop 6) ++ n49 ++ n50 ++ n51 ++ n52 ++ n53
def rest22 : List Nat := (n50.drop 6) ++ n51 ++ n52 ++ n53
def rest23 : List Nat := (n52.drop 6) ++ n53
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
theorem last : rest23=JFp_SeedHash.tail := by
  simp only [rest23,n51,n52,n53]
  rfl
#print axioms last
theorem regroup : numeric=JFp_SeedHash.raw := by
  change rest00=JFp_SeedHash.raw
  rw [step00,step01,step02,step03,step04,step05,step06,step07,step08,step09,step10,step11,step12,step13,step14,step15,step16,step17,step18,step19,step20,step21,step22,last]
  simp only [JFp_SeedHash.raw,JFp_SeedHash.head,List.flatten_cons,List.flatten_nil,List.append_nil,List.append_assoc]
#print axioms regroup
theorem native :
    (flatten (TranscriptStep.initParts (alloc.vec.Vec.deref JFs_ExactSerialization.encoded) root 1455#u32)).map Fin.val = numeric := by
  simp only [flatten,TranscriptStep.initParts,Array.to_slice,Array.make,List.flatMap_cons,List.flatMap_nil,
    List.map_append,List.append_nil,List.append_assoc,alloc.vec.Vec.deref,JFs_ExactSerialization.encoded,
    JFs_SerializedBytes.bytes,JFs_SerializedBytes.chunks,id_eq,
    List.map_map,Function.comp_def,decodeByte,
    cast00,    cast01,    cast02,    cast03,    cast04,    cast05,    cast06,    cast07,    cast08,    cast09,    cast10,    cast11,    cast12,    cast13,    cast14,    cast15,    cast16,    cast17,    cast18,    cast19,    cast20,    cast21,    cast22,    cast23,    cast24,    cast25,    cast26,    cast27,    cast28,    cast29,    cast30,    cast31,    cast32,    cast33,    cast34,    cast35,    cast36,    cast37,    cast38,    cast39,    cast40,    cast41,    cast42,    cast43,    cast44,    cast45,    cast46,    cast47,    cast48,    cast49,    cast50,    cast51,    cast52,    cast53,numeric]
  simp only [n01,n03,n10]
#print axioms native
end AspisR1.JFp_InitBytes
