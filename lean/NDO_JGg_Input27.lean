import NDO_JGe_Payload27
import NDO_JGe_Q27Absorb
import NDO_JGe_OpeningInit
set_option autoImplicit false
namespace AspisR1.JGg_Input27
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open JGe_Window27
def before : State := JGe_OpeningInit.state
def payload : Slice U8 := JGe_Payload27.value
def n00 : List Nat := [71,158,156,223,196,59,228,42,63,10,79,20,162,20,64,13,61,75,124,237,11,37,245,58,18,39,252,119,142,89,193,123,0,187,160,3,0,0]
def n01 : List Nat := [34,194,187,46,77,91,113,104,129,133,219,40,197,161,69,71,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def n02 : List Nat := [72,132,161,5,145,155,80,48,181,166,23,94,46,11,39,116,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def n03 : List Nat := [148,62,130,121,55,9,143,40,145,201,103,29,96,88,145,24,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def n04 : List Nat := [130,91,96,22,222,172,0,56,249,244,137,42,169,229,6,67,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def n05 : List Nat := [23,160,4,126,44,204,162,18,248,86,90,108,219,182,34,114,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def n06 : List Nat := [225,36,87,53,174,189,128,106,7,123,178,91,109,253,228,33,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def n07 : List Nat := [221,137,3,66,212,39,192,8,250,231,100,36,11,45,15,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def n08 : List Nat := [213,61,44,75,85,38,92,14,39,71,243,61,158,121,109,18,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def n09 : List Nat := [93,160,19,21,234,7,171,61,146,221,114,28,37,168,119,46,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def n10 : List Nat := [186,190,88,96,227,57,148,65,181,174,156,25,80,161,252,36,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def n11 : List Nat := [179,227,216,115,107,30,42,90,30,186,122,97,100,85,149,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def n12 : List Nat := [156,226,232,37,141,175,231,19,154,163,133,78,210,210,119,73,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def n13 : List Nat := [156,130,139,110,109,177,253,37,54,100,66,4,195,114,105,16,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def n14 : List Nat := [44,214,249,118,214,186,0,1,123,81,156,103,42,0,182,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def n15 : List Nat := [16,146,47,0,167,9,193,19,65,138,102,117,218,229,69,86,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def n16 : List Nat := [237,195,240,13,85,148,114,23,251,177,99,124,176,183,252,120,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def n17 : List Nat := [215,23,94,114,124,36,215,72,56,117,255,47,63,185,57,118,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def n18 : List Nat := [71,32,40,76,80,212,95,14,167,150,210,14,253,69,115,68,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def n19 : List Nat := [225,240,228,101,91,30,37,110,239,34,238,46,34,14,48,94,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def n20 : List Nat := [245,64,186,37,127,205,219,92,24,193,230,94,24,216,188,58,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def n21 : List Nat := [39,3,9,72,195,213,189,16,30,220,173,16,185,187,23,70,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def n22 : List Nat := [116,100,1,113,177,113,1,98,31,30,193,17,234,47,241,48,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def n23 : List Nat := [125,151,107,55,211,19,7,116,21,177,142,45,237,130,62,10,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def n24 : List Nat := [220,113,195,62,103,111,155,73,103,118,122,44,214,251,171,54,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def n25 : List Nat := [27,94,179,81,49,89,173,87,247,194,181,48,202,96,12,122,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def n26 : List Nat := [150,5,36,4,215,118,233,44,21,253,238,29,85,232,143,113,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def n27 : List Nat := [211,78,148,68,1,255,57,89,177,62,97,100,117,69,14,117,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def n28 : List Nat := [111,146,53,39,205,39,212,116,202,244,6,32,234,183,192,84,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def n29 : List Nat := [132,34,205,24,61,12,127,6,218,51,141,7,13,180,50,85,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem cast00 : c00.map (fun x=>x.val) ++ (List.replicate 16 0#u8).map (fun x=>x.val)=n01 := by rfl
#print axioms cast00
theorem cast01 : c01.map (fun x=>x.val) ++ (List.replicate 16 0#u8).map (fun x=>x.val)=n02 := by rfl
#print axioms cast01
theorem cast02 : c02.map (fun x=>x.val) ++ (List.replicate 16 0#u8).map (fun x=>x.val)=n03 := by rfl
#print axioms cast02
theorem cast03 : c03.map (fun x=>x.val) ++ (List.replicate 16 0#u8).map (fun x=>x.val)=n04 := by rfl
#print axioms cast03
theorem cast04 : c04.map (fun x=>x.val) ++ (List.replicate 16 0#u8).map (fun x=>x.val)=n05 := by rfl
#print axioms cast04
theorem cast05 : c05.map (fun x=>x.val) ++ (List.replicate 16 0#u8).map (fun x=>x.val)=n06 := by rfl
#print axioms cast05
theorem cast06 : c06.map (fun x=>x.val) ++ (List.replicate 16 0#u8).map (fun x=>x.val)=n07 := by rfl
#print axioms cast06
theorem cast07 : c07.map (fun x=>x.val) ++ (List.replicate 16 0#u8).map (fun x=>x.val)=n08 := by rfl
#print axioms cast07
theorem cast08 : c08.map (fun x=>x.val) ++ (List.replicate 16 0#u8).map (fun x=>x.val)=n09 := by rfl
#print axioms cast08
theorem cast09 : c09.map (fun x=>x.val) ++ (List.replicate 16 0#u8).map (fun x=>x.val)=n10 := by rfl
#print axioms cast09
theorem cast10 : c10.map (fun x=>x.val) ++ (List.replicate 16 0#u8).map (fun x=>x.val)=n11 := by rfl
#print axioms cast10
theorem cast11 : c11.map (fun x=>x.val) ++ (List.replicate 16 0#u8).map (fun x=>x.val)=n12 := by rfl
#print axioms cast11
theorem cast12 : c12.map (fun x=>x.val) ++ (List.replicate 16 0#u8).map (fun x=>x.val)=n13 := by rfl
#print axioms cast12
theorem cast13 : c13.map (fun x=>x.val) ++ (List.replicate 16 0#u8).map (fun x=>x.val)=n14 := by rfl
#print axioms cast13
theorem cast14 : c14.map (fun x=>x.val) ++ (List.replicate 16 0#u8).map (fun x=>x.val)=n15 := by rfl
#print axioms cast14
theorem cast15 : c15.map (fun x=>x.val) ++ (List.replicate 16 0#u8).map (fun x=>x.val)=n16 := by rfl
#print axioms cast15
theorem cast16 : c16.map (fun x=>x.val) ++ (List.replicate 16 0#u8).map (fun x=>x.val)=n17 := by rfl
#print axioms cast16
theorem cast17 : c17.map (fun x=>x.val) ++ (List.replicate 16 0#u8).map (fun x=>x.val)=n18 := by rfl
#print axioms cast17
theorem cast18 : c18.map (fun x=>x.val) ++ (List.replicate 16 0#u8).map (fun x=>x.val)=n19 := by rfl
#print axioms cast18
theorem cast19 : c19.map (fun x=>x.val) ++ (List.replicate 16 0#u8).map (fun x=>x.val)=n20 := by rfl
#print axioms cast19
theorem cast20 : c20.map (fun x=>x.val) ++ (List.replicate 16 0#u8).map (fun x=>x.val)=n21 := by rfl
#print axioms cast20
theorem cast21 : c21.map (fun x=>x.val) ++ (List.replicate 16 0#u8).map (fun x=>x.val)=n22 := by rfl
#print axioms cast21
theorem cast22 : c22.map (fun x=>x.val) ++ (List.replicate 16 0#u8).map (fun x=>x.val)=n23 := by rfl
#print axioms cast22
theorem cast23 : c23.map (fun x=>x.val) ++ (List.replicate 16 0#u8).map (fun x=>x.val)=n24 := by rfl
#print axioms cast23
theorem cast24 : c24.map (fun x=>x.val) ++ (List.replicate 16 0#u8).map (fun x=>x.val)=n25 := by rfl
#print axioms cast24
theorem cast25 : c25.map (fun x=>x.val) ++ (List.replicate 16 0#u8).map (fun x=>x.val)=n26 := by rfl
#print axioms cast25
theorem cast26 : c26.map (fun x=>x.val) ++ (List.replicate 16 0#u8).map (fun x=>x.val)=n27 := by rfl
#print axioms cast26
theorem cast27 : c27.map (fun x=>x.val) ++ (List.replicate 16 0#u8).map (fun x=>x.val)=n28 := by rfl
#print axioms cast27
theorem cast28 : c28.map (fun x=>x.val) ++ (List.replicate 16 0#u8).map (fun x=>x.val)=n29 := by rfl
#print axioms cast28
theorem payloadNat : payload.val.map (fun x=>x.val)=n01 ++ n02 ++ n03 ++ n04 ++ n05 ++ n06 ++ n07 ++ n08 ++ n09 ++ n10 ++ n11 ++ n12 ++ n13 ++ n14 ++ n15 ++ n16 ++ n17 ++ n18 ++ n19 ++ n20 ++ n21 ++ n22 ++ n23 ++ n24 ++ n25 ++ n26 ++ n27 ++ n28 ++ n29 := by
  rw [show payload.val=JGe_Payload27.sourceChunks.flatten from JGe_Payload27.bytes]
  simp only [JGe_Payload27.sourceChunks,JGe_Payload27.rawChunks,List.map_cons,List.map_nil]
  simp only [List.flatten_cons,List.flatten_nil,List.map_append,List.map_nil,List.append_nil,cast00,cast01,cast02,cast03,cast04,cast05,cast06,cast07,cast08,cast09,cast10,cast11,cast12,cast13,cast14,cast15,cast16,cast17,cast18,cast19,cast20,cast21,cast22,cast23,cast24,cast25,cast26,cast27,cast28]
  <;> simp only [List.append_assoc]
#print axioms payloadNat
theorem prefixCast : (encodeState before).val.map (fun x=>x.val) ++ [0,187] ++ [160,3,0,0]=n00 := by rfl
#print axioms prefixCast
def numeric : List Nat := n00 ++ n01 ++ n02 ++ n03 ++ n04 ++ n05 ++ n06 ++ n07 ++ n08 ++ n09 ++ n10 ++ n11 ++ n12 ++ n13 ++ n14 ++ n15 ++ n16 ++ n17 ++ n18 ++ n19 ++ n20 ++ n21 ++ n22 ++ n23 ++ n24 ++ n25 ++ n26 ++ n27 ++ n28 ++ n29
def suffix030 : List Nat := []
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
attribute [local irreducible] suffix000 suffix001 suffix002 suffix003 suffix004 suffix005 suffix006 suffix007 suffix008 suffix009 suffix010 suffix011 suffix012 suffix013 suffix014 suffix015 suffix016 suffix017 suffix018 suffix019 suffix020 suffix021 suffix022 suffix023 suffix024 suffix025 suffix026 suffix027 suffix028 suffix029 suffix030
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
theorem numeric_eq : numeric=rest00 := by
  simp only [numeric,rest00,List.append_assoc,List.append_nil,suffix001,suffix002,suffix003,suffix004,suffix005,suffix006,suffix007,suffix008,suffix009,suffix010,suffix011,suffix012,suffix013,suffix014,suffix015,suffix016,suffix017,suffix018,suffix019,suffix020,suffix021,suffix022,suffix023,suffix024,suffix025,suffix026,suffix027,suffix028,suffix029,suffix030]
#print axioms numeric_eq
theorem step00 : rest00=JGe_Q27Absorb.B00.input ++ rest01 := by
  have cell : n00 ++ n01=JGe_Q27Absorb.B00.input ++ (n01.drop 26) := by rfl
  simpa only [rest00,rest01,suffix001,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix002) cell
#print axioms step00
theorem step01 : rest01=JGe_Q27Absorb.B01.input ++ rest02 := by
  have cell : (n01.drop 26) ++ n02 ++ n03=JGe_Q27Absorb.B01.input ++ (n03.drop 26) := by rfl
  simpa only [rest01,rest02,suffix002,suffix003,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix004) cell
#print axioms step01
theorem step02 : rest02=JGe_Q27Absorb.B02.input ++ rest03 := by
  have cell : (n03.drop 26) ++ n04 ++ n05=JGe_Q27Absorb.B02.input ++ (n05.drop 26) := by rfl
  simpa only [rest02,rest03,suffix004,suffix005,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix006) cell
#print axioms step02
theorem step03 : rest03=JGe_Q27Absorb.B03.input ++ rest04 := by
  have cell : (n05.drop 26) ++ n06 ++ n07=JGe_Q27Absorb.B03.input ++ (n07.drop 26) := by rfl
  simpa only [rest03,rest04,suffix006,suffix007,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix008) cell
#print axioms step03
theorem step04 : rest04=JGe_Q27Absorb.B04.input ++ rest05 := by
  have cell : (n07.drop 26) ++ n08 ++ n09=JGe_Q27Absorb.B04.input ++ (n09.drop 26) := by rfl
  simpa only [rest04,rest05,suffix008,suffix009,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix010) cell
#print axioms step04
theorem step05 : rest05=JGe_Q27Absorb.B05.input ++ rest06 := by
  have cell : (n09.drop 26) ++ n10 ++ n11=JGe_Q27Absorb.B05.input ++ (n11.drop 26) := by rfl
  simpa only [rest05,rest06,suffix010,suffix011,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix012) cell
#print axioms step05
theorem step06 : rest06=JGe_Q27Absorb.B06.input ++ rest07 := by
  have cell : (n11.drop 26) ++ n12 ++ n13=JGe_Q27Absorb.B06.input ++ (n13.drop 26) := by rfl
  simpa only [rest06,rest07,suffix012,suffix013,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix014) cell
#print axioms step06
theorem step07 : rest07=JGe_Q27Absorb.B07.input ++ rest08 := by
  have cell : (n13.drop 26) ++ n14 ++ n15=JGe_Q27Absorb.B07.input ++ (n15.drop 26) := by rfl
  simpa only [rest07,rest08,suffix014,suffix015,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix016) cell
#print axioms step07
theorem step08 : rest08=JGe_Q27Absorb.B08.input ++ rest09 := by
  have cell : (n15.drop 26) ++ n16 ++ n17=JGe_Q27Absorb.B08.input ++ (n17.drop 26) := by rfl
  simpa only [rest08,rest09,suffix016,suffix017,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix018) cell
#print axioms step08
theorem step09 : rest09=JGe_Q27Absorb.B09.input ++ rest10 := by
  have cell : (n17.drop 26) ++ n18 ++ n19=JGe_Q27Absorb.B09.input ++ (n19.drop 26) := by rfl
  simpa only [rest09,rest10,suffix018,suffix019,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix020) cell
#print axioms step09
theorem step10 : rest10=JGe_Q27Absorb.B10.input ++ rest11 := by
  have cell : (n19.drop 26) ++ n20 ++ n21=JGe_Q27Absorb.B10.input ++ (n21.drop 26) := by rfl
  simpa only [rest10,rest11,suffix020,suffix021,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix022) cell
#print axioms step10
theorem step11 : rest11=JGe_Q27Absorb.B11.input ++ rest12 := by
  have cell : (n21.drop 26) ++ n22 ++ n23=JGe_Q27Absorb.B11.input ++ (n23.drop 26) := by rfl
  simpa only [rest11,rest12,suffix022,suffix023,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix024) cell
#print axioms step11
theorem step12 : rest12=JGe_Q27Absorb.B12.input ++ rest13 := by
  have cell : (n23.drop 26) ++ n24 ++ n25=JGe_Q27Absorb.B12.input ++ (n25.drop 26) := by rfl
  simpa only [rest12,rest13,suffix024,suffix025,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix026) cell
#print axioms step12
theorem step13 : rest13=JGe_Q27Absorb.B13.input ++ rest14 := by
  have cell : (n25.drop 26) ++ n26 ++ n27=JGe_Q27Absorb.B13.input ++ (n27.drop 26) := by rfl
  simpa only [rest13,rest14,suffix026,suffix027,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix028) cell
#print axioms step13
theorem step14 : rest14=JGe_Q27Absorb.B14.input ++ rest15 := by
  have cell : (n27.drop 26) ++ n28 ++ n29=JGe_Q27Absorb.B14.input ++ (n29.drop 26) := by rfl
  simpa only [rest14,rest15,suffix028,suffix029,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix030) cell
#print axioms step14
theorem last : rest15=JGe_Q27Absorb.tail := by
  simp only [rest15,suffix030,n29]
  rfl
#print axioms last
theorem regroup : numeric=JGe_Q27Absorb.message := by
  rw [numeric_eq]
  rw [step00,step01,step02,step03,step04,step05,step06,step07,step08,step09,step10,step11,step12,step13,step14,last]
  simp only [JGe_Q27Absorb.message,JGe_Q27Absorb.head,List.flatten_cons,List.flatten_nil,List.append_nil,List.append_assoc]
#print axioms regroup
theorem lengthCast : (core.num.U32.to_le_bytes 928#u32).val.map (fun x=>x.val)=[160,3,0,0] := by
  simp [core.num.U32.to_le_bytes,BitVec.toLEBytes] <;> (repeat' constructor) <;> scalar_tac
#print axioms lengthCast
theorem native : (flatten (CallerStep.openingAbsorbParts (encodeState before) 187#u8 928#u32 payload)).map Fin.val=JGe_Q27Absorb.message := by
  rw [←regroup]
  simp only [flatten,CallerStep.openingAbsorbParts,Array.to_slice,Array.make,List.flatMap_cons,List.flatMap_nil,List.map_append,List.append_nil,List.map_map,Function.comp_def,decodeByte,payloadNat,lengthCast,List.map_cons,List.map_nil]
  change (encodeState before).val.map (fun x=>x.val) ++ ([0,187] ++ ([160,3,0,0] ++ (n01 ++ n02 ++ n03 ++ n04 ++ n05 ++ n06 ++ n07 ++ n08 ++ n09 ++ n10 ++ n11 ++ n12 ++ n13 ++ n14 ++ n15 ++ n16 ++ n17 ++ n18 ++ n19 ++ n20 ++ n21 ++ n22 ++ n23 ++ n24 ++ n25 ++ n26 ++ n27 ++ n28 ++ n29)))=numeric
  have h := congrArg (fun lead => lead ++ (n01 ++ n02 ++ n03 ++ n04 ++ n05 ++ n06 ++ n07 ++ n08 ++ n09 ++ n10 ++ n11 ++ n12 ++ n13 ++ n14 ++ n15 ++ n16 ++ n17 ++ n18 ++ n19 ++ n20 ++ n21 ++ n22 ++ n23 ++ n24 ++ n25 ++ n26 ++ n27 ++ n28 ++ n29)) prefixCast
  simpa only [numeric,List.append_assoc] using h
#print axioms native
end AspisR1.JGg_Input27
