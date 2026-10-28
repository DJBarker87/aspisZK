import NDO_JGe_Payload30
import NDO_JGe_Q30Absorb
import NDO_JGe_OpeningInit
import NDO_JGe_Q29Ratchet0
set_option autoImplicit false
namespace AspisR1.JGg_Input30
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open JGe_Window30
def before : State := JFp_SHADigest.output JGe_Q29Ratchet0.result
def payload : Slice U8 := JGe_Payload30.value
def n00 : List Nat := [172,194,84,18,22,182,60,150,181,13,201,75,80,218,5,213,131,85,251,229,232,142,42,121,73,70,154,240,140,228,187,202,0,190,0,1,0,0]
def n01 : List Nat := [46,133,21,235,161,197,244,215,120,165,246,0,196,252,96,124,6,55,195,101,6,216,73,254,64,84,104,238,161,99,66,102]
def n02 : List Nat := [188,176,14,9,104,136,7,67,62,142,62,64,30,43,122,0,27,17,194,73,253,79,59,58,248,148,26,5,195,50,215,58]
def n03 : List Nat := [40,149,9,121,170,168,202,23,96,236,244,9,212,203,57,58,234,145,192,63,170,103,21,1,130,144,87,104,162,174,104,42]
def n04 : List Nat := [90,246,9,91,155,215,244,108,89,187,30,28,176,40,54,49,238,86,137,121,102,70,147,5,8,15,223,111,110,170,103,77]
def n05 : List Nat := [8,163,183,118,71,183,36,100,45,254,225,21,162,55,70,38,16,0,88,19,207,66,130,107,57,96,214,122,8,91,228,77]
def n06 : List Nat := [95,15,238,117,66,129,87,26,7,89,115,113,17,5,162,84,186,29,143,42,74,68,41,20,152,107,107,32,55,239,115,30]
def n07 : List Nat := [45,169,13,60,211,53,107,97,151,1,166,34,114,37,9,39,40,34,140,122,231,173,93,81,238,112,237,111,200,111,127,4]
def n08 : List Nat := [14,151,64,27,60,199,201,12,214,203,81,76,46,217,25,63,54,87,253,78,6,103,150,41,225,21,24,67,188,33,161,5]
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
theorem payloadNat : payload.val.map (fun x=>x.val)=n01 ++ n02 ++ n03 ++ n04 ++ n05 ++ n06 ++ n07 ++ n08 := by
  rw [show payload.val=JGe_Payload30.rawChunks.flatten from JGe_Payload30.retained]
  simp only [JGe_Payload30.rawChunks]
  simp only [List.flatten_cons,List.flatten_nil,List.map_append,List.map_nil,List.append_nil,cast00,cast01,cast02,cast03,cast04,cast05,cast06,cast07]
  <;> simp only [List.append_assoc]
#print axioms payloadNat
theorem prefixCast : (encodeState before).val.map (fun x=>x.val) ++ [0,190] ++ [0,1,0,0]=n00 := by rfl
#print axioms prefixCast
def numeric : List Nat := n00 ++ n01 ++ n02 ++ n03 ++ n04 ++ n05 ++ n06 ++ n07 ++ n08
def suffix009 : List Nat := []
def suffix008 : List Nat := n08 ++ suffix009
def suffix007 : List Nat := n07 ++ suffix008
def suffix006 : List Nat := n06 ++ suffix007
def suffix005 : List Nat := n05 ++ suffix006
def suffix004 : List Nat := n04 ++ suffix005
def suffix003 : List Nat := n03 ++ suffix004
def suffix002 : List Nat := n02 ++ suffix003
def suffix001 : List Nat := n01 ++ suffix002
def suffix000 : List Nat := n00 ++ suffix001
attribute [local irreducible] suffix000 suffix001 suffix002 suffix003 suffix004 suffix005 suffix006 suffix007 suffix008 suffix009
def rest00 : List Nat := n00 ++ suffix001
def rest01 : List Nat := n01.drop 26 ++ suffix002
def rest02 : List Nat := n03.drop 26 ++ suffix004
def rest03 : List Nat := n05.drop 26 ++ suffix006
def rest04 : List Nat := n07.drop 26 ++ suffix008
theorem numeric_eq : numeric=rest00 := by
  simp only [numeric,rest00,List.append_assoc,List.append_nil,suffix001,suffix002,suffix003,suffix004,suffix005,suffix006,suffix007,suffix008,suffix009]
#print axioms numeric_eq
theorem step00 : rest00=JGe_Q30Absorb.B00.input ++ rest01 := by
  have cell : n00 ++ n01=JGe_Q30Absorb.B00.input ++ (n01.drop 26) := by rfl
  simpa only [rest00,rest01,suffix001,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix002) cell
#print axioms step00
theorem step01 : rest01=JGe_Q30Absorb.B01.input ++ rest02 := by
  have cell : (n01.drop 26) ++ n02 ++ n03=JGe_Q30Absorb.B01.input ++ (n03.drop 26) := by rfl
  simpa only [rest01,rest02,suffix002,suffix003,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix004) cell
#print axioms step01
theorem step02 : rest02=JGe_Q30Absorb.B02.input ++ rest03 := by
  have cell : (n03.drop 26) ++ n04 ++ n05=JGe_Q30Absorb.B02.input ++ (n05.drop 26) := by rfl
  simpa only [rest02,rest03,suffix004,suffix005,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix006) cell
#print axioms step02
theorem step03 : rest03=JGe_Q30Absorb.B03.input ++ rest04 := by
  have cell : (n05.drop 26) ++ n06 ++ n07=JGe_Q30Absorb.B03.input ++ (n07.drop 26) := by rfl
  simpa only [rest03,rest04,suffix006,suffix007,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix008) cell
#print axioms step03
theorem last : rest04=JGe_Q30Absorb.tail := by
  simp only [rest04,suffix008,suffix009,n07]
  rfl
#print axioms last
theorem regroup : numeric=JGe_Q30Absorb.message := by
  rw [numeric_eq]
  rw [step00,step01,step02,step03,last]
  simp only [JGe_Q30Absorb.message,JGe_Q30Absorb.head,List.flatten_cons,List.flatten_nil,List.append_nil,List.append_assoc]
#print axioms regroup
theorem lengthCast : (core.num.U32.to_le_bytes 256#u32).val.map (fun x=>x.val)=[0,1,0,0] := by
  simp [core.num.U32.to_le_bytes,BitVec.toLEBytes] <;> (repeat' constructor) <;> scalar_tac
#print axioms lengthCast
theorem native : (flatten (CallerStep.openingAbsorbParts (encodeState before) 190#u8 256#u32 payload)).map Fin.val=JGe_Q30Absorb.message := by
  rw [←regroup]
  simp only [flatten,CallerStep.openingAbsorbParts,Array.to_slice,Array.make,List.flatMap_cons,List.flatMap_nil,List.map_append,List.append_nil,List.map_map,Function.comp_def,decodeByte,payloadNat,lengthCast,List.map_cons,List.map_nil]
  change (encodeState before).val.map (fun x=>x.val) ++ ([0,190] ++ ([0,1,0,0] ++ (n01 ++ n02 ++ n03 ++ n04 ++ n05 ++ n06 ++ n07 ++ n08)))=numeric
  have h := congrArg (fun lead => lead ++ (n01 ++ n02 ++ n03 ++ n04 ++ n05 ++ n06 ++ n07 ++ n08)) prefixCast
  simpa only [numeric,List.append_assoc] using h
#print axioms native
end AspisR1.JGg_Input30
