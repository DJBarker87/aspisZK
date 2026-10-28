import NDO_JGe_Payload29
import NDO_JGe_Q29Absorb
import NDO_JGe_OpeningInit
import NDO_JGe_Q28Ratchet0
set_option autoImplicit false
namespace AspisR1.JGg_Input29
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open JGe_Window29
def before : State := JFp_SHADigest.output JGe_Q28Ratchet0.result
def payload : Slice U8 := JGe_Payload29.value
def n00 : List Nat := [79,168,249,236,108,96,132,98,157,115,88,226,151,202,106,156,171,86,249,127,234,23,137,51,194,41,207,211,251,196,102,155,0,189,224,0,0,0]
def n01 : List Nat := [46,213,220,46,162,57,244,41,103,172,16,99,98,121,43,29,127,12,117,113,192,128,126,20,61,9,91,40,166,99,116,47]
def n02 : List Nat := [43,158,97,9,184,3,53,58,60,74,173,81,221,15,5,114,207,32,103,0,227,67,151,47,55,57,143,3,133,74,190,45]
def n03 : List Nat := [110,93,75,1,149,42,92,56,229,78,131,3,231,165,87,61,104,122,16,43,94,101,147,94,238,226,246,24,246,191,88,15]
def n04 : List Nat := [198,32,12,18,57,29,68,34,212,14,55,51,147,215,238,100,215,247,139,119,29,169,77,61,169,58,92,82,150,43,57,22]
def n05 : List Nat := [1,70,199,105,208,87,185,38,41,51,90,19,218,104,246,116,182,43,91,108,216,23,212,35,17,129,221,14,10,194,170,35]
def n06 : List Nat := [245,115,11,86,119,140,227,65,95,110,135,57,208,120,208,25,147,212,250,1,85,238,185,86,0,173,123,124,37,0,235,123]
def n07 : List Nat := [164,209,215,34,206,85,207,23,149,47,77,38,1,248,219,10,211,86,108,126,164,36,116,49,119,29,229,27,82,226,9,121]
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
theorem payloadNat : payload.val.map (fun x=>x.val)=n01 ++ n02 ++ n03 ++ n04 ++ n05 ++ n06 ++ n07 := by
  rw [show payload.val=JGe_Payload29.rawChunks.flatten from JGe_Payload29.retained]
  simp only [JGe_Payload29.rawChunks]
  simp only [List.flatten_cons,List.flatten_nil,List.map_append,List.map_nil,List.append_nil,cast00,cast01,cast02,cast03,cast04,cast05,cast06]
  <;> simp only [List.append_assoc]
#print axioms payloadNat
theorem prefixCast : (encodeState before).val.map (fun x=>x.val) ++ [0,189] ++ [224,0,0,0]=n00 := by rfl
#print axioms prefixCast
def numeric : List Nat := n00 ++ n01 ++ n02 ++ n03 ++ n04 ++ n05 ++ n06 ++ n07
def suffix008 : List Nat := []
def suffix007 : List Nat := n07 ++ suffix008
def suffix006 : List Nat := n06 ++ suffix007
def suffix005 : List Nat := n05 ++ suffix006
def suffix004 : List Nat := n04 ++ suffix005
def suffix003 : List Nat := n03 ++ suffix004
def suffix002 : List Nat := n02 ++ suffix003
def suffix001 : List Nat := n01 ++ suffix002
def suffix000 : List Nat := n00 ++ suffix001
attribute [local irreducible] suffix000 suffix001 suffix002 suffix003 suffix004 suffix005 suffix006 suffix007 suffix008
def rest00 : List Nat := n00 ++ suffix001
def rest01 : List Nat := n01.drop 26 ++ suffix002
def rest02 : List Nat := n03.drop 26 ++ suffix004
def rest03 : List Nat := n05.drop 26 ++ suffix006
def rest04 : List Nat := n07.drop 26 ++ suffix008
theorem numeric_eq : numeric=rest00 := by
  simp only [numeric,rest00,List.append_assoc,List.append_nil,suffix001,suffix002,suffix003,suffix004,suffix005,suffix006,suffix007,suffix008]
#print axioms numeric_eq
theorem step00 : rest00=JGe_Q29Absorb.B00.input ++ rest01 := by
  have cell : n00 ++ n01=JGe_Q29Absorb.B00.input ++ (n01.drop 26) := by rfl
  simpa only [rest00,rest01,suffix001,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix002) cell
#print axioms step00
theorem step01 : rest01=JGe_Q29Absorb.B01.input ++ rest02 := by
  have cell : (n01.drop 26) ++ n02 ++ n03=JGe_Q29Absorb.B01.input ++ (n03.drop 26) := by rfl
  simpa only [rest01,rest02,suffix002,suffix003,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix004) cell
#print axioms step01
theorem step02 : rest02=JGe_Q29Absorb.B02.input ++ rest03 := by
  have cell : (n03.drop 26) ++ n04 ++ n05=JGe_Q29Absorb.B02.input ++ (n05.drop 26) := by rfl
  simpa only [rest02,rest03,suffix004,suffix005,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix006) cell
#print axioms step02
theorem step03 : rest03=JGe_Q29Absorb.B03.input ++ rest04 := by
  have cell : (n05.drop 26) ++ n06 ++ n07=JGe_Q29Absorb.B03.input ++ (n07.drop 26) := by rfl
  simpa only [rest03,rest04,suffix006,suffix007,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix008) cell
#print axioms step03
theorem last : rest04=JGe_Q29Absorb.tail := by
  simp only [rest04,suffix008,n07]
  rfl
#print axioms last
theorem regroup : numeric=JGe_Q29Absorb.message := by
  rw [numeric_eq]
  rw [step00,step01,step02,step03,last]
  simp only [JGe_Q29Absorb.message,JGe_Q29Absorb.head,List.flatten_cons,List.flatten_nil,List.append_nil,List.append_assoc]
#print axioms regroup
theorem lengthCast : (core.num.U32.to_le_bytes 224#u32).val.map (fun x=>x.val)=[224,0,0,0] := by
  simp [core.num.U32.to_le_bytes,BitVec.toLEBytes] <;> (repeat' constructor) <;> scalar_tac
#print axioms lengthCast
theorem native : (flatten (CallerStep.openingAbsorbParts (encodeState before) 189#u8 224#u32 payload)).map Fin.val=JGe_Q29Absorb.message := by
  rw [←regroup]
  simp only [flatten,CallerStep.openingAbsorbParts,Array.to_slice,Array.make,List.flatMap_cons,List.flatMap_nil,List.map_append,List.append_nil,List.map_map,Function.comp_def,decodeByte,payloadNat,lengthCast,List.map_cons,List.map_nil]
  change (encodeState before).val.map (fun x=>x.val) ++ ([0,189] ++ ([224,0,0,0] ++ (n01 ++ n02 ++ n03 ++ n04 ++ n05 ++ n06 ++ n07)))=numeric
  have h := congrArg (fun lead => lead ++ (n01 ++ n02 ++ n03 ++ n04 ++ n05 ++ n06 ++ n07)) prefixCast
  simpa only [numeric,List.append_assoc] using h
#print axioms native
end AspisR1.JGg_Input29
