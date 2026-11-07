import NNC_SourceCuts
import RSL_TX2_241
set_option autoImplicit false
noncomputable section
namespace NNC_ByteCarriers
open Aeneas Aeneas.Std AspisR1
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
/-- Exact byte-carrier conversion; no byte content is abstracted away. -/
def nativeByte (b : UInt8) : U8 := ⟨b.toBitVec⟩
def hostByte (b : U8) : UInt8 := ⟨b.bv⟩
def nativeList (bs : RSL.Bytes) : List U8 := bs.map nativeByte
def host (bs : List U8) : RSL.Bytes := bs.map hostByte
def protocol (bs : RSL.Bytes) : Bytes := MultiproofConeCanonical.bytesOf (nativeList bs)
/-- Canonical V2Lib.Root0 on byte carriers. Only the harmless slice subtype
length proof is omitted here; the literal raw-list predicate is unchanged. -/
def Root0 (ck proof : RSL.Bytes) : Prop :=
 ((nativeList ck).drop 112).take 32=(AspisV8R19.SqueezeOracleBridge.encodeState
  ((SemanticRecordCodec.decodeState
    (OraclePortCompactDraft.slice (protocol proof) 16 32)).getD (fun _=>0))).val
theorem native_host (s : List U8) : nativeList (host s)=s := by
 simp only [nativeList,host,List.map_map]
 exact congrFun List.map_id_fun s
theorem host_native (bs : RSL.Bytes) : host (nativeList bs)=bs := by
 simp only [nativeList,host,List.map_map]
 exact congrFun List.map_id_fun bs
theorem root0_native (ck proof : Slice U8) :
 Root0 (host ck.val) (host proof.val) ↔ NLP_InputDomain.Root0 ck proof := by
 simp only [Root0,protocol,native_host,NLP_InputDomain.Root0]
theorem root0_protocol (ck proof : Slice U8) (c p : RSL.Bytes)
 (hc : host ck.val=c) (hp : host proof.val=p) :
 Root0 c p ↔ NLP_InputDomain.Root0 ck proof := by
 rw [←hc,←hp]
 exact root0_native ck proof
theorem protocol_host (s : Slice U8) : protocol (host s.val)=MultiproofConeCanonical.bytesOf s.val := by
 unfold protocol
 rw [native_host]
theorem host_slice (s : List U8) (i j : Nat) :
 host ((s.drop i).take (j-i))=RSL.slice (host s) i j := by
 simp only [host,RSL.slice,List.map_take,List.map_drop]
#print axioms native_host
#print axioms host_native
#print axioms root0_native
#print axioms root0_protocol
#print axioms protocol_host
#print axioms host_slice
end NNC_ByteCarriers
