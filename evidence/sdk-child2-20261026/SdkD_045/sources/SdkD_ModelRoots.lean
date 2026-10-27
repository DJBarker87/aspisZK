import SdkD_SliceAlgebra
set_option autoImplicit false
noncomputable section
namespace AspisR1.SdkD_ModelRoots
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open MultiproofConeCanonical OraclePortCompactDraft

theorem rawSlice (xs : List U8) (start finish : Nat) :
    bytesOf (xs.slice start finish) = slice (bytesOf xs) start (finish-start) := by
  simp only [List.slice,bytesOf,slice,List.map_take,List.map_drop]

theorem decode_native (root : Array U8 32#usize) :
    SemanticRecordCodec.decodeState (bytesOf root.val) = some (decodeState root) := by
  have same := MultiproofConePhysicalTransport.digest_bytes root
  rw [← same,SemanticRecordCodec.decodeState_bytes]

#print List.slice
#print axioms rawSlice
#print axioms decode_native
end AspisR1.SdkD_ModelRoots
end
