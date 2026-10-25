import WAdm_ArrayHelpers
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.WAdm_FissionedContent
open WAdm_Fissioned WAdm_model WAdm_EmittedScalars
open AspisR1Stage2.WireTx2 (singletonParts checksumParts)

def header : List U8 :=
  [82#u8,49#u8,80#u8,50#u8,67#u8,75#u8,80#u8,50#u8,2#u8,10#u8,1#u8,0#u8,0#u8,0#u8,0#u8,0#u8]

def body (f : WAdm_Fields) (weights : alloc.vec.Vec K) (hp hu : Array U8 32#usize) : List U8 :=
  header ++ hp.val ++ hu.val ++ f.state.val ++ f.roots.val.flatMap (fun x => x.val) ++
  f.early.val.flatMap CheckpointBytesE.rawBytes ++ CheckpointP6EncodeK.bytes f.rho ++
  f.queries.val.flatMap (fun x => (core.num.U32.to_le_bytes x).val) ++
  f.semantic.val.flatMap CheckpointP6EncodeK.bytes ++ f.coordinates.val.flatMap CheckpointP6EncodeK.bytes ++
  f.tail.val.flatMap CheckpointBytesE.rawBytes ++ CheckpointP6EncodeK.bytes f.power ++
  weights.val.flatMap CheckpointP6EncodeK.bytes

theorem body_length (f : WAdm_Fields) (weights : alloc.vec.Vec K) (hp hu : Array U8 32#usize)
    (size : weights.val.length = 64) : (body f weights hp hu).length = 1736 := by
  have roots := WAdm_ArrayHelpers.flatMap_length (fun x : Array U8 32#usize => x.val) 32
    (fun x => x.property) f.roots.val
  have early := WAdm_ArrayHelpers.flatMap_length CheckpointBytesE.rawBytes 32
    CheckpointBytesE.rawBytes_length f.early.val
  have queries := WAdm_ArrayHelpers.flatMap_length (fun x => (core.num.U32.to_le_bytes x).val) 4
    (fun x => (core.num.U32.to_le_bytes x).property) f.queries.val
  have semantic := WAdm_ArrayHelpers.flatMap_length CheckpointP6EncodeK.bytes 16 k_length f.semantic.val
  have coordinates := WAdm_ArrayHelpers.flatMap_length CheckpointP6EncodeK.bytes 16 k_length f.coordinates.val
  have tail := WAdm_ArrayHelpers.flatMap_length CheckpointBytesE.rawBytes 32 CheckpointBytesE.rawBytes_length f.tail.val
  have weightLength := WAdm_ArrayHelpers.flatMap_length CheckpointP6EncodeK.bytes 16 k_length weights.val
  simp only [body,List.length_append,header,List.length_cons,List.length_nil,hp.property,hu.property,
    f.state.property,roots,early,queries,semantic,coordinates,tail,weightLength,k_length,
    f.roots.property,f.early.property,f.queries.property,f.semantic.property,f.coordinates.property,
    f.tail.property,size]
  rfl

def bodySlice (f : WAdm_Fields) (weights : alloc.vec.Vec K) (hp hu : Array U8 32#usize)
    (size : weights.val.length = 64) : Slice U8 :=
  ⟨body f weights hp hu,by rw [body_length f weights hp hu size]; scalar_tac⟩

def finish (f : WAdm_Fields) (weights : alloc.vec.Vec K) (hp hu hc : Array U8 32#usize)
    (size : weights.val.length = 64) : alloc.vec.Vec U8 :=
  ⟨body f weights hp hu ++ hc.val,by
    rw [List.length_append,body_length f weights hp hu size,hc.property]; scalar_tac⟩

def shell {H : Type} (D : WAdm_Fissioned.aspis_core.digest.Digest32 H) (hash : H)
    (f : WAdm_Fields) (weights : alloc.vec.Vec K) (proof pub : Slice U8)
    (size : weights.val.length = 64) : Result (alloc.vec.Vec U8) := do
  let hp ← D.digest hash (singletonParts proof)
  let hu ← D.digest hash (singletonParts pub)
  let hc ← D.digest hash (checksumParts (bodySlice f weights hp hu size))
  ok (finish f weights hp hu hc size)

#print axioms body_length
end AspisR1.WAdm_FissionedContent
end
