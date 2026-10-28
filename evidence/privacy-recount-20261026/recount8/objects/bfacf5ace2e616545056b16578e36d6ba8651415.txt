import R1Z.ProverRwOuterPrepare
import R1Z.ProverCommitPublicBinding40
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwOuterFrames
open Aeneas Aeneas.Std Result ProverRwFull
open ProverRwOuterContextModel ProverRwOuterEncode ProverCommitOwnerBytes42

def domain : Slice U8 :=
  Array.to_slice
      (Array.make 30#usize [
        85#u8, 78#u8, 80#u8, 82#u8, 79#u8, 86#u8, 69#u8, 68#u8, 58#u8, 82#u8,
        49#u8, 58#u8, 80#u8, 51#u8, 58#u8, 80#u8, 82#u8, 73#u8, 86#u8, 65#u8,
        84#u8, 69#u8, 45#u8, 65#u8, 84#u8, 84#u8, 69#u8, 77#u8, 80#u8, 84#u8
        ])

def digestInput (val : alloc.vec.Vec U8) : Slice (Slice U8) :=
  Array.to_slice (Array.make 1#usize [alloc.vec.Vec.deref val])
def bindingInput (val : alloc.vec.Vec U8) (v : transport.Variant)
    (digest nonce : Array U8 32#usize) : Slice (Slice U8) :=
  Array.to_slice (Array.make 4#usize [domain,alloc.vec.Vec.deref val,
    Array.to_slice (Array.make 1#usize [ProverRwOuterTag.byte v]),
    Array.to_slice (value (context digest nonce))])
def run (val : alloc.vec.Vec U8) (v : transport.Variant)
    (hash : Slice (Slice U8) → Result (Array U8 32#usize)) (nonce : Array U8 32#usize) := do
  let digest ← hash (digestInput val)
  let binding ← hash (bindingInput val v digest nonce)
  .ok (context digest nonce,binding)

theorem direct_run (val : alloc.vec.Vec U8) (v : transport.Variant)
    (hash : Slice (Slice U8) → Result (Array U8 32#usize)) (nonce : Array U8 32#usize) :
    ProverRwOuterPrepare.direct val v hash nonce = run val v hash nonce := by
  unfold ProverRwOuterPrepare.direct run digestInput bindingInput domain
  simp only [lift,bind_tc_ok]

def flatten (parts : Slice (Slice U8)) : List UInt8 :=
  (parts.val.flatMap (fun s => s.val)).map byte

theorem digest_frame (val : alloc.vec.Vec U8) :
    flatten (digestInput val) = val.val.map byte := by
  simp [flatten,digestInput,Array.to_slice,Array.make,alloc.vec.Vec.deref]

theorem binding_frame (val : alloc.vec.Vec U8) (v : transport.Variant)
    (digest nonce : Array U8 32#usize) :
    flatten (bindingInput val v digest nonce) =
      ProverCommitPublicBinding40.binding (val.val.map byte)
        (byte (ProverRwOuterTag.byte v)) (block digest) (block nonce) := by
  simp only [flatten,bindingInput,Array.to_slice,Array.make,alloc.vec.Vec.deref]
  simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil,List.map_append,
    List.map_cons,List.map_nil]
  rw [ProverRwOuterContextModel.context_encoding]
  unfold domain ProverCommitPublicBinding40.binding
  simp only [Array.to_slice,Array.make,List.map_cons,List.map_nil]
  simp [List.append_assoc,LayoutR1PBin.dBind0,byte]

#print axioms direct_run
#print axioms digest_frame
#print axioms binding_frame
end R1Z.ProverRwOuterFrames
