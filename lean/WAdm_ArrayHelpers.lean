import WAdm_LoopShapes
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.WAdm_ArrayHelpers
open WAdm_Fissioned WAdm_model

theorem roots (xs : Array (Array U8 32#usize) 2#usize) (out : alloc.vec.Vec U8)
    (bound : out.val.length + 64 ≤ Usize.max) :
    ∃ after, WAdm_roots out xs = ok after ∧ after.val = out.val ++ xs.val.flatMap (fun x => x.val) := by
  rw [WAdm_LoopShapes.roots]
  exact WAdm_Fold.contents (fun x => x.val) 32 (fun x => x.property) WAdm_EmittedScalars.putDigest WAdm_EmittedScalars.put_digest
    xs.val out (by rw [xs.property]; exact bound)

#print axioms roots

theorem early (xs : Array (WAdm_EmittedScalars.E) 4#usize) (out : alloc.vec.Vec U8)
    (bound : out.val.length + 128 ≤ Usize.max) :
    ∃ after, WAdm_early out xs = ok after ∧ after.val = out.val ++ xs.val.flatMap (CheckpointBytesE.rawBytes) := by
  rw [WAdm_LoopShapes.early]
  exact WAdm_Fold.contents (CheckpointBytesE.rawBytes) 32 (CheckpointBytesE.rawBytes_length) WAdm_EmittedScalars.putE WAdm_EmittedScalars.put_e
    xs.val out (by rw [xs.property]; exact bound)

#print axioms early

theorem tail (xs : Array (WAdm_EmittedScalars.E) 2#usize) (out : alloc.vec.Vec U8)
    (bound : out.val.length + 64 ≤ Usize.max) :
    ∃ after, WAdm_tail out xs = ok after ∧ after.val = out.val ++ xs.val.flatMap (CheckpointBytesE.rawBytes) := by
  rw [WAdm_LoopShapes.tail]
  exact WAdm_Fold.contents (CheckpointBytesE.rawBytes) 32 (CheckpointBytesE.rawBytes_length) WAdm_EmittedScalars.putE WAdm_EmittedScalars.put_e
    xs.val out (by rw [xs.property]; exact bound)

#print axioms tail

theorem queries (xs : Array (U32) 22#usize) (out : alloc.vec.Vec U8)
    (bound : out.val.length + 88 ≤ Usize.max) :
    ∃ after, WAdm_queries out xs = ok after ∧ after.val = out.val ++ xs.val.flatMap (fun x => (core.num.U32.to_le_bytes x).val) := by
  rw [WAdm_LoopShapes.queries]
  exact WAdm_Fold.contents (fun x => (core.num.U32.to_le_bytes x).val) 4 (fun x => (core.num.U32.to_le_bytes x).property) WAdm_EmittedScalars.putWord WAdm_EmittedScalars.put_word
    xs.val out (by rw [xs.property]; exact bound)

#print axioms queries

theorem semantic (xs : Array (WAdm_EmittedScalars.K) 10#usize) (out : alloc.vec.Vec U8)
    (bound : out.val.length + 160 ≤ Usize.max) :
    ∃ after, WAdm_semantic out xs = ok after ∧ after.val = out.val ++ xs.val.flatMap (CheckpointP6EncodeK.bytes) := by
  rw [WAdm_LoopShapes.semantic]
  exact WAdm_Fold.contents (CheckpointP6EncodeK.bytes) 16 (WAdm_EmittedScalars.k_length) WAdm_model.WAdm_putK WAdm_EmittedScalars.put_k
    xs.val out (by rw [xs.property]; exact bound)

#print axioms semantic

theorem coordinates (xs : Array (WAdm_EmittedScalars.K) 4#usize) (out : alloc.vec.Vec U8)
    (bound : out.val.length + 64 ≤ Usize.max) :
    ∃ after, WAdm_coordinates out xs = ok after ∧ after.val = out.val ++ xs.val.flatMap (CheckpointP6EncodeK.bytes) := by
  rw [WAdm_LoopShapes.coordinates]
  exact WAdm_Fold.contents (CheckpointP6EncodeK.bytes) 16 (WAdm_EmittedScalars.k_length) WAdm_model.WAdm_putK WAdm_EmittedScalars.put_k
    xs.val out (by rw [xs.property]; exact bound)

#print axioms coordinates

theorem flatMap_length {T : Type} (encode : T → List U8) (width : Nat)
    (length : ∀ x, (encode x).length = width) (xs : List T) :
    (xs.flatMap encode).length = width * xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.flatMap_cons,List.length_append,length,ih,List.length_cons,Nat.mul_succ]; omega

#print axioms flatMap_length
end AspisR1.WAdm_ArrayHelpers
end
