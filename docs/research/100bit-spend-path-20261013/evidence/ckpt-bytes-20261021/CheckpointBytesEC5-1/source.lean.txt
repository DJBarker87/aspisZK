import CheckpointBytesE

set_option autoImplicit false
namespace AspisR1.CheckpointBytesEC5
open Aeneas Aeneas.Std Result
open OraclePortCkptAbi2Extracted OraclePortCkptAbi5Codec OraclePortCkptAbi4Decode
open MultiproofConeCanonical OraclePortCompactDraft CheckpointBytesE

/-- Exact wide field layout, retaining all eight canonical raw limbs. -/
theorem rawBytes_c5 (q : RawE) (canonical : CanonicalWide q) :
    bytesOf (rawBytes q) = OraclePortCheckpointAbiC5.encodeE (exactE q canonical) := by
  rw [c5_e_bytes]
  simp only [rawBytes,CheckpointP6EncodeK.bytes,bytesOf,List.map_append]
  change bytesOf (core.num.U32.to_le_bytes q.c0.c0.a).val ++
    bytesOf (core.num.U32.to_le_bytes q.c0.c0.b).val ++
    bytesOf (core.num.U32.to_le_bytes q.c0.c1.a).val ++
    bytesOf (core.num.U32.to_le_bytes q.c0.c1.b).val ++
    (bytesOf (core.num.U32.to_le_bytes q.c1.c0.a).val ++
    bytesOf (core.num.U32.to_le_bytes q.c1.c0.b).val ++
    bytesOf (core.num.U32.to_le_bytes q.c1.c1.a).val ++
    bytesOf (core.num.U32.to_le_bytes q.c1.c1.b).val) = _
  rw [CheckpointP6KBytes.word_bytes,CheckpointP6KBytes.word_bytes,
    CheckpointP6KBytes.word_bytes,CheckpointP6KBytes.word_bytes,
    CheckpointP6KBytes.word_bytes,CheckpointP6KBytes.word_bytes,
    CheckpointP6KBytes.word_bytes,CheckpointP6KBytes.word_bytes]
  simp [words,List.append_assoc]

/-- Every in-range selector call succeeds and returns exactly C5's byte.
Canonicality is needed for physical/exact-field interpretation, not totality. -/
theorem e_byte_c5 (q : RawE) (canonical : CanonicalWide q)
    (i : Usize) (bound : i.val < 32) :
    ∃ v, e_byte q i = ok v ∧
      (OraclePortCheckpointAbiC5.encodeE (exactE q canonical))[i.val]? =
        some (AspisV8R19.SqueezeOracleBridge.decodeByte v) := by
  let j : Fin 32 := ⟨i.val,bound⟩
  have eq : Usize.ofNat j.val (by have := j.isLt; scalar_tac) = i := by
    apply UScalar.eq_of_val_eq
    simp [j]
  have run := e_byte_raw q j
  rw [eq] at run
  refine ⟨_,run,?_⟩
  rw [← rawBytes_c5 q canonical]
  simp [bytesOf,j,List.getElem?_eq_getElem,rawBytes_length,bound]

#print axioms rawBytes_c5
#print axioms e_byte_c5
end AspisR1.CheckpointBytesEC5
