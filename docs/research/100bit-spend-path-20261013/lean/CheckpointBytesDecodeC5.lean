import CheckpointBytesBody
import OraclePortCkptAbiCodec

set_option autoImplicit false
noncomputable section
namespace AspisR1.CheckpointBytesDecodeC5
open Aeneas Aeneas.Std Result
open OraclePortCkptAbi2Extracted aspis_r1_cost_probe.verifier
open CheckpointBytesBody CheckpointBytesBlocks CheckpointBytesDigest
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OraclePortCompactDraft MultiproofConeCanonical

/-- Materialization of the extracted sparse source selector. The fallback is
unreachable on the canonical bounded domain, as source_body_c5 proves. -/
def sourceBody (p : Prepared) (a : Accumulator) (hp hu : Array U8 32#usize) : Bytes :=
  List.ofFn fun j : Fin 1736 =>
    match OraclePortCkptAbi2Extracted.body_byte p a hp hu
      (Usize.ofNat j.val (by have := j.isLt; scalar_tac)) with
    | ok v => AspisV8R19.SqueezeOracleBridge.decodeByte v
    | _ => 0

theorem source_body_c5 (p : Prepared) (a : Accumulator) (hp hu : Array U8 32#usize)
    (size : a.weights.val.length = 64)
    (qb : ∀ j : Fin 22, (p.queries.val[j.val]'(by simpa [p.queries.property] using j.isLt)).val < 262144)
    (canonical : CanonicalFields (fields p a size qb)) (next : a.next.val = 10) :
    sourceBody p a hp hu =
      OraclePortCheckpointAbiC5.body (prepared (fields p a size qb) canonical)
        (accumulator (fields p a size qb) canonical) (stateOf hp) (stateOf hu) := by
  apply List.ext_getElem
  · simp only [sourceBody,List.length_ofFn,OraclePortCheckpointAbiC5.body_length]
  · intro i hi hj
    have bound : i < 1736 := by simpa only [sourceBody,List.length_ofFn] using hi
    obtain ⟨v,run,byte⟩ := body_byte_c5 p a hp hu size qb canonical next
      (Usize.ofNat i (by scalar_tac)) (by simpa using bound)
    have castVal : (Usize.ofNat i (by scalar_tac)).val = i := by simp
    simp only [castVal] at byte
    rw [List.getElem?_eq_getElem hj] at byte
    simp only [sourceBody,List.getElem_ofFn,run]
    exact (Option.some.inj byte).symm

/-- Checksum congruence is over the complete source-selected body. This is a
byte-list result; physical Vec extension and digest-call adoption are separate. -/
theorem source_checksum_c5 (H : Bytes → State) (p : Prepared) (a : Accumulator)
    (hp hu : Array U8 32#usize) (size : a.weights.val.length = 64)
    (qb : ∀ j : Fin 22, (p.queries.val[j.val]'(by simpa [p.queries.property] using j.isLt)).val < 262144)
    (canonical : CanonicalFields (fields p a size qb)) (next : a.next.val = 10) :
    sourceBody p a hp hu ++ bytes (H (OraclePortPhysicalFrameDraft.domain ++ sourceBody p a hp hu)) =
      let b := OraclePortCheckpointAbiC5.body (prepared (fields p a size qb) canonical)
        (accumulator (fields p a size qb) canonical) (stateOf hp) (stateOf hu)
      b ++ bytes (H (OraclePortPhysicalFrameDraft.domain ++ b)) := by
  rw [source_body_c5 p a hp hu size qb canonical next]

/-- All C5 K output meanings, including failure of every non-encoding. -/
theorem decode_k_iff (b : Bytes) (x : OraclePortCheckpointAbiC5.K) :
    ExactLeafFieldCodec.decodeQM31 b = some x ↔ OraclePortCheckpointAbiC5.encodeK x = b := by
  constructor
  · exact ExactLeafFieldCodec.encodeQM31_of_decodeQM31 b x
  · intro h
    rw [← h]
    exact ExactLeafFieldCodec.decodeQM31_encodeQM31 x

theorem reject_k_iff (b : Bytes) :
    ExactLeafFieldCodec.decodeQM31 b = none ↔
      ¬ ∃ x : OraclePortCheckpointAbiC5.K, OraclePortCheckpointAbiC5.encodeK x = b := by
  constructor
  · intro rejected ⟨x,encoding⟩
    have accepted := (decode_k_iff b x).2 encoding
    rw [rejected] at accepted
    cases accepted
  · intro notEncoding
    cases h : ExactLeafFieldCodec.decodeQM31 b with
    | none => rfl
    | some x => exact False.elim (notEncoding ⟨x,(decode_k_iff b x).1 h⟩)

theorem decode_e_iff (b : Bytes) (x : OraclePortCheckpointAbiC5.E) :
    FoldedLeafCodec.decodeWide b = some x ↔ OraclePortCheckpointAbiC5.encodeE x = b :=
  FoldedLeafCodec.decodeWide_eq_some_iff b x

theorem reject_e_iff (b : Bytes) :
    FoldedLeafCodec.decodeWide b = none ↔
      ¬ ∃ x : OraclePortCheckpointAbiC5.E, OraclePortCheckpointAbiC5.encodeE x = b := by
  constructor
  · intro rejected ⟨x,encoding⟩
    have accepted := (decode_e_iff b x).2 encoding
    rw [rejected] at accepted
    cases accepted
  · intro notEncoding
    cases h : FoldedLeafCodec.decodeWide b with
    | none => rfl
    | some x => exact False.elim (notEncoding ⟨x,(decode_e_iff b x).1 h⟩)

/-- Complete C5 model output on the concrete source field interpretation.
Duplicate query rejection is retained; canonical field bytes alone do not
imply semantic validity of a checkpoint or allocator availability. -/
theorem decode_source_fields (H : Bytes → State) (stored pub : Bytes)
    (p : Prepared) (a : Accumulator) (size : a.weights.val.length = 64)
    (qb : ∀ j : Fin 22, (p.queries.val[j.val]'(by simpa [p.queries.property] using j.isLt)).val < 262144)
    (canonical : CanonicalFields (fields p a size qb)) :
    OraclePortCkptAbiCodec.decode
      (OraclePortCheckpointAbiC5.encode H stored pub (prepared (fields p a size qb) canonical)
        (accumulator (fields p a size qb) canonical)) =
      if Function.Injective (fields p a size qb).queries then
        some (prepared (fields p a size qb) canonical,accumulator (fields p a size qb) canonical)
      else none :=
  OraclePortCkptAbiCodec.decode_encode H stored pub _ _ rfl

#print axioms source_body_c5
#print axioms source_checksum_c5
#print axioms decode_k_iff
#print axioms reject_k_iff
#print axioms decode_e_iff
#print axioms reject_e_iff
#print axioms decode_source_fields
end AspisR1.CheckpointBytesDecodeC5
end
