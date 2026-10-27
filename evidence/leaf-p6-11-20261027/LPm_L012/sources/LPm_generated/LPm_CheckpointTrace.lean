import LPm_CheckpointProgram
import LPm_BytePorts
import MultiproofConeByteEquality
set_option autoImplicit false
noncomputable section
namespace AspisR1.LPm_CheckpointTrace
open Aeneas Aeneas.Std Result
open CheckpointBytes5Effect CheckpointBytes5Writer CheckpointBytes5Inputs
open CheckpointBytesBlocks CheckpointBytesBody CheckpointBytesDigest CheckpointBytesDecodeC5
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep MultiproofConeCanonical
open AspisR1Stage2.WireTx2 (singletonParts checksumParts)
attribute [local irreducible] sourceBody LPm_CheckpointBody.nativeBody

/-- Only local append steps, linked through the SAME owned output buffer. -/
inductive Appends : List (List U8) → List U8 → List U8 → Prop where
  | done (buf : List U8) : Appends [] buf buf
  | step (bs : List U8) (rest : List (List U8)) (before middle after : List U8)
      (write : middle = before ++ bs) (tail : Appends rest middle after) :
      Appends (bs::rest) before after

theorem append_result {bs : List (List U8)} {before after : List U8}
    (tr : Appends bs before after) : after = before ++ bs.flatten := by
  induction tr with
  | done buf => simp only [List.flatten_nil,List.append_nil]
  | step bs rest before middle after write tail ih =>
    rw [ih,write]
    simp only [List.flatten_cons,List.append_assoc]

def prefixBlocks (p : Prepared) (a : Accumulator)
    (size : a.weights.val.length = 64)
    (qb : ∀ j : Fin 22,
      (p.queries.val[j.val]'(by simpa [p.queries.property] using j.isLt)).val < 262144)
    (hp hu : Digest) : List Bytes :=
  (blocks (fields p a size qb) (stateOf hp) (stateOf hu)).take 17

/-- The actual weights carrier supplies the final block. The prefix is the
concrete earlier fields, rather than a separately selected checkpoint body. -/
theorem body_split (p : Prepared) (a : Accumulator)
    (size : a.weights.val.length = 64)
    (qb : ∀ j : Fin 22,
      (p.queries.val[j.val]'(by simpa [p.queries.property] using j.isLt)).val < 262144)
    (hp hu : Digest) :
    LPm_CheckpointBody.nativeBody p a size qb hp hu =
      (prefixBlocks p a size qb hp hu).flatten ++
        bytesOf (LPi_SerializationFold.fold [] a.weights.val) := by
  rw [LPm_CheckpointBody.weights_port a size]
  simp only [LPm_CheckpointBody.nativeBody,CheckpointBytesBlocks.body,prefixBlocks,
    blocks,fields,List.take_succ_cons,List.take_zero,List.flatten_cons,List.flatten_nil,
    List.append_nil,List.append_assoc]

/-- Source-local trace through the pre-weight writes, the 64 actual weight
iterations, and the last checksum append. It contains no complete-body or
whole native/model equality field. The middle bytes are the SAME bytes used
as the third digest argument, not an independent arbitrary cut. -/
structure Trace (p : Prepared) (a : Accumulator)
    (size : a.weights.val.length = 64)
    (qb : ∀ j : Fin 22,
      (p.queries.val[j.val]'(by simpa [p.queries.property] using j.isLt)).val < 262144)
    (hp hu hc : Digest) (body out : Slice U8) where
  beforeWeights : List U8
  prefixSteps : Appends ((prefixBlocks p a size qb hp hu).map (List.map u8)) [] beforeWeights
  weightSteps : LPm_WeightLoop.Trace a.weights.val beforeWeights body.val
  checksumAppend : out.val = body.val ++ hc.val

theorem body_bytes (p : Prepared) (a : Accumulator)
    (size : a.weights.val.length = 64)
    (qb : ∀ j : Fin 22,
      (p.queries.val[j.val]'(by simpa [p.queries.property] using j.isLt)).val < 262144)
    (hp hu hc : Digest) (body out : Slice U8) (tr : Trace p a size qb hp hu hc body out) :
    bytesOf body.val = LPm_CheckpointBody.nativeBody p a size qb hp hu := by
  have pre := append_result tr.prefixSteps
  simp only [List.nil_append] at pre
  have w := LPm_WeightLoop.result tr.weightSteps
  rw [LPi_SerializationFold.contents] at w
  rw [w,bytesOf,List.map_append]
  rw [pre]
  rw [body_split]
  congr 1
  · change bytesOf (((prefixBlocks p a size qb hp hu).map (List.map u8)).flatten) = _
    unfold bytesOf
    rw [List.map_flatten,List.map_map]
    change (List.map (fun bs => bytesOf (bs.map u8))
      (prefixBlocks p a size qb hp hu)).flatten = _
    simp only [bytes_roundtrip]
    rw [List.map_id]
  · rw [LPi_SerializationFold.contents,List.nil_append]
    rfl


/-- Complete SAME-execution result/log join on the concrete carriers. The
three call observations are LOCAL oracle replies, never a supplied whole
run equality. Native source gates construct the local linked trace. -/
theorem native_result {Hash : Type}
    (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (p : Prepared) (a : Accumulator) (proof public1 : Slice U8)
    (size : a.weights.val.length = 64)
    (qb : ∀ j : Fin 22,
      (p.queries.val[j.val]'(by simpa [p.queries.property] using j.isLt)).val < 262144)
    (canonical : CanonicalFields (fields p a size qb)) (next : a.next.val = 10)
    (hp hu hc : Digest) (body out : Slice U8) (before : Log)
    (tr : Trace p a size qb hp hu hc body out)
    (proofCall : D.digest hash (singletonParts proof) = ok hp)
    (publicCall : D.digest hash (singletonParts public1) = ok hu)
    (checksumCall : D.digest hash (checksumParts body) = ok hc) :
    run D hash (writer p a proof public1) before =
      ok (out,((before ++ [(singletonParts proof,hp)]) ++
        [(singletonParts public1,hu)]) ++ [(checksumParts body,hc)]) := by
  have decoded := (body_bytes p a size qb hp hu hc body out tr).trans
    (LPm_CheckpointBody.source_body p a size qb canonical next hp hu)
  have bodyEq : body = bodySlice p a hp hu := by
    apply Subtype.ext
    apply MultiproofConeByteEquality.bytes_injective
    exact decoded.trans (bytes_roundtrip _).symm
  have outEq : out = finish p a hp hu hc := by
    apply Subtype.ext
    rw [tr.checksumAppend,bodyEq]
    rfl
  rw [bodyEq] at checksumCall
  simp only [writer,run_bind,run_read,run_pure,proofCall,publicCall,checksumCall,
    bind_tc_ok,Aeneas.Std.uncurry]
  rw [outEq,bodyEq]

#print axioms append_result
#print axioms body_split
#print axioms body_bytes
#print axioms native_result
end AspisR1.LPm_CheckpointTrace
end
