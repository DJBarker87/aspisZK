import Port4B_SliceReads
import CheckpointBytes5Output

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port4B_Prepared
open Aeneas Aeneas.Std Result AspisR1Stage2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge
open MultiproofConeCanonical

theorem digest_of_bytes (native : Array U8 32#usize) (model : State)
    (content : bytesOf native.val=bytes model) : native=encodeState model := by
  have encoded := MultiproofConePhysicalTransport.digest_bytes (encodeState model)
  rw [state_roundtrip] at encoded
  exact Subtype.ext (MultiproofConeByteEquality.bytes_injective (content.trans encoded))

/-- The two physical Prepared roots come from the SAME saved/prepared body
provenance. This does not assert that arbitrary Prepared fields match parsed. -/
theorem roots (p : verifier.Prepared) (a : verifier.Accumulator)
    (pm : OraclePortCheckpointAbiC5.Prepared)
    (am : QueryAccumulator.State OraclePortCheckpointAbiC5.K OraclePortCheckpointAbiC5.E)
    (fields : CheckpointBytes4SavedFields.BodyMatches p a pm am) :
    Port3_BatchStage.root0 p=encodeState (pm.roots 0) ∧
    Port3_BatchStage.root1 p=encodeState (pm.roots 1) := by
  have len : p.roots.val.length=2 := p.roots.property
  have zero := congrArg (fun xs : List Bytes => xs[0]?.getD []) fields.roots
  have one := congrArg (fun xs : List Bytes => xs[1]?.getD []) fields.roots
  constructor
  · apply digest_of_bytes
    simpa only [Port3_BatchStage.root0,List.getElem?_map,List.getElem?_eq_getElem (show 0<p.roots.val.length by omega),
      Option.map_some,Option.getD_some,List.getElem?_cons_zero] using zero
  · apply digest_of_bytes
    simpa only [Port3_BatchStage.root1,List.getElem?_map,List.getElem?_eq_getElem (show 1<p.roots.val.length by omega),
      Option.map_some,Option.getD_some,List.getElem?_cons_succ,List.getElem?_cons_zero] using one

/-- Exact canonical physical query, with no modulo weakening of raw words. -/
theorem query_value (p : verifier.Prepared) (a : verifier.Accumulator)
    (pm : OraclePortCheckpointAbiC5.Prepared)
    (am : QueryAccumulator.State OraclePortCheckpointAbiC5.K OraclePortCheckpointAbiC5.E)
    (fields : CheckpointBytes4SavedFields.BodyMatches p a pm am)
    (j : Fin 22) (value : U32)
    (read : Array.index_usize p.queries (Usize.ofNat j.val (by scalar_tac))=ok value) :
    value.val=(pm.queries j).val := by
  have observed := congrArg (fun xs : List Nat => xs[j.val]?) fields.queries
  have len : p.queries.val.length=22 := p.queries.property
  have item := List.getElem?_eq_getElem (show j.val<p.queries.val.length by omega)
  change (match p.queries.val[j.val]? with | none => fail .arrayOutOfBounds | some u => ok u)=ok value at read
  rw [item] at read
  have same := Result.ok.inj read
  simp only [List.getElem?_map,item,Option.map_some,List.getElem?_ofFn,j.isLt,↓reduceDIte] at observed
  exact (congrArg UScalar.val same).symm.trans (Option.some.inj observed)

#print axioms digest_of_bytes
#print axioms roots
#print axioms query_value
end AspisR1.Port4B_Prepared
end
