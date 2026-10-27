import RPz7_Tx2N_DecodeHeader
set_option autoImplicit false
noncomputable section
namespace AspisR1.Tx2N_Decode
open Aeneas Aeneas.Std Result AspisR1Stage2
open OraclePortCheckpointAbiC5 OraclePortCheckpointResumeC5
open CheckpointBytes5Output

/-- Successful installed reader, at its actual TX2 cursor, decodes exactly
the returned accumulator. No writer-state or encoding equation is assumed. -/
theorem actual (reserved : Bool) {Hash : Type} (D : aspis_core.digest.Digest32 Hash)
    (checkpoint proof pub : Slice U8) (hash : Hash) (p : verifier.Prepared) (a : verifier.Accumulator)
    (next : a.next = 10#usize)
    (success : verifier.resumeWithOps (CheckpointBytes4Ops.ops reserved) D checkpoint proof pub .S2 hash =
      ok (.Ok (p,a))) :
    decodeAccumulator (MultiproofConeCanonical.bytesOf checkpoint.val) = some (accumulator a) := by
  obtain ⟨f⟩ := CheckpointBytes4Ops.successful_fields reserved D checkpoint proof pub .S2 hash p a success
  obtain ⟨_,_,_,_,_,size,_⟩ := Tx2N_Header.cuts reserved D checkpoint proof pub hash p a success
  have flat := CheckpointBytes4Layout.flat_fields reserved checkpoint p a f size
  obtain ⟨rhs,readRhs,rhsEq⟩ := flat.rhs
  obtain ⟨power,readPower,powerEq⟩ := flat.power
  obtain ⟨weights,readWeights,weightsEq⟩ := flat.weights
  have header := Tx2N_DecodeHeader.accepted reserved D checkpoint proof pub hash p a next success
  have state : accumulator a = (⟨weights,rhs,power,10⟩ : QueryAccumulator.State K E) := by
    unfold accumulator
    congr 1
    · funext j
      simp only [weightsEq,List.getElem?_map,List.getElem?_ofFn,j.isLt,↓reduceDIte,
        Option.map_some,Option.getD_some,ofK_source]
    · rw [← rhsEq,ofE_source]
    · rw [← powerEq,ofK_source]
    · rw [next]
      scalar_tac
  rw [decodeAccumulator,if_pos header,readRhs,readPower,readWeights]
  simp only [Option.bind_eq_bind,Option.bind_some]
  rw [state]

#print axioms actual
end AspisR1.Tx2N_Decode
end
