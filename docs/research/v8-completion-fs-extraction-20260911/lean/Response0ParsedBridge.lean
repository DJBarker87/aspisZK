import ExtractionCollectorCausalMatrix

/-!
# Literal response0 bytes determine the parsed first relation response

This leaf closes the byte/value adapter needed by the alpha-fork collision
dichotomy.  It does not construct the fork matrix or assign a probability to
the collision alternative.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 200000

namespace AspisV8Completion.Response0ParsedBridge

open AspisV5ComponentCQM31TowerExact
open AspisV8.SameBodySequentialCodec
open AspisV8Completion.FSLiveSelectedMiddleQueryRho
open AspisV8Completion.SameBodyFunctionalProducerSource
open AspisV8Completion.SameBodyRelation

abbrev Bytes := List UInt8
abbrev K := FSNonzeroQM31.K

private theorem response0_byte_eq
    (leftBody rightBody : Bytes)
    (leftLong : 6768 ≤ leftBody.length)
    (rightLong : 6768 ≤ rightBody.length)
    (same : response0Bytes leftBody = response0Bytes rightBody)
    (offset : Nat) (lt : offset < 96) :
    leftBody[6672 + offset]'(by omega) =
      rightBody[6672 + offset]'(by omega) := by
  have leftSlice : offset < (response0Bytes leftBody).length := by
    simp [response0Bytes, List.length_take, List.length_drop]
    omega
  have rightSlice : offset < (response0Bytes rightBody).length := by
    simp [response0Bytes, List.length_take, List.length_drop]
    omega
  have atOffset := congrArg
    (fun xs : Bytes => xs.getD offset 0) same
  rw [List.getD_eq_getElem _ _ leftSlice, List.getD_eq_getElem _ _ rightSlice] at atOffset
  simpa [response0Bytes] using atOffset

private theorem response0_chunk_eq
    (leftBody rightBody : Bytes)
    (leftLong : 6768 ≤ leftBody.length)
    (rightLong : 6768 ≤ rightBody.length)
    (same : response0Bytes leftBody = response0Bytes rightBody)
    (sent : Fin 6) :
    AspisV8.SameBodyChunkParser.chunk
        (FSV7PrefixBridge.encode leftBody) (16 * (417 + sent.val)) =
      AspisV8.SameBodyChunkParser.chunk
        (FSV7PrefixBridge.encode rightBody) (16 * (417 + sent.val)) := by
  funext byte
  have rawEq := response0_byte_eq leftBody rightBody leftLong rightLong same
    (16 * sent.val + byte.val) (by omega)
  simp only [AspisV8.SameBodyChunkParser.chunk, FSV7PrefixBridge.encode]
  rw [List.getD_eq_getElem _ _ (by simp; omega),
    List.getD_eq_getElem _ _ (by simp; omega)]
  simp only [List.getElem_map]
  simpa [show 16 * (417 + sent.val) + byte.val =
      6672 + (16 * sent.val + byte.val) by omega] using congrArg UInt8.toFin rawEq

/-- Equality of the exact 96-byte response0 slice of two successfully parsed
bodies determines equality of all six canonical field values consumed by
round zero. -/
theorem response0_parsed_eq
    (leftBody rightBody : Bytes)
    (leftValues rightValues : List K)
    (leftParsed : fields (FSV7PrefixBridge.encode leftBody) = some leftValues)
    (rightParsed : fields (FSV7PrefixBridge.encode rightBody) = some rightValues)
    (same : response0Bytes leftBody = response0Bytes rightBody) :
    response (wordOfValues leftValues) 0 =
      response (wordOfValues rightValues) 0 := by
  have leftChunkParsed : AspisV8.SameBodyChunkParser.fields
      (FSV7PrefixBridge.encode leftBody) = some leftValues := by
    rw [AspisV8.SameBodyChunkParser.fields_eq_parseFixed,
      ← AspisV8.SameBodySequentialCodec.fields_eq_parseFixed]
    exact leftParsed
  have rightChunkParsed : AspisV8.SameBodyChunkParser.fields
      (FSV7PrefixBridge.encode rightBody) = some rightValues := by
    rw [AspisV8.SameBodyChunkParser.fields_eq_parseFixed,
      ← AspisV8.SameBodySequentialCodec.fields_eq_parseFixed]
    exact rightParsed
  have leftFacts := AspisV8.SameBodyChunkParser.accepted_fields
    (FSV7PrefixBridge.encode leftBody) leftValues leftChunkParsed
  have rightFacts := AspisV8.SameBodyChunkParser.accepted_fields
    (FSV7PrefixBridge.encode rightBody) rightValues rightChunkParsed
  have leftLength : 6768 ≤ leftBody.length := by
    have guard := leftFacts.1
    simp [AspisV8.SameBodyChunkParser.sourceBadLength,
      FSV7PrefixBridge.encode] at guard
    omega
  have rightLength : 6768 ≤ rightBody.length := by
    have guard := rightFacts.1
    simp [AspisV8.SameBodyChunkParser.sourceBadLength,
      FSV7PrefixBridge.encode] at guard
    omega
  funext sent
  let index : Fin 697 := ⟨417 + sent.val, by omega⟩
  have leftDecoded := leftFacts.2.2 index
  have rightDecoded := rightFacts.2.2 index
  have chunkEq := response0_chunk_eq leftBody rightBody leftLength rightLength
    same sent
  have decodeEq := congrArg decodeQM31ExactLE chunkEq
  change leftValues.getD (417 + sent.val) 0 =
    rightValues.getD (417 + sent.val) 0
  exact Option.some.inj (leftDecoded.symm.trans (decodeEq.trans rightDecoded))

/-- Collector specialization: equal response0 slices in two successful
same-body replay cells force equality of the round-zero messages actually
used by `wordOf`.  Parser witnesses are constructed by each successful
functional run rather than supplied as a coherence premise. -/
theorem cell_response0_eq_of_bytes_eq
    {n m : Nat} {z : Fin 10 → K}
    {cuts : FSBoundedTranscript.RootCuts}
    {initialDigest : FSBoundedTranscript.Block}
    {firstWork : FSV8PostOODGammaScript.Point →
      FSOracleExecution.Script Bytes FSBoundedTranscript.Block Unit n}
    {secondWork : FSV8PostOODGammaScript.Point →
      FSV8PostOODGammaScript.Point →
      FSOracleExecution.Script Bytes FSBoundedTranscript.Block Unit m}
    (left right :
      ExtractionCollectorCausalMatrix.Cell n m z cuts initialDigest
        firstWork secondWork)
    (same : response0Bytes left.body = response0Bytes right.body) :
    ExtractionCollectorCausalMatrix.responseOf left 0 =
      ExtractionCollectorCausalMatrix.responseOf right 0 := by
  apply response0_parsed_eq left.body right.body
    (Classical.choose
      (ExtractionCollectorFinalMatrix.parser_values left.record))
    (Classical.choose
      (ExtractionCollectorFinalMatrix.parser_values right.record))
  · exact ExtractionCollectorFinalMatrix.final256_parser left.record
  · exact ExtractionCollectorFinalMatrix.final256_parser right.record
  · exact same

#print axioms response0_parsed_eq
#print axioms cell_response0_eq_of_bytes_eq

end AspisV8Completion.Response0ParsedBridge
