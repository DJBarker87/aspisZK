import FSLiveSelectedMiddleQueryRho
import SameBodyChunkParser

set_option autoImplicit false

namespace AspisV8Completion.FSV8AlphaNonceBodyBridge
open FSLiveSelectedMiddleQueryRho
open AspisV8.SameBodyChunkParser
open AspisK1.V7Tag73TranscriptSchedule

abbrev Bytes := List UInt8

/- The body slice is converted to the typed V7 nonce only after room has been
   established.  The default in `getD` is therefore unreachable below. -/
def alpha0NonceOfBody (body : Bytes) : NonceBytes :=
  fun i => (alpha0NonceBytes body).getD i.val 0

theorem alpha0NonceOfBody_ofFn
    (body : Bytes) (bodyRoom : 11220 ≤ body.length) :
    List.ofFn (alpha0NonceOfBody body) = alpha0NonceBytes body := by
  unfold alpha0NonceOfBody alpha0NonceBytes
  apply List.ext_getElem
  · simp only [List.length_take, List.length_drop]
    have room : 8 ≤ body.length - 11212 := by omega
    simp [room]
  · intro index leftBound rightBound
    have indexBound : index < 8 := by
      simpa [List.length_take] using leftBound
    have offsetBound : 11212 + index < body.length := by omega
    simp only [List.getElem_take, List.getElem_ofFn]
    have dropBound : index < (body.drop 11212).length := by
      simp [List.length_drop]
      omega
    rw [List.getD]
    rw [List.getElem?_eq_getElem (by simpa [List.length_take] using rightBound)]
    simp [List.getElem_drop]

theorem alpha0NoncePayload_eq
    (body : Bytes) (bodyRoom : 11220 ≤ body.length) :
    0 :: List.ofFn (alpha0NonceOfBody body) =
      0 :: alpha0NonceBytes body := by
  rw [alpha0NonceOfBody_ofFn body bodyRoom]

theorem bodyRoom_of_fields_success
    (body : Bytes) (values : List FSNonzeroQM31.K)
    (success : fields (body.map UInt8.toFin) = some values) :
    11220 ≤ body.length := by
  have notBad := (accepted_fields (body.map UInt8.toFin) values success).1
  have shape := guard_frontier_shape (body.map UInt8.toFin).length
  have frontier := shape.mp notBad
  simp only [List.length_map] at frontier
  omega

theorem alpha0NoncePayload_of_fields_success
    (body : Bytes) (values : List FSNonzeroQM31.K)
    (success : fields (body.map UInt8.toFin) = some values) :
    0 :: List.ofFn (alpha0NonceOfBody body) =
      0 :: alpha0NonceBytes body := by
  exact alpha0NoncePayload_eq body (bodyRoom_of_fields_success body values success)

#print axioms alpha0NonceOfBody_ofFn
#print axioms bodyRoom_of_fields_success
#print axioms alpha0NoncePayload_of_fields_success

end AspisV8Completion.FSV8AlphaNonceBodyBridge
