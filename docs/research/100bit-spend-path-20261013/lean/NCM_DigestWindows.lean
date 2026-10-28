import NCM_KMXWindows
import Port4B_LeafCode

set_option autoImplicit false
namespace AspisR1.NCM_DigestWindows

/-- A symbolic byte offset covers a complete finite slice. Neither actual
length nor frame is inferred from the successful byte equality. -/
theorem slice {α : Type} [Inhabited α] (actual expected : List α)
    (length : actual.length=expected.length)
    (window : ∀ i, i<expected.length → actual[i]! = expected[i]!) : actual=expected := by
  apply List.ext_getElem
  · exact length
  · intro i ha he
    simpa only [getElem!_pos actual i ha,getElem!_pos expected i he] using window i he

/-- The separate grammar/left/right native windows compose to EXACT three
parts; equality of flattened bytes alone would not establish this boundary. -/
theorem parts {α : Type} [Inhabited α]
    (tag left right etag eleft eright : List α)
    (geometry : tag=etag ∧ left.length=eleft.length ∧ right.length=eright.length)
    (leftWindow : ∀ i, i<eleft.length → left[i]! = eleft[i]!)
    (rightWindow : ∀ i, i<eright.length → right[i]! = eright[i]!) :
    [tag,left,right]=[etag,eleft,eright] := by
  rw [geometry.1,slice left eleft geometry.2.1 leftWindow,
    slice right eright geometry.2.2 rightWindow]

/-- Pair independent argument and reply windows before using the unchanged
runtime digest realization. This theorem assumes no SHA implementation. -/
theorem request_reply {α : Type} [Inhabited α]
    (actual expected : List (List α)) (reply expectedReply : List α)
    (args : actual=expected) (size : reply.length=expectedReply.length)
    (returned : ∀ i, i<expectedReply.length → reply[i]! = expectedReply[i]!) :
    (actual,reply)=(expected,expectedReply) := by
  rw [args,slice reply expectedReply size returned]

#print axioms slice
#print axioms parts
#print axioms request_reply
end AspisR1.NCM_DigestWindows
