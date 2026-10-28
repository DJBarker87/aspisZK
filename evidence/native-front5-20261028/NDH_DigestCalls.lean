import Aeneas
set_option autoImplicit false
namespace NDH_DigestCalls
open Aeneas Aeneas.Std Result

/-- Value-level call records. Native pointer/length gates supply these parts;
sha256's value stays in RuntimeSha256Value, outside this transport lemma. -/
def parentParts (children : Fin 8 → List U8) : List (List U8) :=
  [ [24#u8], children 0, children 1, children 2, children 3,
    children 4, children 5, children 6, children 7 ]

def leafParts (tag : U8) (value salt : List U8) : List (List U8) :=
  [[16#u8,tag],value,salt]

theorem parent_reply (hash : List (List U8) → Result (List U8))
    (children : Fin 8 → List U8) (reply : List U8)
    (runtime_reply : hash (parentParts children) = ok reply) :
    (do let r ← hash (parentParts children); ok r) = ok reply := by
  rw [runtime_reply]; rfl

theorem leaf_reply (hash : List (List U8) → Result (List U8))
    (tag : U8) (value salt reply : List U8)
    (runtime_reply : hash (leafParts tag value salt) = ok reply) :
    (do let r ← hash (leafParts tag value salt); ok r) = ok reply := by
  rw [runtime_reply]; rfl

#print axioms parent_reply
#print axioms leaf_reply
end NDH_DigestCalls
