import Std

/-! IMPORTED FIRST ATTEMPT; COMPILED IN THIS WORKSTREAM.
A privacy observer does NOT see honest prover-private hash inputs, leaf seeds
or the full source oracle cache. A soundness extractor's full shared log must
not accidentally be used as the observer's public view.
-/
set_option autoImplicit false
namespace AspisV8Privacy
abbrev Bytes := List UInt8
abbrev FullDigest := Fin 32 → UInt8

inductive PublicEvent where
  | published (bytes : Bytes)
  | adversaryReply (input : Bytes) (answer : FullDigest)
  | finished (success : Bool) (publicCode : Nat)

inductive InternalEvent where
  | privateHash (input : Bytes) (answer : FullDigest)
  | publicEvent (event : PublicEvent)

/-- The source adapter must derive visibility labels from WHO issued a call,
not just its byte prefix: an adversary may submit a valid leaf-domain query. -/
def visible : InternalEvent → Option PublicEvent
  | .privateHash _ _ => none
  | .publicEvent e => some e

def publicProjection (trace : List InternalEvent) : List PublicEvent :=
  trace.filterMap visible

theorem projection_append (left right : List InternalEvent) :
    publicProjection (left ++ right) = publicProjection left ++ publicProjection right := by
  simp [publicProjection]

theorem private_event_not_directly_disclosed (input : Bytes) (answer : FullDigest)
    (left right : List InternalEvent) :
    publicProjection (left ++ .privateHash input answer :: right) =
      publicProjection (left ++ right) := by
  simp [publicProjection, visible]

/-- This only states what is not DIRECTLY revealed. A later public root,
opening, status or oracle reply can still depend on a private event. -/
theorem published_event_retained (e : PublicEvent) (rest : List InternalEvent) :
    publicProjection (.publicEvent e :: rest) = e :: publicProjection rest := by
  rfl

#print axioms projection_append
#print axioms private_event_not_directly_disclosed
#print axioms published_event_retained
end AspisV8Privacy
