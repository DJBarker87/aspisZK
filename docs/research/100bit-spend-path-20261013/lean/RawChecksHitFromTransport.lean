import LiteralNoHitFromTranscriptAlignment
set_option autoImplicit false
namespace AspisR1.RawChecksHitFromTransport
theorem hitFrom_transport {X M C : Type}
    (bad : FS.Prefix X M C → M → C → Prop)
    {x y : X} (hxy : x = y) {rs ss : List (M × C)} (hrs : rs = ss) :
    AspisR1.GenericNoHit.hitFrom bad x [] rs ↔
      AspisR1.GenericNoHit.hitFrom bad y [] ss := by
  cases hxy
  cases hrs
  rfl
end AspisR1.RawChecksHitFromTransport
