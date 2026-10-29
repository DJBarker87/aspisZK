import NDM_SnapshotRef.Funs
set_option autoImplicit false
namespace NDM_ProjectionTransport
open Aeneas Aeneas.Std Result

def pairMap {C P X Y : Type} (f : C → X) (g : P → Y)
 (reply : core.result.Result (C × P) U8) : core.result.Result (X × Y) U8 :=
 match reply with | .Ok (c,p)=>.Ok (f c,g p) | .Err e=>.Err e

/-- The extracted constructor reference commutes with scalar/array projections.
 No native field or callback law is asserted by this algebraic lemma. -/
theorem reference {C P X Y : Type} (f : C → X) (g : P → Y) (c : C) (p : P) (valid : Bool) :
 (do let reply ← NDM_SnapshotRef.validation_ref c p valid
     ok (pairMap f g reply)) = NDM_SnapshotRef.validation_ref (f c) (g p) valid := by
 cases valid <;> rfl

#print axioms reference
end NDM_ProjectionTransport
