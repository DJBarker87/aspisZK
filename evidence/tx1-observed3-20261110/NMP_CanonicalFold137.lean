import NMP_SpecRefines
set_option autoImplicit false
namespace AspisR1.NMP_CanonicalFold137
open RSL NMP_SpecRefines
/-- Canonical child136 invocation packet at the actual reached tuple. The
Domain conjunct is a caller obligation, not an inserted runtime check.
This is a relational fold support object, never an actual producer. -/
def call136 (V : VLib)
 (finish : TX1_136.Args V → Observer → Env → Obs (Except V.WErr (Verified V)))
 (a : TX1_136.Args V) (obs : Observer) : RE V.WErr (Verified V) :=
 Spec.call (TX1_136.Domain V) (fun a env o => o=finish a obs env) a

def body (V : VLib)
 (finish : TX1_136.Args V → Observer → Env → Obs (Except V.WErr (Verified V)))
 (a : TX1_137.Args V) (obs : Observer) : RE V.WErr (Verified V) :=
 RE.bind (V.parsePrefix.run a.bytes) fun pfx =>
 RE.bind (V.publicTranscript.run (a.public_,V.c1Root pfx)) fun t0 =>
 RE.bind (V.begin.run (pfx,t0)) fun r =>
 call136 V finish ⟨a.public_,pfx,r.2,r.1⟩ obs

/-- The only open CHILD LAW is EXACTLY canonical RowSpec_136. Every event and
abort prefix is transported by the relational bind, at SAME call arguments.
The emitted producer/closed-library interpretation and caller domains must
still be installed; this intermediate theorem is not a RowSpec_137 root. -/
theorem fold (V : VLib)
 (finish : TX1_136.Args V → Observer → Env → Obs (Except V.WErr (Verified V)))
 (child : TX1_136.RowSpec_136 V finish) (a : TX1_137.Args V) (obs : Observer) :
 Refines (body V finish a obs) (TX1_137.Ref V a) := by
 unfold body TX1_137.Ref
 apply result_bind _ _ _ _ (fun _ _ h => h)
 intro pfx
 apply result_bind _ _ _ _ (fun _ _ h => h)
 intro t0
 apply result_bind _ _ _ _ (fun _ _ h => h)
 intro r env o h
 rcases h with ⟨hd,ho⟩
 subst o
 exact ⟨hd,child _ obs env hd⟩
#print axioms fold
end AspisR1.NMP_CanonicalFold137
