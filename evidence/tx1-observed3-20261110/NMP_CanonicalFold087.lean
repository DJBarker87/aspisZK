import NMP_SpecRefines
set_option autoImplicit false
namespace AspisR1.NMP_CanonicalFold087
open RSL NMP_SpecRefines

def call137 (V : VLib)
 (observed : TX1_137.Args V → Observer → Env → Obs (Except V.WErr (Verified V)))
 (a : TX1_137.Args V) (obs : Observer) : RE V.WErr (Verified V) :=
 Spec.call (TX1_137.Domain V) (fun a env o => o=observed a obs env) a

def front (V : VLib)
 (observed : TX1_137.Args V → Observer → Env → Obs (Except V.WErr (Verified V)))
 (a : TX1_087.Args V) (obs : Observer) : RE V.VErr (Verified V × V.View) :=
 RE.bind (RE.mapErr (fun _ => V.vAllocation) (V.filled.run (LOGICAL_SEMANTIC+LOGICAL_Y1))) fun logical =>
 let semantic0 := logical.take LOGICAL_SEMANTIC
 let y10 := logical.drop LOGICAL_SEMANTIC
 RE.bind (RE.mapErr V.codecToV (V.expandSemantic.run (slice a.proof OFF_SEMANTIC OFF_Y1,semantic0))) fun semantic =>
 RE.bind (RE.mapErr V.codecToV (V.expandValues.run (slice a.proof OFF_Y1 OFF_INACTIVE,y10))) fun y1 =>
 RE.bind (V.wideView.run (a.proof,semantic,y1)) fun v =>
 RE.bind (RE.mapErr (fun _ => V.vSemantic) (call137 V observed ⟨a.public_,V.viewSemantic v⟩ obs)) fun sem =>
 RE.pure (sem,v)

def body (V : VLib) (P : PreparedNew V)
 (observed : TX1_137.Args V → Observer → Env → Obs (Except V.WErr (Verified V)))
 (a : TX1_087.Args V) (obs : Observer) : Spec (Except V.VErr V.Prepared × V.E29) :=
 Spec.bind (front V observed a obs) fun r => match r with
 | .error e => Spec.pure (.error e,a.g)
 | .ok (sem,v) => P.run (sem,v,a.g)

/-- Full canonical087 relation, parameterized ONLY in canonical137's child
law. The179 interface here is the complete PreparedNew packet, not its
successful-only theorem. Actual179 installation remains an explicit gap. -/
theorem fold (V : VLib) (P : PreparedNew V)
 (observed : TX1_137.Args V → Observer → Env → Obs (Except V.WErr (Verified V)))
 (child : TX1_137.RowSpec_137 V observed) (a : TX1_087.Args V) (obs : Observer) :
 Refines (body V P observed a obs) (TX1_087.Ref V P a) := by
 unfold body TX1_087.Ref
 apply bind _ _ _ _ ?_ (fun _ _ _ h => h)
 unfold front TX1_087.front
 apply result_bind _ _ _ _ (fun _ _ h => h)
 intro logical
 apply result_bind _ _ _ _ (fun _ _ h => h)
 intro semantic
 apply result_bind _ _ _ _ (fun _ _ h => h)
 intro y1
 apply result_bind _ _ _ _ (fun _ _ h => h)
 intro v
 apply result_bind _ _ _ _ ?_ (fun _ _ _ h => h)
 unfold RE.mapErr Spec.map
 apply bind _ _ _ _ ?_ (fun _ _ _ h => h)
 intro env o h
 rcases h with ⟨hd,ho⟩
 subst o
 exact ⟨hd,child _ obs env hd⟩
#print axioms fold
end AspisR1.NMP_CanonicalFold087
