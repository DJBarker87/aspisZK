import RSL_TX1_136
import NNG_EmittedContext
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_Row136Fold
open RSL

/-- The target is the observation of the fresh emitted function. The input
and observation transports are explicit until LIB supplies its carriers.
This definition is a target, not a proof or an installed VLib instance. -/
def Target {H W : Type} (VL : VLib) (c : NNG_Emitted.Calls)
    (input : TX1_136.Args VL → Observer → Env → NNG_Emitted.Parent H W)
    (observe : TX1_136.Args VL → Observer → Env →
      Aeneas.Std.Result (NNG_Emitted.Output H) → Obs (Except VL.WErr (Verified VL))) : Prop :=
  RSL.TX1_136.RowSpec_136 VL
    (fun a obs env => observe a obs env (NNG_Emitted.emitted c (input a obs env)))

/-- Interpreted source calls, not VLib field instances. Each effectful call
includes its own domain and complete observation, including stopped prefixes.
LIB owns the field instances and the CLOSED-model graph evidence below. -/
structure Calls (VL : VLib) where
  semanticRounds : VL.Prefix × VL.Transcript → RE VL.WErr (VL.QM31 × VL.Alpha × VL.Transcript)
  claims : VL.Prefix → RE VL.WErr VL.Claims
  terminalQm31 : VL.Public × VL.Claims × VL.Alpha × VL.OrigChallenges → RE Unit VL.QM31
  circle : VL.Transcript × VL.Record → RE VL.WErr (VL.Point × VL.Transcript)
  validatedRecord : VL.Prefix → Nat → Except VL.WErr VL.Record
  decodeK29 : VL.Record → Nat → Except VL.WErr VL.K29
  payload : VL.Prefix → Nat → Except VL.WErr Bytes
  qadd : VL.QM31 → VL.QM31 → VL.QM31
  qmul : VL.QM31 → VL.QM31 → VL.QM31
  maskValue : VL.Claims → VL.Alpha → VL.QM31

/-- These equalities must be proved from graphs of CLOSED deterministic
models. In particular the rounds model is PreparedHashCode.run of
S1SemanticCode.rounds, never NJM_RoundsInduction.chain's native-cut image.
This conditional fold does not discharge or invent any of these laws. -/
structure FieldGraphs (VL : VLib) (c : Calls VL) : Prop where
  semanticRounds : ∀ x, c.semanticRounds x = VL.semanticRounds.run x
  claims : ∀ x, c.claims x = VL.claims.run x
  terminalQm31 : ∀ x, c.terminalQm31 x = VL.terminalQm31.run x
  circle : ∀ x, c.circle x = VL.circle.run x
  validatedRecord : ∀ p i, c.validatedRecord p i = VL.validatedRecord p i
  decodeK29 : ∀ r i, c.decodeK29 r i = VL.decodeK29 r i
  payload : ∀ p i, c.payload p i = VL.payload p i
  qadd : ∀ x y, c.qadd x y = VL.qadd x y
  qmul : ∀ x y, c.qmul x y = VL.qmul x y
  maskValue : ∀ claims alpha, c.maskValue claims alpha = VL.maskValue claims alpha

/-- Source-order relational body after standard-library and carrier
interpretation. The emitted-to-interpreted association is a separate obligation;
this body alone is not the producer named in Target. -/
def body (VL : VLib) (c : Calls VL) (a : TX1_136.Args VL) : RE VL.WErr (Verified VL) :=
  RE.bind (c.semanticRounds (a.prefix_, a.transcript)) fun r =>
  let running := r.1
  let alpha := r.2.1
  let t1 := r.2.2
  RE.bind (c.claims a.prefix_) fun claims =>
  let orig := VL.origChallenges a.challenges
  RE.bind (RE.mapErr (fun _ => VL.wPublic) (c.terminalQm31 (a.public_, claims, alpha, orig))) fun terminal =>
  let mask := c.maskValue claims alpha
  RE.bind (RE.ofExcept (c.validatedRecord a.prefix_ 25)) fun rec25 =>
  RE.bind (RE.ofExcept (c.decodeK29 rec25 87)) fun extra =>
  let masked := c.qadd (c.qadd mask (c.qmul (VL.eta a.challenges) terminal)) (VL.at28 extra)
  RE.seq (RE.check (decide (running ≠ masked)) VL.wTerminal) <|
  let stateBefore := VL.state t1
  RE.bind (RE.ofExcept (c.validatedRecord a.prefix_ 25)) fun rec25' =>
  RE.bind (c.circle (t1, rec25')) fun c0 =>
  let z0 := c0.1
  let t2 := c0.2
  RE.bind (RE.ofExcept (c.validatedRecord a.prefix_ 26)) fun rec26 =>
  RE.bind (RE.ofExcept (c.decodeK29 rec26 0)) fun beforeZ1 =>
  RE.bind (RE.ofExcept (c.validatedRecord a.prefix_ 26)) fun rec26' =>
  RE.bind (c.circle (t2, rec26')) fun c1 =>
  let z1 := c1.1
  let t3 := c1.2
  RE.seq (RE.check (decide (z0 = z1)) VL.wEqualCirclePoints) <|
  RE.bind (RE.ofExcept (c.payload a.prefix_ 2)) fun p2 =>
  match TX1_136.toB32 p2 with
  | none => RE.lift Spec.panic
  | some root1 =>
    RE.pure { roots := (VL.c1Root a.prefix_, root1), challenges := a.challenges, alpha := alpha,
      claims := claims, extra := extra, before_z1 := beforeZ1, state_before_z0 := stateBefore,
      z := (z0, z1), transcript := t3 }

/-- Once the interpreted occurrences equal their fields, the ENTIRE relation
is the frozen Ref, including every Result, event order and stopped prefix.
No endpoint or successful-child equation is a hypothesis. This remains
conditional support until the emitted association and LIB laws are installed. -/
theorem fold (VL : VLib) (c : Calls VL) (h : FieldGraphs VL c) (a : TX1_136.Args VL) :
    body VL c a = RSL.TX1_136.Ref VL a := by
  simp only [body, TX1_136.Ref, h.semanticRounds, h.claims, h.terminalQm31,
    h.circle, h.validatedRecord, h.decodeK29, h.payload, h.qadd, h.qmul, h.maskValue]
#print axioms fold
end AspisR1.NNG_Row136Fold
