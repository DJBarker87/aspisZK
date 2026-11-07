import RSL_TX1_136
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_Canonical136
open RSL

def root32 (V : VLib) (a : TX1_136.Args V) (alpha : V.Alpha) (claims : V.Claims)
    (extra before : V.K29) (state : B32) (z0 z1 : V.Point) (t3 : V.Transcript) (bytes : Bytes) :
    RE V.WErr (Verified V) :=
  match TX1_136.toB32 bytes with
  | none => RE.lift Spec.panic
  | some root => RE.pure (⟨(V.c1Root a.prefix_,root),a.challenges,alpha,claims,extra,before,state,(z0,z1),t3⟩ : Verified V)

def payload2 (V : VLib) (a : TX1_136.Args V) (alpha : V.Alpha) (claims : V.Claims)
    (extra before : V.K29) (state : B32) (z0 z1 : V.Point) (t3 : V.Transcript) : RE V.WErr (Verified V) :=
  RE.bind (RE.ofExcept (V.payload a.prefix_ 2)) (root32 V a alpha claims extra before state z0 z1 t3)

def circleGuard (V : VLib) (a : TX1_136.Args V) (alpha : V.Alpha) (claims : V.Claims)
    (extra before : V.K29) (state : B32) (z0 z1 : V.Point) (t3 : V.Transcript) : RE V.WErr (Verified V) :=
  RE.seq (RE.check (decide (z0 = z1)) V.wEqualCirclePoints) (payload2 V a alpha claims extra before state z0 z1 t3)

def circle1 (V : VLib) (a : TX1_136.Args V) (alpha : V.Alpha) (claims : V.Claims)
    (extra before : V.K29) (state : B32) (z0 : V.Point) (t2 : V.Transcript) (rec26 : V.Record) : RE V.WErr (Verified V) :=
  RE.bind (V.circle.run (t2,rec26)) fun c1 => circleGuard V a alpha claims extra before state z0 c1.1 c1.2

def record26b (V : VLib) (a : TX1_136.Args V) (alpha : V.Alpha) (claims : V.Claims)
    (extra before : V.K29) (state : B32) (z0 : V.Point) (t2 : V.Transcript) : RE V.WErr (Verified V) :=
  RE.bind (RE.ofExcept (V.validatedRecord a.prefix_ 26)) (circle1 V a alpha claims extra before state z0 t2)

def beforeZ1 (V : VLib) (a : TX1_136.Args V) (alpha : V.Alpha) (claims : V.Claims)
    (extra : V.K29) (state : B32) (z0 : V.Point) (t2 : V.Transcript) (rec26 : V.Record) : RE V.WErr (Verified V) :=
  RE.bind (RE.ofExcept (V.decodeK29 rec26 0)) fun before => record26b V a alpha claims extra before state z0 t2

def record26a (V : VLib) (a : TX1_136.Args V) (alpha : V.Alpha) (claims : V.Claims)
    (extra : V.K29) (state : B32) (z0 : V.Point) (t2 : V.Transcript) : RE V.WErr (Verified V) :=
  RE.bind (RE.ofExcept (V.validatedRecord a.prefix_ 26)) (beforeZ1 V a alpha claims extra state z0 t2)

def circle0 (V : VLib) (a : TX1_136.Args V) (alpha : V.Alpha) (claims : V.Claims)
    (extra : V.K29) (state : B32) (t1 : V.Transcript) (rec25 : V.Record) : RE V.WErr (Verified V) :=
  RE.bind (V.circle.run (t1,rec25)) fun c0 => record26a V a alpha claims extra state c0.1 c0.2

def record25b (V : VLib) (a : TX1_136.Args V) (alpha : V.Alpha) (claims : V.Claims)
    (extra : V.K29) (state : B32) (t1 : V.Transcript) : RE V.WErr (Verified V) :=
  RE.bind (RE.ofExcept (V.validatedRecord a.prefix_ 25)) (circle0 V a alpha claims extra state t1)

def stateBefore (V : VLib) (a : TX1_136.Args V) (alpha : V.Alpha) (claims : V.Claims)
    (extra : V.K29) (t1 : V.Transcript) : RE V.WErr (Verified V) :=
  RE.bind (RE.pure (V.state t1)) fun state => record25b V a alpha claims extra state t1

def terminalGuard (V : VLib) (a : TX1_136.Args V) (running masked : V.QM31)
    (alpha : V.Alpha) (claims : V.Claims) (extra : V.K29) (t1 : V.Transcript) : RE V.WErr (Verified V) :=
  RE.seq (RE.check (decide (running ≠ masked)) V.wTerminal) (stateBefore V a alpha claims extra t1)

def addExtra (V : VLib) (a : TX1_136.Args V) (running partialValue : V.QM31)
    (alpha : V.Alpha) (claims : V.Claims) (extra : V.K29) (t1 : V.Transcript) : RE V.WErr (Verified V) :=
  RE.bind (RE.pure (V.qadd partialValue (V.at28 extra))) fun masked => terminalGuard V a running masked alpha claims extra t1

def addMask (V : VLib) (a : TX1_136.Args V) (running mask product : V.QM31)
    (alpha : V.Alpha) (claims : V.Claims) (extra : V.K29) (t1 : V.Transcript) : RE V.WErr (Verified V) :=
  RE.bind (RE.pure (V.qadd mask product)) fun partialValue => addExtra V a running partialValue alpha claims extra t1

def multiply (V : VLib) (a : TX1_136.Args V) (running mask terminal : V.QM31)
    (alpha : V.Alpha) (claims : V.Claims) (extra : V.K29) (t1 : V.Transcript) : RE V.WErr (Verified V) :=
  RE.bind (RE.pure (V.qmul (V.eta a.challenges) terminal)) fun product => addMask V a running mask product alpha claims extra t1

def extra (V : VLib) (a : TX1_136.Args V) (running mask terminal : V.QM31)
    (alpha : V.Alpha) (claims : V.Claims) (t1 : V.Transcript) (rec25 : V.Record) : RE V.WErr (Verified V) :=
  RE.bind (RE.ofExcept (V.decodeK29 rec25 87)) fun ex => multiply V a running mask terminal alpha claims ex t1

def record25a (V : VLib) (a : TX1_136.Args V) (running mask terminal : V.QM31)
    (alpha : V.Alpha) (claims : V.Claims) (t1 : V.Transcript) : RE V.WErr (Verified V) :=
  RE.bind (RE.ofExcept (V.validatedRecord a.prefix_ 25)) (extra V a running mask terminal alpha claims t1)

def mask (V : VLib) (a : TX1_136.Args V) (running terminal : V.QM31)
    (alpha : V.Alpha) (claims : V.Claims) (t1 : V.Transcript) : RE V.WErr (Verified V) :=
  RE.bind (RE.pure (V.maskValue claims alpha)) fun value => record25a V a running value terminal alpha claims t1

def terminal (V : VLib) (a : TX1_136.Args V) (running : V.QM31)
    (alpha : V.Alpha) (claims : V.Claims) (t1 : V.Transcript) : RE V.WErr (Verified V) :=
  RE.bind (RE.mapErr (fun _ => V.wPublic)
    (V.terminalQm31.run (a.public_,claims,alpha,V.origChallenges a.challenges))) fun value =>
    mask V a running value alpha claims t1

def claims (V : VLib) (a : TX1_136.Args V) (running : V.QM31) (alpha : V.Alpha) (t1 : V.Transcript) :
    RE V.WErr (Verified V) :=
  RE.bind (V.claims.run a.prefix_) fun value => terminal V a running alpha value t1

def body (V : VLib) (a : TX1_136.Args V) : RE V.WErr (Verified V) :=
  RE.bind (V.semanticRounds.run (a.prefix_,a.transcript)) fun r => claims V a r.1 r.2.1 r.2.2

/-- Pure source steps are inserted only to align actual lexical occurrences.
They disappear by proved monad laws; the target remains the exact frozen Ref. -/
theorem body_ref (V : VLib) (a : TX1_136.Args V) : body V a = RSL.TX1_136.Ref V a := by
  simp only [body,claims,terminal,mask,record25a,extra,multiply,addMask,addExtra,
    terminalGuard,stateBefore,record25b,circle0,record26a,beforeZ1,record26b,circle1,
    circleGuard,payload2,root32,RSL.TX1_136.Ref,RE.bind_pure] <;> rfl
#print axioms body_ref
end AspisR1.NNG_Canonical136
