/-
TX1:136  crates/aspis-r1-cost-probe/src/r1_semantic.rs::verify_finish
Frozen signature (r1_semantic.rs:232), prover feature off:
  fn verify_finish<H: Digest32>(public: Public<'_>, prefix: Prefix<'_>,
      transcript: SemanticTranscript<H>, challenges: Challenges,
      obs: crate::verifier::Observer) -> Result<Verified<H>, Error>
Deployed instantiation (ruling (al)): H = SolanaDigest.
Route: emitted body under (bm).
Children (all CLOSED, entering as `Child` packets of RSL_Verifier.VLib):
semantic_rounds TX1:134, mark TX1:130 (detail-phases off: `let _ = (obs, i)`,
no effect for every obs, so no obs clause is needed), claims TX1:129 (its own
allocation/Reservation arms are inside its law), terminal_qm31 TX1:256,
state_only_selected_mask_value TX1:076, validated_record TX1:141, decode_k
TX1:147, QM31 add/mul TX1:024/029, state TX1:146, circle_validated TX1:142,
payload TX1:139.
Own-input domain ((bf)(2)): `V.finishInputDom public prefix transcript
challenges` (see RSL_Verifier), recorded as a caller clause of TX1:137.
Effects: the children's ordered events (digest/oracle queries inside
semantic_rounds and the two circle_validated calls; the claims allocation),
concatenated in source order; abort arms carry only the prefix.  The
`try_into().unwrap()` on payload(2) is a panic arm unless payload(2) has 32
bytes.
-/
import NMT_RSL_Verifier
set_option autoImplicit false

namespace RSL.TX1_136

structure Args (V : VLib) where
  public_ : V.Public
  prefix_ : V.Prefix
  transcript : V.Transcript
  challenges : V.Challenges

def toB32 (b : Bytes) : Option B32 := if h : b.length = 32 then some ⟨b, h⟩ else none

def Ref (V : VLib) (a : Args V) : RE V.WErr (Verified V) :=
  RE.bind (V.semanticRounds.run (a.prefix_, a.transcript)) fun r =>
  let running := r.1
  let alpha := r.2.1
  let t1 := r.2.2
  -- mark(obs, 2): no effect
  RE.bind (V.claims.run a.prefix_) fun claims =>
  let orig := V.origChallenges a.challenges
  RE.bind (RE.mapErr (fun _ => V.wPublic) (V.terminalQm31.run (a.public_, claims, alpha, orig)))
    fun terminal =>
  -- mark(obs, 3): no effect
  let mask := V.maskValue claims alpha
  RE.bind (RE.ofExcept (V.validatedRecord a.prefix_ 25)) fun rec25 =>
  RE.bind (RE.ofExcept (V.decodeK29 rec25 87)) fun extra =>
  let masked := V.qadd (V.qadd mask (V.qmul (V.eta a.challenges) terminal)) (V.at28 extra)
  RE.seq (RE.check (decide (running ≠ masked)) V.wTerminal) <|
  -- mark(obs, 4): no effect
  let stateBefore := V.state t1
  RE.bind (RE.ofExcept (V.validatedRecord a.prefix_ 25)) fun rec25' =>
  RE.bind (V.circle.run (t1, rec25')) fun c0 =>
  let z0 := c0.1
  let t2 := c0.2
  RE.bind (RE.ofExcept (V.validatedRecord a.prefix_ 26)) fun rec26 =>
  RE.bind (RE.ofExcept (V.decodeK29 rec26 0)) fun beforeZ1 =>
  RE.bind (RE.ofExcept (V.validatedRecord a.prefix_ 26)) fun rec26' =>
  RE.bind (V.circle.run (t2, rec26')) fun c1 =>
  let z1 := c1.1
  let t3 := c1.2
  -- mark(obs, 5): no effect
  RE.seq (RE.check (decide (z0 = z1)) V.wEqualCirclePoints) <|
  RE.bind (RE.ofExcept (V.payload a.prefix_ 2)) fun p2 =>
  match toB32 p2 with
  | none => RE.lift Spec.panic
  | some root1 =>
    RE.pure { roots := (V.c1Root a.prefix_, root1), challenges := a.challenges, alpha := alpha,
              claims := claims, extra := extra, before_z1 := beforeZ1,
              state_before_z0 := stateBefore, z := (z0, z1), transcript := t3 }

def Domain (V : VLib) (a : Args V) : Prop :=
  V.finishInputDom a.public_ a.prefix_ a.transcript a.challenges

/-- `obs` is an argument of the frozen function; the reference is independent
of it (mark is a no-op without detail-phases), so it is quantified. -/
def RowSpec_136 (V : VLib)
    (verify_finish : Args V → Observer → Env → Obs (Except V.WErr (Verified V))) : Prop :=
  ∀ a obs env, Domain V a → Ref V a env (verify_finish a obs env)

/-! ## Rejection of trivial implementations

A constant `Err(w)` or a constant abort with no events is rejected whenever the
CLOSED semantic_rounds law, at some argument in the domain, admits a single
observation that is an Err different from `w` with no events (e.g. the first
round's Boundary error); the reference then forces exactly that Err.  Lean
statement: -/

theorem rejects_constErr (V : VLib) (a : Args V) (ob : Observer) (w w' : V.WErr)
    (hd : Domain V a)
    (hlaw : ∀ env o, V.semanticRounds.law (a.prefix_, a.transcript) env o ↔
              o = ⟨.ret (.error w'), []⟩)
    (hne : w ≠ w') :
    ¬ RowSpec_136 V (fun _ (_ : Observer) _ => (⟨.ret (.error w), []⟩ : Obs (Except V.WErr (Verified V)))) := by
  intro h
  have h1 := h a ob env0 hd
  unfold Ref RE.bind at h1
  rcases h1 with ⟨r, e1, o2, hm, hk, ho⟩ | ⟨e1, hm, _⟩ | ⟨e1, hm, _⟩
  · have hm' := (hlaw env0 _).mp hm.2
    simp only [Obs.mk.injEq, Exit.ret.injEq] at hm'
    rcases hm' with ⟨rfl, rfl⟩
    simp only [Spec.pure] at hk
    subst hk
    simp only [Obs.mk.injEq, Exit.ret.injEq, Except.error.injEq] at ho
    exact hne ho.1
  · have := (hlaw env0 _).mp hm.2; simp at this
  · have := (hlaw env0 _).mp hm.2; simp at this

end RSL.TX1_136
