/-
TX1:137  crates/aspis-r1-cost-probe/src/r1_semantic.rs::verify_observed
Frozen signature (r1_semantic.rs:311):
  pub fn verify_observed<H: Digest32>(public: Public<'_>, bytes: &[u8], hash: H,
      obs: crate::verifier::Observer) -> Result<Verified<H>, Error>
Deployed instantiation (ruling (al)): H = SolanaDigest (the `hash` argument is
the unit value of that type and is not modelled further).
Route: emitted body under (bm) ((bh): verify_observed stager root).
Children: CLOSED Prefix::parse TX1:138, mark TX1:130 (no effect),
public_transcript TX1:131, wire::begin TX1:150 (mutates the transcript), OPEN
verify_finish TX1:136 (RowSpec_136 reference at SAME arguments: the public,
the parsed prefix by move, the transcript after begin, the challenges).
Own-input domain ((bf)(2)): `V.publicDom public ∧ V.semanticBytesDom bytes`
(the `public` clause of TX1:256 carried upward, and TX1:138's own clause on
`bytes`), recorded as caller clauses of TX1:087.  `obs` is not constrained:
r1_semantic::mark ignores it.
The remainder of `finishInputDom` (prefix provenance, transcript carry) must be
derived inside the root from the parse/public_transcript/begin laws; it is not
a hypothesis here.
Effects: the children's ordered events (public_transcript and begin digest
queries, then verify_finish's), abort = prefix.
-/
import NMT_R2_RSL_TX1_136
set_option autoImplicit false

namespace RSL.TX1_137

structure Args (V : VLib) where
  public_ : V.Public
  bytes : Bytes

def Ref (V : VLib) (a : Args V) : RE V.WErr (Verified V) :=
  RE.bind (V.parsePrefix.run a.bytes) fun pfx =>
  -- mark(obs, 0): no effect
  RE.bind (V.publicTranscript.run (a.public_, V.c1Root pfx)) fun t0 =>
  RE.bind (V.begin.run (pfx, t0)) fun r =>
  -- mark(obs, 1): no effect
  Spec.call (TX1_136.Domain V) (TX1_136.Ref V) ⟨a.public_, pfx, r.2, r.1⟩

def Domain (V : VLib) (a : Args V) : Prop := V.publicDom a.public_ ∧ V.semanticBytesDom a.bytes

def RowSpec_137 (V : VLib)
    (verify_observed : Args V → Observer → Env → Obs (Except V.WErr (Verified V))) : Prop :=
  ∀ a obs env, Domain V a → Ref V a env (verify_observed a obs env)

/-! ## Rejection of trivial implementations: as for TX1:136, the reference is
exactly the CLOSED parse law's Err (no events) at any bytes that Prefix::parse
rejects, e.g. a short buffer. -/

theorem rejects_constErr (V : VLib)
    (a : Args V) (ob : Observer) (w w' : V.WErr) (hd : Domain V a)
    (hlaw : ∀ env o, V.parsePrefix.law a.bytes env o ↔ o = ⟨.ret (.error w'), []⟩)
    (hne : w ≠ w') :
    ¬ RowSpec_137 V (fun _ (_ : Observer) _ => (⟨.ret (.error w), []⟩ : Obs (Except V.WErr (Verified V)))) := by
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

end RSL.TX1_137
