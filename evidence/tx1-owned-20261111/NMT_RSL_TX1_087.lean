/-
TX1:087  crates/aspis-r1-cost-probe/src/candidate.rs::prepare
Frozen signature (candidate.rs:255):
  fn prepare<H: Digest32>(public: Public<'_>, proof: &[u8], hash: H, obs: Observer,
      g: &mut [E; 29]) -> Result<Box<Prepared>, Error>
Deployed instantiation (ruling (al)): H = SolanaDigest, obs = observer() = None.
Route: emitted body under (bm) ((bh)).
Children: CLOSED heap::filled TX1:064 (14759 zero bytes; allocation failure is
its Err value, mapped to Error::Allocation), expand_semantic TX1:098 and
expand_values TX1:099 (write the two disjoint halves 13831/928 of the SAME
buffer; CodecError -> Error::Parse), wide_view TX1:095, verifier::mark TX1:191
(no effect at obs = None), Prepared::new TX1:179 (writes g); OPEN
verify_observed TX1:137 (RowSpec_137 reference at SAME arguments: public and
the expanded semantic half; any Err -> Error::Semantic).
Own-input domain ((bf)(2)), caller clauses of TX1:094:
  (R1) proof.len() = 57607 (the slices at 16..7031, 7031..7495 and the wide
       fields are then in range; NLO-bf:TX1:087:081:len);
  (R2) obs = None;
  (R3) V.publicDom public (carried from TX1:137).
`g` is a &mut argument: its final value is part of the result on every
returning arm (unchanged on the arms before Prepared::new).  The `logical`
Vec and the Verified value are dropped at return; the drops write no account
or return data and are outside the obligation ((bl)(3)).
-/
import NMT_RSL_TX1_137
set_option autoImplicit false

namespace RSL.TX1_087

structure Args (V : VLib) where
  public_ : V.Public
  proof : Bytes
  g : V.E29

/-- The fallible prefix up to (excluding) Prepared::new: returns the Verified
value and the View. -/
def front (V : VLib) (a : Args V) : RE V.VErr (Verified V × V.View) :=
  RE.bind (RE.mapErr (fun _ => V.vAllocation) (V.filled.run (LOGICAL_SEMANTIC + LOGICAL_Y1)))
    fun logical =>
  let semantic0 := logical.take LOGICAL_SEMANTIC
  let y10 := logical.drop LOGICAL_SEMANTIC
  RE.bind (RE.mapErr V.codecToV (V.expandSemantic.run (slice a.proof OFF_SEMANTIC OFF_Y1, semantic0)))
    fun semantic =>
  RE.bind (RE.mapErr V.codecToV (V.expandValues.run (slice a.proof OFF_Y1 OFF_INACTIVE, y10)))
    fun y1 =>
  RE.bind (V.wideView.run (a.proof, semantic, y1)) fun v =>
  RE.bind (RE.mapErr (fun _ => V.vSemantic)
      (Spec.call (TX1_137.Domain V) (TX1_137.Ref V) ⟨a.public_, V.viewSemantic v⟩)) fun sem =>
  -- mark(obs, Phase::Semantic): no effect at obs = None
  RE.pure (sem, v)

/-- Reference: returns (Result<Box<Prepared>, Error>, final g). -/
def Ref (V : VLib) (P : PreparedNew V) (a : Args V) : Spec (Except V.VErr V.Prepared × V.E29) :=
  Spec.bind (front V a) fun r =>
  match r with
  | .error e => Spec.pure (.error e, a.g)
  | .ok (sem, v) => P.run (sem, v, a.g)

def Domain (V : VLib) (a : Args V) (obs : Observer) : Prop :=
  a.proof.length = VPROOF_BYTES ∧ obs = none ∧ V.publicDom a.public_

def RowSpec_087 (V : VLib) (P : PreparedNew V)
    (prepare : Args V → Observer → Env → Obs (Except V.VErr V.Prepared × V.E29)) : Prop :=
  ∀ a obs env, Domain V a obs → Ref V P a env (prepare a obs env)

/-! ## Rejection of trivial implementations

If the CLOSED heap::filled law admits only its Err at 14759 (allocation
failure value) the reference forces exactly (Err(Allocation), g); if it admits
only Ok, the next steps run.  The Lean check below shows the reference
pins the g component: an implementation that returns an Err with a g
different from the input g, before Prepared::new, is rejected. -/

theorem front_alloc_err (V : VLib) (a : Args V) (env : Env)
    (hfd : V.filled.dom (LOGICAL_SEMANTIC + LOGICAL_Y1))
    (hfill : ∀ o, V.filled.law (LOGICAL_SEMANTIC + LOGICAL_Y1) env o ↔ o = ⟨.ret (.error ()), []⟩)
    (o : Obs (Except V.VErr (Verified V × V.View))) :
    front V a env o ↔ o = ⟨.ret (.error V.vAllocation), []⟩ := by
  unfold front
  apply RE.bind_err_det
  intro o'
  rw [RE.mapErr_det _ _ env (.error ()) (Child.run_det _ _ env _ hfd hfill)]
  rfl

theorem rejects_wrong_g (V : VLib) (P : PreparedNew V) (a : Args V) (g' : V.E29) (e : V.VErr)
    (hg : g' ≠ a.g) (hd : Domain V a none)
    (hfd : V.filled.dom (LOGICAL_SEMANTIC + LOGICAL_Y1))
    (hfill : ∀ o, V.filled.law (LOGICAL_SEMANTIC + LOGICAL_Y1) env0 o ↔ o = ⟨.ret (.error ()), []⟩) :
    ¬ RowSpec_087 V P (fun _ _ _ => ⟨.ret (.error e, g'), []⟩) := by
  intro h
  have h1 := h a none env0 hd
  unfold Ref at h1
  rw [Spec.bind_det _ _ env0 _ (front_alloc_err V a env0 hfd hfill)] at h1
  simp only [Spec.pure, Obs.mk.injEq, Exit.ret.injEq, Prod.mk.injEq] at h1
  exact hg h1.1.2

end RSL.TX1_087
