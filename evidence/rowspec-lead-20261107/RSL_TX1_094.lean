/-
TX1:094  crates/aspis-r1-cost-probe/src/candidate.rs::tx1
Frozen signature (candidate.rs:270):
  pub fn tx1<H: Digest32>(public: Public<'_>, public_bytes: &[u8], proof: &[u8], k: usize,
      hash: H, obs: Observer) -> Result<Vec<u8>, Error>
Deployed instantiation (ruling (al)): H = SolanaDigest, obs = None.
Route: emitted body under (bm).
Children: CLOSED parse_shape TX1:086, canonical_scan TX1:084, mark TX1:191 (no
effect at None), Accumulator::new TX1:174, batch_merkle TX1:081 (batch 0),
QueryGeometry::for_range TX1:181, BatchedWeights::new TX1:176, query_loop
TX1:088, BatchedWeights::finish TX1:175, checkpoint TX1:186; OPEN prepare
TX1:087 (RowSpec_087 reference at SAME arguments: public, proof, g = [E::ZERO;29],
obs).  The CLOSED children's (bf)(2) clauses (e.g. NLO-bf:TX1:094:TX1:081 len /
wire / canonical / rootValues for batch_merkle) are inside their `Child.dom`
and must be discharged here from parse_shape's and prepare's laws at SAME
arguments; they are not hypotheses of this row.
Own-input domain ((bf)(2)), caller clauses of TX1:328: (T1) obs = None;
(T2) V.publicDom public.
Revision 3 (ruling (bq), LIB0_ F2): the 087 call now requires 087's (R4)
`V.checkValuesDom proof[7031..7495]`.  It is NOT a new clause of this row: it
is discharged here, because canonical_scan (candidate.rs:54-55) runs
`compact::check_values(&proof[OFF_Y1..OFF_INACTIVE])?` first, at SAME proof,
before prepare.  The obligation is `R4Discharge V` (a property of the CLOSED
TX1:084 law NKL_ScanRoot, to be proved by the instantiation); `r4_of_scan`
shows it yields (R4) at the 087 call site.
NLJ094 defect avoided: the RowSpec constrains the observation of the ACTUAL
function (a total function of its arguments and oracle replies); it is not a
statement about an arbitrary invocation relation, so the empty relation does
not satisfy it (see `rejects_constErr`).
-/
import RSL_TX1_087
set_option autoImplicit false

namespace RSL.TX1_094

structure Args (V : VLib) where
  public_ : V.Public
  public_bytes : Bytes
  proof : Bytes
  k : Nat

def Ref (V : VLib) (P : PreparedNew V) (a : Args V) : RE V.VErr Bytes :=
  RE.seq (RE.check (a.k != SPLIT) V.vParse) <|
  RE.seq (V.parseShape.run a.proof) <|
  RE.seq (V.canonicalScan.run a.proof) <|
  -- mark(obs, Parsed): no effect
  RE.bind (Spec.bind (Spec.call (fun x : TX1_087.Args V => TX1_087.Domain V x none)
                (TX1_087.Ref V P) ⟨a.public_, a.proof, V.zeroE29⟩)
            (fun r => match r.1 with
              | .ok p => Spec.pure (.ok (p, r.2))
              | .error e => Spec.pure (.error e))) fun pg =>
  let p := pg.1
  let g := pg.2
  RE.bind (V.accNew.run ()) fun acc =>
  -- mark(obs, Prepare): no effect
  match TX1_136.toB32 (slice a.proof OFF_FOLDED_ROOT OFF_ROUND1) with
  | none => RE.lift Spec.panic
  | some folded =>
  RE.seq (V.batchMerkle.run (a.proof, p, folded, 0)) <|
  -- mark(obs, Merkle(0)): no effect
  RE.bind (V.geometry.run (p, 0, a.k)) fun geo =>
  RE.bind (V.weightsNew.run acc) fun pending =>
  RE.bind (V.queryLoop.run (a.proof, p, acc, g, geo, pending, a.k)) fun r =>
  RE.bind (RE.lift (V.finish.run (r.2, r.1))) fun acc2 =>
  RE.bind (RE.lift (V.checkpoint.run (p, acc2, a.proof, a.public_bytes))) fun bytes =>
  -- mark(obs, CheckpointWrite): no effect
  RE.pure bytes

/-- Revision 3: the canonical_scan law exports check_values on the y1 slice of
its SAME argument whenever it returns Ok(()). -/
def R4Discharge (V : VLib) : Prop :=
  ∀ (proof : Bytes) (env : Env) (ev : List Event),
    V.canonicalScan.law proof env ⟨.ret (.ok ()), ev⟩ →
    V.checkValuesDom (slice proof OFF_Y1 OFF_INACTIVE)

/-- Where (R4) is discharged: on the arm of `Ref` that reaches the 087 call,
`canonicalScan.run a.proof` has returned Ok(()), and the 087 argument has the
same proof, so 087's (R4) holds. -/
theorem r4_of_scan (V : VLib) (hR4 : R4Discharge V) (a : Args V) (env : Env) (ev : List Event)
    (hs : V.canonicalScan.run a.proof env ⟨.ret (.ok ()), ev⟩) :
    V.checkValuesDom (slice (⟨a.public_, a.proof, V.zeroE29⟩ : TX1_087.Args V).proof
      OFF_Y1 OFF_INACTIVE) :=
  hR4 a.proof env ev hs.2

def Domain (V : VLib) (_a : Args V) (obs : Observer) (pub : V.Public) : Prop :=
  obs = none ∧ V.publicDom pub

def RowSpec_094 (V : VLib) (P : PreparedNew V)
    (tx1 : Args V → Observer → Env → Obs (Except V.VErr Bytes)) : Prop :=
  ∀ a obs env, Domain V a obs a.public_ → Ref V P a env (tx1 a obs env)

/-! ## Rejection of trivial implementations

(i) `k ≠ 10` forces exactly Err(Parse) with no event.  (ii) at k = 10 with a
proof that parse_shape and canonical_scan accept (silently) and an allocation
failure of heap::filled, the reference forces exactly Err(Allocation).  Since
Parse ≠ Allocation in the frozen enum, no constant Err survives; (i) rejects a
constant abort. -/

theorem rejects_constErr (V : VLib) (P : PreparedNew V) (a : Args V) (e : V.VErr)
    (hne : V.vParse ≠ V.vAllocation) (hk : a.k = SPLIT) (hlen : a.proof.length = VPROOF_BYTES)
    (hpub : V.publicDom a.public_)
    (hy1 : V.checkValuesDom (slice a.proof OFF_Y1 OFF_INACTIVE))
    (hps : ∀ o, V.parseShape.run a.proof env0 o ↔ o = ⟨.ret (.ok ()), []⟩)
    (hcs : ∀ o, V.canonicalScan.run a.proof env0 o ↔ o = ⟨.ret (.ok ()), []⟩)
    (hfd : V.filled.dom (LOGICAL_SEMANTIC + LOGICAL_Y1))
    (hfill : ∀ o, V.filled.law (LOGICAL_SEMANTIC + LOGICAL_Y1) env0 o ↔ o = ⟨.ret (.error ()), []⟩) :
    ¬ RowSpec_094 V P (fun _ _ _ => ⟨.ret (.error e), []⟩) := by
  intro h
  have h1 := h { a with k := 0 } none env0 ⟨rfl, hpub⟩
  have h2 := h a none env0 ⟨rfl, hpub⟩
  unfold Ref at h1 h2
  have c1 : (({ a with k := 0 } : Args V).k != SPLIT) = true := by simp [SPLIT]
  rw [c1, RE.check_true, RE.seq_throw] at h1
  have c2 : (a.k != SPLIT) = false := by simp [hk]
  rw [c2, RE.check_false, RE.seq_pure] at h2
  unfold RE.seq at h2
  rw [RE.bind] at h2
  rw [Spec.bind_det _ _ env0 _ hps] at h2
  simp only at h2
  rw [RE.bind] at h2
  rw [Spec.bind_det _ _ env0 _ hcs] at h2
  simp only at h2
  have h087 : ∀ o, Spec.call (fun x : TX1_087.Args V => TX1_087.Domain V x none) (TX1_087.Ref V P)
      ⟨a.public_, a.proof, V.zeroE29⟩ env0 o ↔ o = ⟨.ret (.error V.vAllocation, V.zeroE29), []⟩ := by
    intro o
    rw [Spec.call_trivial _ _ _ ⟨hlen, rfl, hpub, hy1⟩]
    unfold TX1_087.Ref
    rw [Spec.bind_det _ _ env0 _ (TX1_087.front_alloc_err V _ env0 hfd hfill)]
    rfl
  rw [RE.bind] at h2
  rw [Spec.bind_det _ _ env0 _ (fun o => by rw [Spec.bind_det _ _ env0 _ h087]; rfl)] at h2
  simp [RE.throw, Spec.pure] at h1 h2
  rw [h1] at h2
  exact hne h2

end RSL.TX1_094
