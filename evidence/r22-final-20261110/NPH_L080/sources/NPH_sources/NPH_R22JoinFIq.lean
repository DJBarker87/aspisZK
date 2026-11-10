import NPH_R22FIqTerminal
import NPH_R22JoinSM7

/-! NPH_ (R22, FIq step 2): the FIq terminal composed to the deployed 345 entry.
- `finish_term_congr` (generic): FinishModel.finish with the terminal slot replaced by t' equals
  the original whenever t' agrees with the terminal at the arguments the finish passes: the
  public, the claims of the SAME successful claims call and the alpha of the SAME successful
  rounds call (`NPH_R22JoinSM3.Head`).
- `gterm`: the terminal that runs FIq_Terminal.terminal only on NLU_Terminal.InputDomain with
  canonical claims and alpha (otherwise fail). `term_site`: wherever gterm runs the terminal,
  the terminal is ok (NPH_R22FIqTerminal.terminal_total), so every FIq kernel call inside it
  returned ok.
- `BslotT r`: NPH_R22JoinSM5.Bslot r (mask/add/mul guarded) with terminal := gterm.
  `deployed_finish_guardedT`/`deployed_verify_guardedT`: the finish and verify over BslotT equal
  those over the deployed record, given the public digest domain (the InputDomain is derived as in
  NPH_R22JoinSM4.deployed_verify_guarded).
- `slotM_guardedT`, `tx1_guardedMT`, `GT`, `GT_agree`, `stage1_guardedT`: the NPH_R22JoinSM7
  chain with BslotT in place of Bslot. `stage1_guardedT` has NO premise: every execution of the
  deployed 345 entry equals the execution over GT c, whose tx1 semantic finish runs the FIq
  terminal only on its input domain. Standard axioms. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.NPH_R22JoinFIq
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation
open AspisR1.NPH_R22JoinSM3 (Q Claims bind_congr_ok branch_cont Head verify_congr)

theorem finish_term_congr (R : RoundModel.Boundaries) (B : FinishModel.Boundaries)
    (t' : FIq_Carriers.Public → Claims → Array Q 10#usize → r1_wire.Challenges →
      Result (core.result.Result Q FIq_Terminal.Error))
    {H : Type} (D : aspis_core.Digest32 H) (pub : pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pre : r1_wire.Prefix) (t : r1_wire.SemanticTranscript H) (ch : r1_wire.Challenges)
    (obs : Option (RPz7_PhaseIso.Phase → Result Unit))
    (hterm : ∀ (running : Q) (alpha : Array Q 10#usize) (t1 : r1_wire.SemanticTranscript H) (v1 : Claims),
      Head R B D pre t running alpha t1 v1 → t' pub v1 alpha ch = B.terminal pub v1 alpha ch) :
    FinishModel.finish R { B with terminal := t' } D pub pre t ch obs =
      FinishModel.finish R B D pub pre t ch obs := by
  unfold FinishModel.finish
  refine bind_congr_ok _ _ _ (fun r hr => ?_)
  refine bind_congr_ok _ _ _ (fun cf hcf => ?_)
  cases cf with
  | Break res => dsimp only
  | Continue val =>
  obtain ⟨running, alpha, t1⟩ := val
  have hR : RoundModel.rounds R D pre t = ok (.Ok (running, alpha, t1)) := by
    rw [hr, (branch_cont r _).1 hcf]
  refine bind_congr_ok _ _ _ (fun u2 _ => ?_)
  refine bind_congr_ok _ _ _ (fun r1 hr1 => ?_)
  refine bind_congr_ok _ _ _ (fun cf1 hcf1 => ?_)
  cases cf1 with
  | Break res => dsimp only
  | Continue v1 =>
  have hC : B.claims pre = ok (.Ok v1) := by
    have e := (branch_cont r1 _).1 hcf1; subst e; exact hr1
  show (t' pub v1 alpha ch >>= _) = _
  rw [hterm running alpha t1 v1 ⟨hR, hC⟩]
  rfl
#print axioms finish_term_congr

/-- The terminal input domain at a finish call. -/
def TermDom (pub : FIq_Carriers.Public) (claims : Claims) (alpha : Array Q 10#usize)
    (c : r1_wire.Challenges) : Prop :=
  NLU_Terminal.InputDomain pub c ∧ (∀ row ∈ claims.val, ∀ q ∈ row.val, NPH_R22JoinSM4.Canon q) ∧
    NPH_R22JoinSM4.AllC alpha

open Classical in
def gterm (pub : FIq_Carriers.Public) (claims : Claims) (alpha : Array Q 10#usize)
    (c : r1_wire.Challenges) : Result (core.result.Result Q FIq_Terminal.Error) :=
  if TermDom pub claims alpha c then FIq_Terminal.terminal pub claims alpha c
  else fail Aeneas.Std.Error.panic

theorem term_site (pub : FIq_Carriers.Public) (claims : Claims) (alpha : Array Q 10#usize)
    (c : r1_wire.Challenges) :
    gterm pub claims alpha c = fail Aeneas.Std.Error.panic ∨
    (TermDom pub claims alpha c ∧ gterm pub claims alpha c = FIq_Terminal.terminal pub claims alpha c ∧
      ∃ out, FIq_Terminal.terminal pub claims alpha c = ok out) := by
  by_cases hd : TermDom pub claims alpha c
  · right
    refine ⟨hd, by unfold gterm; rw [if_pos hd], ?_⟩
    exact NPH_R22FIqTerminal.terminal_total pub claims alpha c hd.1
      (NPH_R22JoinSM4.mapped_rows claims hd.2.1) (NPH_R22JoinSM4.mapped_array alpha hd.2.2)
  · left
    unfold gterm
    rw [if_neg hd]
#print axioms term_site

theorem deployed_finish_guardedT (std : ClaimsUnrolledFinish.StdCalls) (r : NP6_StdModel.Reservation)
    {H : Type} (D : aspis_core.Digest32 H) (pub : pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pre : r1_wire.Prefix) (t : r1_wire.SemanticTranscript H) (ch : r1_wire.Challenges)
    (obs : Option (RPz7_PhaseIso.Phase → Result Unit))
    (heta : NPH_R22JoinSM4.Canon ch.eta) (hdom : NLU_Terminal.InputDomain pub ch) :
    FinishModel.finish AspisS1ExtractedRoundChildren.children
        { NPH_R22JoinSM4.Bg std r with terminal := gterm } D pub pre t ch obs =
      FinishModel.finish AspisS1ExtractedRoundChildren.children (NPH_R22JoinSM4.Bd std r) D pub pre t ch obs := by
  rw [← NPH_R22JoinSM4.deployed_finish_guarded std r D pub pre t ch obs heta hdom]
  apply finish_term_congr
  intro running alpha t1 v1 hH
  obtain ⟨hR, hC⟩ := hH
  have hc := NPH_R22JoinSM4.claims_canon std r pre v1 hC
  have hal := NPH_R22JoinSM4.alpha_canon _ D pre t t1 running alpha hR
  show gterm pub v1 alpha ch = FIq_Terminal.terminal pub v1 alpha ch
  unfold gterm
  rw [if_pos ⟨hdom, hc, hal⟩]
#print axioms deployed_finish_guardedT

theorem deployed_verify_guardedT (std : ClaimsUnrolledFinish.StdCalls) (r : NP6_StdModel.Reservation)
    {H : Type} (D : aspis_core.Digest32 H) (pub : pool_v1.pair_forest_semantic_terminal.r0.Public)
    (bytes : Slice U8) (hash : H) (obs : Option (RPz7_PhaseIso.Phase → Result Unit))
    (hdig : LIB_VPublicDomain.publicDigestDom pub) :
    VerifyPrefix.verify (FinishModel.finish AspisS1ExtractedRoundChildren.children
        { NPH_R22JoinSM4.Bg std r with terminal := gterm }) D pub bytes hash obs =
      VerifyPrefix.verify (FinishModel.finish AspisS1ExtractedRoundChildren.children
        (NPH_R22JoinSM4.Bd std r)) D pub bytes hash obs := by
  apply verify_congr
  intro p t t' c hp ht hb
  obtain ⟨hl, hchi, hth, hmu, heta, hz⟩ := FJn_BeginCanonical.value D p t t' c hb
  obtain ⟨bytes', hbytes, -⟩ := PreparationSuccess.public_transcript_success D pub hash p.c1_root t ht
  have hasset := LIB_VPublicAsset.bytes_asset pub bytes' hbytes
  have hdom : NLU_Terminal.InputDomain pub c :=
    ⟨hdig, hasset, NPH_R22JoinSM4.mapped_array c.zc hz, hl, hchi, hth, hmu⟩
  exact deployed_finish_guardedT std r D pub p t' c obs heta hdom
#print axioms deployed_verify_guardedT

/-- The slot record: Bslot (guarded mask/add/mul) with the guarded terminal. -/
def BslotT (r : NP6_StdModel.Reservation) : FinishModel.Boundaries :=
  { NPH_R22JoinSM5.Bslot r with terminal := gterm }

theorem bgT_eq (r : NP6_StdModel.Reservation) :
    { NPH_R22JoinSM4.Bg (NP6_StdModel.calls r) r with terminal := gterm } =
      S1SemanticRootCopy.install (BslotT r) := rfl
#print axioms bgT_eq

theorem slotT_kernels (r : NP6_StdModel.Reservation) :
    (BslotT r).terminal = gterm ∧ (BslotT r).mask = NPH_R22JoinSM4.gmask ∧
    (BslotT r).add = NPH_R22JoinSM4.gadd ∧ (BslotT r).mul = NPH_R22JoinSM4.gmul := ⟨rfl, rfl, rfl, rfl⟩
#print axioms slotT_kernels

section deployed
open AspisR1CurrentCaller

theorem slotM_guardedT (m : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE) (env : RSL.Env)
    (err : NFN_NEW_GeometryDictionary.CE) (r : NP6_StdModel.Reservation)
    (D : aspis_core.digest.Digest32 Unit)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public) (bytes : Slice U8)
    (hdig : LIB_VPublicDomain.publicDigestDom (FirstComposition.toRetainedPublic pub)) :
    (NNH_Run5bCurrentShape.current m env err r).op9 D pub bytes () none =
      S1SemanticInstallation.verify AspisS1ExtractedRoundChildren.children (BslotT r) D pub bytes () := by
  have h := deployed_verify_guardedT (NP6_StdModel.calls r) r
    (InstalledPreparation.retainedDigest D) (FirstComposition.toRetainedPublic pub) bytes () none hdig
  rw [NPH_R22JoinSM5.bd_eq, bgT_eq] at h
  rw [NPH_R22JoinSM7.slotM m env err r D pub bytes]
  unfold S1SemanticInstallation.verify
  rw [← h]
#print axioms slotM_guardedT

/-- The op9 slot with the guarded semantic installation over BslotT on release `none`. -/
def op9gT (r : NP6_StdModel.Reservation) (O : Ops) : NPH_R22JoinSM6.Op9 := fun {H} D pub b h o =>
  match o with
  | none => S1SemanticInstallation.verify AspisS1ExtractedRoundChildren.children (BslotT r) D pub b h
  | some ob => O.op9 D pub b h (some ob)

theorem tx1_guardedMT (m : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE) (env : RSL.Env)
    (err : NFN_NEW_GeometryDictionary.CE) (r : NP6_StdModel.Reservation)
    (cp : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (hdig : LIB_VPublicDomain.publicDigestDom (FirstComposition.toRetainedPublic cp))
    (D : aspis_core.digest.Digest32 Unit) (pubBytes proof : Slice U8) (k : Usize) :
    verifier.candidate.tx1
        { NNH_Run5bCurrentShape.current m env err r with
          op9 := op9gT r (NNH_Run5bCurrentShape.current m env err r) }
        D cp pubBytes proof k () none =
      verifier.candidate.tx1 (NNH_Run5bCurrentShape.current m env err r) D cp pubBytes proof k () none := by
  apply NPH_R22JoinSM6.tx1_op9_congr
  intro b
  show S1SemanticInstallation.verify AspisS1ExtractedRoundChildren.children (BslotT r) D cp b () = _
  exact (slotM_guardedT m env err r D cp b hdig).symm
#print axioms tx1_guardedMT

abbrev OgT {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) :=
  { NPH_R22JoinSM7.Ocur c with op9 := op9gT c.fixed.reservation (NPH_R22JoinSM7.Ocur c) }

/-- The deployed adapter with op10 on observer `none` running the tx1 candidate over OgT c. -/
def GT {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) : NPH_R22JoinSM7.AOps :=
  { NOC_Stage1Forward.S c with
    op10 := fun {H} D p b s k h o =>
      match o with
      | none => AspisS6CurrentFirstInstallation.current (OgT c) D p b s k h none
      | some ob => (NOC_Stage1Forward.S c).op10 D p b s k h (some ob) }

theorem GT_op10_none {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) {H : Type}
    (D : _root_.AdapterRw.aspis_core.digest.Digest32 H) (p : NPH_R22JoinSM7.Pub) (b s : Slice U8)
    (k : Usize) (h : H) :
    (GT c).op10 D p b s k h none = AspisS6CurrentFirstInstallation.current (OgT c) D p b s k h none := rfl
#print axioms GT_op10_none

theorem GT_agree {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) (p : NPH_R22JoinSM7.Pub) (pub proof : Slice U8)
    (k : Usize) (hv : NPH_R22JoinSM7.Validated (NOC_Stage1Forward.S c) p) :
    (GT c).op10 (NPH_R22JoinSM7.Dig (NOC_Stage1Forward.S c)) p pub proof k () none =
      (NOC_Stage1Forward.S c).op10 (NPH_R22JoinSM7.Dig (NOC_Stage1Forward.S c)) p pub proof k () none := by
  obtain ⟨st, h21, hsp⟩ := hv
  obtain ⟨sp, hsp', hbind⟩ := NOC_Stage1Forward.publicBinding st
  have e : sp = p := Result.ok.inj (hsp'.symm.trans hsp)
  subst e
  have slot : (NOC_Stage1Forward.S c).op21 st = NNH_S1HostCodec.validate st := rfl
  rw [slot] at h21
  have hdig := NPH_R22JoinSM6.digest_of_binding st h21 _ hbind
  refine (GT_op10_none c (NPH_R22JoinSM7.Dig (NOC_Stage1Forward.S c)) sp pub proof k ()).trans ?_
  refine Eq.trans ?_ (NNH_Run5bCurrentInventory.adapter (NOC_Tx1Forward.M c) (NNH_HostCtx.envOf c)
    c.fixed.indexError c.fixed.reservation (NPH_R22JoinSM7.Dig (NOC_Stage1Forward.S c)) sp pub proof k ()).symm
  exact NPH_R22JoinSM7.current_congr _ _ _ _ _ _ _ _ (tx1_guardedMT _ _ _ _ _ hdig _ _ _ _)
#print axioms GT_agree

/-- Every execution of the deployed 345 entry equals the execution over GT c (no premise). -/
theorem stage1_guardedT {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) (program : _) (xs : _) (data : _) :
    _root_.AdapterRw.r1_pool_adapter.owned.stage1_owned (GT c) program xs data =
      _root_.AdapterRw.r1_pool_adapter.owned.stage1_owned (NOC_Stage1Forward.S c) program xs data :=
  NPH_R22JoinSM7.stage1_congr (NOC_Stage1Forward.S c) (GT c)
    (fun p pub proof k hv => GT_agree c p pub proof k hv) program xs data
#print axioms stage1_guardedT

theorem OgT_op9_none {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) {H : Type}
    (D : aspis_core.digest.Digest32 H) (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (b : Slice U8) (h : H) :
    (OgT c).op9 D pub b h none =
      S1SemanticInstallation.verify AspisS1ExtractedRoundChildren.children
        (BslotT c.fixed.reservation) D pub b h := rfl
#print axioms OgT_op9_none

end deployed

end AspisR1.NPH_R22JoinFIq
