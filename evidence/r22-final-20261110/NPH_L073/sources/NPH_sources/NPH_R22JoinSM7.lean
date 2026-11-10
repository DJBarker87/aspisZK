import NPH_R22JoinSM6
import NOC_Stage1Forward

/-! NPH_ (R22, SM step 6): the stage1_owned ordering link, and SM composed to the 345 entry.
- `stage1_congr` (generic over every adapter Ops record): r1_pool_adapter.owned.stage1_owned with
  op10 replaced by the op10 of any record f equals the original whenever f agrees with op10 at
  every public p that is `Validated`: the semantic_public of a statement whose op21 returned Ok.
  Proved by bind-stepping both data branches ([3,10] and [3,11]) of the extracted body: in
  each, the only first_decoded call is at `p ← semantic_public val2` after `ops.op21 val2`
  returned Ok (the premise is bundled into the def predicate `Validated`, after L055-L060).
- `fd10`: first_decoded reads op10 only at its own arguments, hash () and observer none.
- `slotM`/`slotM_guarded`/`tx1_guardedM`: the NPH_R22JoinSM5/SM6 slot and tx1 statements for the
  record that the deployed adapter S c actually runs (NNH_Run5bCurrentShape.current, the
  record of NOC_Stage1Forward.fdLemma), for every reservation.
- `G c`: S c with op10 on observer `none` running the tx1 candidate whose op9 slot on release
  `none` is the guarded semantic installation over NPH_R22JoinSM5.Bslot (mask/add/mul run only
  on canonical arguments). `G_agree`: at every Validated public the guarded op10 equals S c's
  (NOC_Stage1Forward.publicBinding, NPH_R22JoinSM6.digest_of_binding).
- `stage1_guarded`: stage1_owned (G c) = stage1_owned (S c) for every host context and input,
  no premise. Standard axioms. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.NPH_R22JoinSM7
open Aeneas Aeneas.Std Result

section adapter

abbrev AOps := _root_.AdapterRw.Ops
abbrev Pub := _root_.AdapterRw.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public
abbrev Dig (ops : AOps) := _root_.AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 ops

/-- p is the semantic public of a statement whose op21 validate returned Ok. -/
def Validated (ops : AOps) (p : Pub) : Prop :=
  ∃ st, ops.op21 st = ok (.Ok ()) ∧
    _root_.AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public st = ok p

theorem ok_of_map_err {T E F O : Type} {I : core.ops.function.FnOnce O E F}
    {r : core.result.Result T E} {o : O} {r' : core.result.Result T F} {v : T}
    (h : _root_.AdapterRw.core.result.Result.map_err I r o = ok r')
    (hb : core.result.Result.Insts.CoreOpsTry.branch r' =
      ok (core.ops.control_flow.ControlFlow.Continue v)) : r = .Ok v := by
  have e := (NPH_R22JoinSM3.branch_cont r' v).1 hb
  subst e
  cases r with
  | Ok x =>
    simp only [_root_.AdapterRw.core.result.Result.map_err] at h
    first | (cases h; rfl) | simp_all
  | Err e =>
    simp only [_root_.AdapterRw.core.result.Result.map_err] at h
    obtain ⟨t, -, ht⟩ := NPH_R22JoinSM3.bind_ok_inv h
    cases ht
#print axioms ok_of_map_err

theorem fd10 (ops f : AOps) (p : Pub) (pub proof : Slice U8) (k : Usize)
    (h : f.op10 (Dig ops) p pub proof k () none = ops.op10 (Dig ops) p pub proof k () none) :
    _root_.AdapterRw.first_decoded { ops with op10 := f.op10 } p pub proof k =
      _root_.AdapterRw.first_decoded ops p pub proof k := by
  unfold _root_.AdapterRw.first_decoded
  have ho : ∀ q : AOps, _root_.AdapterRw.observer q = ok none := fun _ => rfl
  simp only [ho, bind_tc_ok]
  show (f.op10 (Dig ops) p pub proof k () none >>= _) = _
  rw [h]
  try rfl
#print axioms fd10

theorem stage1_congr (ops f : AOps)
    (hagree : ∀ (p : Pub) (pub proof : Slice U8) (k : Usize), Validated ops p →
      f.op10 (Dig ops) p pub proof k () none = ops.op10 (Dig ops) p pub proof k () none)
    (program : _) (xs : _) (data : _) :
    _root_.AdapterRw.r1_pool_adapter.owned.stage1_owned { ops with op10 := f.op10 } program xs data =
      _root_.AdapterRw.r1_pool_adapter.owned.stage1_owned ops program xs data := by
  unfold _root_.AdapterRw.r1_pool_adapter.owned.stage1_owned
  refine NPH_R22JoinSM3.bind_congr_ok _ _ _ (fun _ _ => ?_)
  refine ite_congr rfl (fun _ => ?_) (fun _ => ?_)
  · refine ite_congr rfl (fun _ => ?_) (fun _ => ?_)
    rfl
    refine NPH_R22JoinSM3.bind_congr_ok _ _ _ (fun _ _ => ?_)
    refine NPH_R22JoinSM3.bind_congr_ok _ _ _ (fun _ _ => ?_)
    refine NPH_R22JoinSM3.bind_congr_ok _ _ _ (fun _ _ => ?_)
    refine NPH_R22JoinSM3.bind_congr_ok _ _ _ (fun _ _ => ?_)
    refine NPH_R22JoinSM3.bind_congr_ok _ _ _ (fun cf1 _ => ?_)
    cases cf1 with
    | Break res => dsimp only
    | Continue v1 =>
    refine NPH_R22JoinSM3.bind_congr_ok _ _ _ (fun _ _ => ?_)
    refine NPH_R22JoinSM3.bind_congr_ok _ _ _ (fun cf2 _ => ?_)
    cases cf2 with
    | Break res => dsimp only
    | Continue v2 =>
    refine NPH_R22JoinSM3.bind_congr_ok _ _ _ (fun _ _ => ?_)
    refine NPH_R22JoinSM3.bind_congr_ok _ _ _ (fun cf3 _ => ?_)
    cases cf3 with
    | Break res => dsimp only
    | Continue v3 =>
    refine NPH_R22JoinSM3.bind_congr_ok _ _ _ (fun _ _ => ?_)
    refine NPH_R22JoinSM3.bind_congr_ok _ _ _ (fun cf4 _ => ?_)
    cases cf4 with
    | Break res => dsimp only
    | Continue v4 =>
    refine NPH_R22JoinSM3.bind_congr_ok _ _ _ (fun _ _ => ?_)
    refine NPH_R22JoinSM3.bind_congr_ok _ _ _ (fun cf5 _ => ?_)
    cases cf5 with
    | Break res => dsimp only
    | Continue v5 =>
    refine NPH_R22JoinSM3.bind_congr_ok _ _ _ (fun _ _ => ?_)
    refine NPH_R22JoinSM3.bind_congr_ok _ _ _ (fun cf6 _ => ?_)
    cases cf6 with
    | Break res => dsimp only
    | Continue v6 =>
    refine NPH_R22JoinSM3.bind_congr_ok _ _ _ (fun _ _ => ?_)
    refine NPH_R22JoinSM3.bind_congr_ok _ _ _ (fun cf7 _ => ?_)
    cases cf7 with
    | Break res => dsimp only
    | Continue v7 =>
    refine NPH_R22JoinSM3.bind_congr_ok _ _ _ (fun _ _ => ?_)
    refine NPH_R22JoinSM3.bind_congr_ok _ _ _ (fun cf8 _ => ?_)
    cases cf8 with
    | Break res => dsimp only
    | Continue v8 =>
    refine NPH_R22JoinSM3.bind_congr_ok _ _ _ (fun r8 hr8 => ?_)
    refine NPH_R22JoinSM3.bind_congr_ok _ _ _ (fun r9 hr9 => ?_)
    refine NPH_R22JoinSM3.bind_congr_ok _ _ _ (fun cf8 hcf8 => ?_)
    cases cf8 with
    | Break res => dsimp only
    | Continue u8 =>
    have h8 := ok_of_map_err hr9 hcf8
    rw [h8] at hr8
    refine NPH_R22JoinSM3.bind_congr_ok _ _ _ (fun _ _ => ?_)
    refine NPH_R22JoinSM3.bind_congr_ok _ _ _ (fun _ _ => ?_)
    refine NPH_R22JoinSM3.bind_congr_ok _ _ _ (fun _ _ => ?_)
    refine NPH_R22JoinSM3.bind_congr_ok _ _ _ (fun cf9 _ => ?_)
    cases cf9 with
    | Break res => dsimp only
    | Continue v9 =>
    refine NPH_R22JoinSM3.bind_congr_ok _ _ _ (fun _ _ => ?_)
    refine NPH_R22JoinSM3.bind_congr_ok _ _ _ (fun cf10 _ => ?_)
    cases cf10 with
    | Break res => dsimp only
    | Continue v10 =>
    refine NPH_R22JoinSM3.bind_congr_ok _ _ _ (fun _ _ => ?_)
    refine NPH_R22JoinSM3.bind_congr_ok _ _ _ (fun _ _ => ?_)
    refine NPH_R22JoinSM3.bind_congr_ok _ _ _ (fun _ _ => ?_)
    refine NPH_R22JoinSM3.bind_congr_ok _ _ _ (fun _ _ => ?_)
    refine NPH_R22JoinSM3.bind_congr_ok _ _ _ (fun cf11 _ => ?_)
    cases cf11 with
    | Break res => dsimp only
    | Continue v11 =>
    refine ite_congr rfl (fun _ => ?_) (fun _ => ?_)
    rfl
    refine NPH_R22JoinSM3.bind_congr_ok _ _ _ (fun _ _ => ?_)
    refine NPH_R22JoinSM3.bind_congr_ok _ _ _ (fun _ _ => ?_)
    refine ite_congr rfl (fun _ => ?_) (fun _ => ?_)
    rfl
    refine NPH_R22JoinSM3.bind_congr_ok _ _ _ (fun _ _ => ?_)
    refine NPH_R22JoinSM3.bind_congr_ok _ _ _ (fun _ _ => ?_)
    refine NPH_R22JoinSM3.bind_congr_ok _ _ _ (fun _ _ => ?_)
    refine ite_congr rfl (fun _ => ?_) (fun _ => ?_)
    rfl
    refine NPH_R22JoinSM3.bind_congr_ok _ _ _ (fun p hp => ?_)
    refine NPH_R22JoinSM3.bind_congr_ok _ _ _ (fun _ _ => ?_)
    refine NPH_R22JoinSM3.bind_congr_ok _ _ _ (fun _ _ => ?_)
    refine NPH_R22JoinSM3.bind_congr_ok _ _ _ (fun _ _ => ?_)
    rw [fd10 _ _ p _ _ _ (hagree p _ _ _ ⟨_, hr8, hp⟩)]
  · refine NPH_R22JoinSM3.bind_congr_ok _ _ _ (fun _ _ => ?_)
    refine ite_congr rfl (fun _ => ?_) (fun _ => ?_)
    · refine ite_congr rfl (fun _ => ?_) (fun _ => ?_)
      rfl
      refine NPH_R22JoinSM3.bind_congr_ok _ _ _ (fun _ _ => ?_)
      refine NPH_R22JoinSM3.bind_congr_ok _ _ _ (fun _ _ => ?_)
      refine NPH_R22JoinSM3.bind_congr_ok _ _ _ (fun _ _ => ?_)
      refine NPH_R22JoinSM3.bind_congr_ok _ _ _ (fun _ _ => ?_)
      refine NPH_R22JoinSM3.bind_congr_ok _ _ _ (fun cf1 _ => ?_)
      cases cf1 with
      | Break res => dsimp only
      | Continue v1 =>
      refine NPH_R22JoinSM3.bind_congr_ok _ _ _ (fun _ _ => ?_)
      refine NPH_R22JoinSM3.bind_congr_ok _ _ _ (fun cf2 _ => ?_)
      cases cf2 with
      | Break res => dsimp only
      | Continue v2 =>
      refine NPH_R22JoinSM3.bind_congr_ok _ _ _ (fun _ _ => ?_)
      refine NPH_R22JoinSM3.bind_congr_ok _ _ _ (fun cf3 _ => ?_)
      cases cf3 with
      | Break res => dsimp only
      | Continue v3 =>
      refine NPH_R22JoinSM3.bind_congr_ok _ _ _ (fun _ _ => ?_)
      refine NPH_R22JoinSM3.bind_congr_ok _ _ _ (fun cf4 _ => ?_)
      cases cf4 with
      | Break res => dsimp only
      | Continue v4 =>
      refine NPH_R22JoinSM3.bind_congr_ok _ _ _ (fun _ _ => ?_)
      refine NPH_R22JoinSM3.bind_congr_ok _ _ _ (fun cf5 _ => ?_)
      cases cf5 with
      | Break res => dsimp only
      | Continue v5 =>
      refine NPH_R22JoinSM3.bind_congr_ok _ _ _ (fun _ _ => ?_)
      refine NPH_R22JoinSM3.bind_congr_ok _ _ _ (fun cf6 _ => ?_)
      cases cf6 with
      | Break res => dsimp only
      | Continue v6 =>
      refine NPH_R22JoinSM3.bind_congr_ok _ _ _ (fun _ _ => ?_)
      refine NPH_R22JoinSM3.bind_congr_ok _ _ _ (fun cf7 _ => ?_)
      cases cf7 with
      | Break res => dsimp only
      | Continue v7 =>
      refine NPH_R22JoinSM3.bind_congr_ok _ _ _ (fun _ _ => ?_)
      refine NPH_R22JoinSM3.bind_congr_ok _ _ _ (fun cf8 _ => ?_)
      cases cf8 with
      | Break res => dsimp only
      | Continue v8 =>
      refine NPH_R22JoinSM3.bind_congr_ok _ _ _ (fun r8 hr8 => ?_)
      refine NPH_R22JoinSM3.bind_congr_ok _ _ _ (fun r9 hr9 => ?_)
      refine NPH_R22JoinSM3.bind_congr_ok _ _ _ (fun cf8 hcf8 => ?_)
      cases cf8 with
      | Break res => dsimp only
      | Continue u8 =>
      have h8 := ok_of_map_err hr9 hcf8
      rw [h8] at hr8
      refine NPH_R22JoinSM3.bind_congr_ok _ _ _ (fun _ _ => ?_)
      refine NPH_R22JoinSM3.bind_congr_ok _ _ _ (fun _ _ => ?_)
      refine NPH_R22JoinSM3.bind_congr_ok _ _ _ (fun _ _ => ?_)
      refine NPH_R22JoinSM3.bind_congr_ok _ _ _ (fun cf9 _ => ?_)
      cases cf9 with
      | Break res => dsimp only
      | Continue v9 =>
      refine NPH_R22JoinSM3.bind_congr_ok _ _ _ (fun _ _ => ?_)
      refine NPH_R22JoinSM3.bind_congr_ok _ _ _ (fun cf10 _ => ?_)
      cases cf10 with
      | Break res => dsimp only
      | Continue v10 =>
      refine NPH_R22JoinSM3.bind_congr_ok _ _ _ (fun _ _ => ?_)
      refine NPH_R22JoinSM3.bind_congr_ok _ _ _ (fun _ _ => ?_)
      refine NPH_R22JoinSM3.bind_congr_ok _ _ _ (fun _ _ => ?_)
      refine NPH_R22JoinSM3.bind_congr_ok _ _ _ (fun _ _ => ?_)
      refine NPH_R22JoinSM3.bind_congr_ok _ _ _ (fun cf11 _ => ?_)
      cases cf11 with
      | Break res => dsimp only
      | Continue v11 =>
      refine ite_congr rfl (fun _ => ?_) (fun _ => ?_)
      rfl
      refine NPH_R22JoinSM3.bind_congr_ok _ _ _ (fun _ _ => ?_)
      refine NPH_R22JoinSM3.bind_congr_ok _ _ _ (fun _ _ => ?_)
      refine ite_congr rfl (fun _ => ?_) (fun _ => ?_)
      rfl
      refine NPH_R22JoinSM3.bind_congr_ok _ _ _ (fun _ _ => ?_)
      refine NPH_R22JoinSM3.bind_congr_ok _ _ _ (fun _ _ => ?_)
      refine NPH_R22JoinSM3.bind_congr_ok _ _ _ (fun _ _ => ?_)
      refine ite_congr rfl (fun _ => ?_) (fun _ => ?_)
      rfl
      refine NPH_R22JoinSM3.bind_congr_ok _ _ _ (fun p hp => ?_)
      refine NPH_R22JoinSM3.bind_congr_ok _ _ _ (fun _ _ => ?_)
      refine NPH_R22JoinSM3.bind_congr_ok _ _ _ (fun _ _ => ?_)
      refine NPH_R22JoinSM3.bind_congr_ok _ _ _ (fun _ _ => ?_)
      rw [fd10 _ _ p _ _ _ (hagree p _ _ _ ⟨_, hr8, hp⟩)]
    · rfl
#print axioms stage1_congr

end adapter

section deployed
open AspisR1CurrentCaller

theorem slotM (m : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE) (env : RSL.Env)
    (err : NFN_NEW_GeometryDictionary.CE) (r : NP6_StdModel.Reservation)
    (D : aspis_core.digest.Digest32 Unit)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public) (bytes : Slice U8) :
    (NNH_Run5bCurrentShape.current m env err r).op9 D pub bytes () none =
      S1SemanticInstallation.verify AspisS1ExtractedRoundChildren.children
        (ClaimsUnrolledFinish.install (NP6_StdModel.calls r) (IDa_Deployed.boundaries r)) D pub bytes () := rfl
#print axioms slotM

theorem slotM_guarded (m : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE) (env : RSL.Env)
    (err : NFN_NEW_GeometryDictionary.CE) (r : NP6_StdModel.Reservation)
    (D : aspis_core.digest.Digest32 Unit)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public) (bytes : Slice U8)
    (hdig : LIB_VPublicDomain.publicDigestDom (FirstComposition.toRetainedPublic pub)) :
    (NNH_Run5bCurrentShape.current m env err r).op9 D pub bytes () none =
      S1SemanticInstallation.verify AspisS1ExtractedRoundChildren.children
        (NPH_R22JoinSM5.Bslot r) D pub bytes () := by
  have h := NPH_R22JoinSM4.deployed_verify_guarded (NP6_StdModel.calls r) r
    (InstalledPreparation.retainedDigest D) (FirstComposition.toRetainedPublic pub) bytes () none hdig
  rw [NPH_R22JoinSM5.bd_eq, NPH_R22JoinSM5.bg_eq] at h
  rw [slotM m env err r D pub bytes]
  unfold S1SemanticInstallation.verify
  rw [← h]
#print axioms slotM_guarded

theorem tx1_guardedM (m : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE) (env : RSL.Env)
    (err : NFN_NEW_GeometryDictionary.CE) (r : NP6_StdModel.Reservation)
    (cp : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (hdig : LIB_VPublicDomain.publicDigestDom (FirstComposition.toRetainedPublic cp))
    (D : aspis_core.digest.Digest32 Unit) (pubBytes proof : Slice U8) (k : Usize) :
    verifier.candidate.tx1
        { NNH_Run5bCurrentShape.current m env err r with
          op9 := NPH_R22JoinSM6.op9g r (NNH_Run5bCurrentShape.current m env err r) }
        D cp pubBytes proof k () none =
      verifier.candidate.tx1 (NNH_Run5bCurrentShape.current m env err r) D cp pubBytes proof k () none := by
  apply NPH_R22JoinSM6.tx1_op9_congr
  intro b
  show S1SemanticInstallation.verify AspisS1ExtractedRoundChildren.children
      (NPH_R22JoinSM5.Bslot r) D cp b () = _
  exact (slotM_guarded m env err r D cp b hdig).symm
#print axioms tx1_guardedM

/-- The tx1 candidate record that the deployed adapter S c runs (NOC_Stage1Forward.fdLemma). -/
abbrev Ocur {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) :=
  NNH_Run5bCurrentShape.current (NOC_Tx1Forward.M c) (NNH_HostCtx.envOf c) c.fixed.indexError
    c.fixed.reservation

/-- The same record with the guarded op9 slot on release `none`. -/
abbrev Og {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) :=
  { Ocur c with op9 := NPH_R22JoinSM6.op9g c.fixed.reservation (Ocur c) }

/-- The deployed adapter with op10 on observer `none` running the guarded tx1 candidate. -/
def G {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) : AOps :=
  { NOC_Stage1Forward.S c with
    op10 := fun {H} D p b s k h o =>
      match o with
      | none => AspisS6CurrentFirstInstallation.current (Og c) D p b s k h none
      | some ob => (NOC_Stage1Forward.S c).op10 D p b s k h (some ob) }

theorem G_agree {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) (p : Pub) (pub proof : Slice U8) (k : Usize)
    (hv : Validated (NOC_Stage1Forward.S c) p) :
    (G c).op10 (Dig (NOC_Stage1Forward.S c)) p pub proof k () none =
      (NOC_Stage1Forward.S c).op10 (Dig (NOC_Stage1Forward.S c)) p pub proof k () none := by
  obtain ⟨st, h21, hsp⟩ := hv
  obtain ⟨sp, hsp', hbind⟩ := NOC_Stage1Forward.publicBinding st
  have e : sp = p := Result.ok.inj (hsp'.symm.trans hsp)
  subst e
  have good : NNH_S1HostCodec.validate st = ok (.Ok ()) := h21
  have hdig := NPH_R22JoinSM6.digest_of_binding st good _ hbind
  rw [NNH_Run5bCurrentInventory.adapter]
  show AspisS6CurrentFirstInstallation.current (Og c) (Dig (NOC_Stage1Forward.S c)) sp pub proof k () none = _
  unfold AspisS6CurrentFirstInstallation.current
  rw [AspisS6CurrentFirstInstallation.observer_none]
  congr 1
  exact tx1_guardedM _ _ _ _ _ hdig _ _ _ _
#print axioms G_agree

/-- Every execution of the deployed 345 entry equals the execution over G c. -/
theorem stage1_guarded {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) (program : _) (xs : _) (data : _) :
    _root_.AdapterRw.r1_pool_adapter.owned.stage1_owned (G c) program xs data =
      _root_.AdapterRw.r1_pool_adapter.owned.stage1_owned (NOC_Stage1Forward.S c) program xs data :=
  stage1_congr (NOC_Stage1Forward.S c) (G c) (fun p pub proof k hv => G_agree c p pub proof k hv)
    program xs data
#print axioms stage1_guarded

/-- What G changes: op10 on observer `none` runs the tx1 candidate over Og c, whose op9 slot
on release `none` is the guarded semantic installation over Bslot; every other slot is S c's. -/
theorem G_op10_none {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) {H : Type}
    (D : _root_.AdapterRw.aspis_core.digest.Digest32 H) (p : Pub) (b s : Slice U8) (k : Usize) (h : H) :
    (G c).op10 D p b s k h none = AspisS6CurrentFirstInstallation.current (Og c) D p b s k h none := rfl
#print axioms G_op10_none

theorem Og_op9_none {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) {H : Type}
    (D : aspis_core.digest.Digest32 H) (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (b : Slice U8) (h : H) :
    (Og c).op9 D pub b h none =
      S1SemanticInstallation.verify AspisS1ExtractedRoundChildren.children
        (NPH_R22JoinSM5.Bslot c.fixed.reservation) D pub b h := rfl
#print axioms Og_op9_none

end deployed

end AspisR1.NPH_R22JoinSM7
