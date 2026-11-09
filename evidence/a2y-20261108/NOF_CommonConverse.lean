import NOF_PowersAssociation
import NNY_NNUParent
import NNH_Run5bFinishEdge
import NNH_ResumeOkPort
import NNH_AuthCodeOk
import NHT_Tx2CommonModel
import NNU_Geometry
import NNU_Query
import NNU_MerkleSlots
import NNU_CommonResume
import NNH_Tx2LiteralSlots
import NNU_Offsets
set_option autoImplicit false
noncomputable section
namespace AspisR1.NOF_CommonConverse
open Aeneas Aeneas.Std Result VTop_Stages

elab "nof_head_reduce " h:ident : tactic => do
  let id ← Lean.Elab.Tactic.getFVarId h
  Lean.Elab.Tactic.liftMetaTactic fun goal => goal.withContext do
    let type ← id.getType
    let args := type.getAppArgs
    unless type.isAppOfArity ``Eq 3 do throwError "not equality"
    let lhs ← Lean.Meta.whnfHeadPred args[1]! (fun e => pure (!e.isAppOf ``ite && !e.isAppOf ``dite))
    if lhs == args[1]! then throwError "head unchanged"
    let next ← Lean.Meta.mkEq lhs args[2]!
    return [← goal.changeLocalDecl id next]

elab "nof_goal_reduce" : tactic =>
  Lean.Elab.Tactic.liftMetaTactic fun goal => goal.withContext do
    let type ← goal.getType
    unless type.isAppOfArity ``Eq 3 do throwError "not equality"
    let args := type.getAppArgs
    let lhs ← Lean.Meta.whnfHeadPred args[1]! (fun e => pure (!e.isAppOf ``ite && !e.isAppOf ``dite))
    if lhs == args[1]! then throwError "head unchanged"
    return [← goal.replaceTargetDefEq (← Lean.Meta.mkEq lhs args[2]!)]

/-- Close a branch whose source hypothesis can no longer be a success. -/
macro "nof_kill " h:ident : tactic => `(tactic| first
  | cases $h:ident
  | (nof_head_reduce $h; cases $h:ident)
  | (simp only [core.result.Result.Insts.CoreOpsTry.branch,Aeneas.Std.bind_tc_ok] at $h:ident; cases $h:ident)
  | (simp only [core.result.Result.Insts.CoreOpsTry.branch,Aeneas.Std.bind_tc_ok] at $h:ident; nof_head_reduce $h; cases $h:ident)
  | (simp [core.result.Result.Insts.CoreOpsTry.branch] at $h:ident))

/-- The SOURCE dictionary: the NJJ/LIBB source calls installed over the actual
stage (unread fields only). Used solely to restate the given source success. -/
def source (m : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (r : NP6_StdModel.Reservation) : Ops :=
 NHT_Tx2CommonModel.constants (NJJ_Common.install (NNH_Tx2SlotTransport.stage m env err r)
  (LIBB_Tx2Reservation.reservation env) (LIBB_Tx2Reservation.reservation env)
  (NLP_NativeMerkle.action (LIBB_PartitionEnv.H env))
  (NLB_Parent.finish (LIBB_Tx2Reservation.reservation env)))

/-- The given LIBB source common is the VTop common body over `source`. -/
theorem source_run (m : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (r : NP6_StdModel.Reservation)
 (pub proof ck : Slice U8) :
 verifier.candidate.tx2_common (source m env err r) (LIBB_PartitionEnv.digest env) pub proof ck () none =
 LIBB_Tx2EnvCode.common env pub proof ck :=
 (NHT_Tx2CommonModel.source (NJJ_Common.install (NNH_Tx2SlotTransport.stage m env err r)
   (LIBB_Tx2Reservation.reservation env) (LIBB_Tx2Reservation.reservation env)
   (NLP_NativeMerkle.action (LIBB_PartitionEnv.H env))
   (NLB_Parent.finish (LIBB_Tx2Reservation.reservation env)))
   (LIBB_PartitionEnv.digest env) pub proof ck () none).symm.trans
  (NJJ_Common.source (NNH_Tx2SlotTransport.stage m env err r) (LIBB_Tx2Reservation.reservation env)
   (LIBB_Tx2Reservation.reservation env) (NLP_NativeMerkle.action (LIBB_PartitionEnv.H env))
   (NLB_Parent.finish (LIBB_Tx2Reservation.reservation env)) (LIBB_PartitionEnv.digest env) pub proof ck ())

/-- Successful source tail implies the installed tail (flush, offsets, finish). -/
theorem tail_transport (m : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (r : NP6_StdModel.Reservation)
 (rep : NJC_FilledClause.reserved r = env.reservation) (pub proof ck : Slice U8)
 (domain : RSL.TX2_241.Dom064 NNH_Libraries.V0
   (LIB_Carriers.bytes pub,LIB_Carriers.bytes proof,LIB_Carriers.bytes ck))
 (success : LIBB_Tx2EnvCode.code env pub proof ck = .ok (.Ok ()))
 (p : verifier.Prepared) (inactive : aspis_core.field.wide_exact.WideExact)
 (state : verifier.Accumulator × verifier.BatchedWeights)
 (h : Tx2I_Cuts.tail (source m env err r) proof p none inactive 7527#usize 7751#usize 7783#usize state
   = ok (.Ok ())) :
 Tx2I_Cuts.tail (NNH_Tx2SlotTransport.stage m env err r) proof p none inactive
   7527#usize 7751#usize 7783#usize state = ok (.Ok ()) := by
 have c := NNH_Tx2LiteralSlots.constants m env err r
 have f20 : (source m env err r).op20 = ok 10055#usize := NNU_Offsets.openings
 have f21 : (source m env err r).op21 = ok 8007#usize := NNU_Offsets.final_offset
 unfold Tx2I_Cuts.tail at h ⊢
 rw [f20,f21] at h
 rw [c.2.2.2.1,c.2.2.2.2.1]
 simp only [NNH_Tx2LiteralSlots.flush,
  NNH_Run5bFinishEdge.selected m env err r rep pub proof ck domain success]
 exact h

/-- Y2: source-ordered successful installed common converse. From the original
reservation representation, Dom064 and source-code success at the SAME arguments,
the ACTUAL installed tx2_common with the SDK digest succeeds. Every call is
transported at its reached arguments; no whole-common equality is assumed. -/
theorem common (m : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (r : NP6_StdModel.Reservation)
 (rep : NJC_FilledClause.reserved r = env.reservation) (pub proof ck : Slice U8)
 (domain : RSL.TX2_241.Dom064 NNH_Libraries.V0
   (LIB_Carriers.bytes pub,LIB_Carriers.bytes proof,LIB_Carriers.bytes ck))
 (success : LIBB_Tx2EnvCode.code env pub proof ck = .ok (.Ok ())) :
 verifier.candidate.tx2_common (NNH_Tx2SlotTransport.stage m env err r)
  (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 (NNH_CorrectConfiguration.sdk m env err r))
  pub proof ck () none = .ok (.Ok ()) := by
 obtain ⟨_variant,_parsed,commonOk⟩ := NNH_AuthCodeOk.entered env pub proof ck success
 have size : ck.val.length=1768 := by
  simpa only [LIB_Carriers.bytes,NMS_R2N_RSLScalars.bytes,List.length_map,RSL.CHECKPOINT_BYTES]
   using domain.2.1
 have hY := (source_run m env err r pub proof ck).trans commonOk
 change verifier.candidate.tx2_common (NNH_Tx2SlotTransport.stage m env err r)
  (LIBB_PartitionEnv.digest env) pub proof ck () none = _
 rw [← Tx2I_Cuts.common_source] at hY ⊢
 unfold Tx2I_Cuts.common at hY ⊢
 have c := NNH_Tx2LiteralSlots.constants m env err r
 have s14 : (source m env err r).op14 = ok 7783#usize := NNU_Offsets.round1
 have s15 : (source m env err r).op15 = ok 7751#usize := NNU_Offsets.folded
 have s16 : (source m env err r).op16 = ok 10#usize := by
  show (ok NHT_Constants.compact.SPLIT : Result Usize) = _
  rw [NNU_Offsets.split_value]
 have s22 : (source m env err r).op22 = ok 7527#usize := NNU_Offsets.round0
 have s23 : (source m env err r).op23 = ok 7495#usize := NNU_Offsets.inactive
 have m13s : ∀ ph, (source m env err r).op13 none ph = ok () := fun _ => rfl
 have m13t : ∀ ph, (NNH_Tx2SlotTransport.stage m env err r).op13 none ph = ok () := fun _ => rfl
 simp only [s14,s15,s16,s22,s23,m13s,c.1,c.2.1,c.2.2.1,c.2.2.2.2.2.1,c.2.2.2.2.2.2,m13t,
  bind_tc_ok] at hY ⊢
 -- resume
 obtain ⟨x0,hx0,hY⟩ := Port3_PushFrame.bind_success _ _ _ hY
 rcases x0 with ⟨⟨p,a⟩⟩ | e0
 swap
 · nof_kill hY
 have resume : NJJ_Common.resume (LIBB_Tx2Reservation.reservation env) (LIBB_PartitionEnv.digest env)
   ck proof pub .S2 () = .ok (.Ok (p,a)) := hx0
 obtain ⟨fields,next⟩ := NNU_CommonResume.occurrence env pub proof ck size commonOk p a resume
 have h18 : (NNH_Tx2SlotTransport.stage m env err r).op18 (LIBB_PartitionEnv.digest env)
   ck proof pub .S2 () = .ok (.Ok (p,a)) := by
  have native := NNH_ResumeOkPort.value _ _ ck proof pub () p a resume
  rw [LIBB_Tx2Reservation.reserved] at native
  exact native
 rw [h18]
 simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at hY ⊢
 try nof_head_reduce hY
 try nof_goal_reduce
 simp only [next,bne_self_eq_false,Bool.false_eq_true,↓reduceIte] at hY ⊢
 -- powers
 obtain ⟨g,hg,hY⟩ := Port3_PushFrame.bind_success _ _ _ hY
 have powers : NHT_PacketOps.powers 29#usize p.gamma = ok g := hg
 have h17 : (NNH_Tx2SlotTransport.stage m env err r).op17 29#usize p.gamma = ok g :=
  (NNH_Tx2LiteralSlots.powers m env err r 29#usize p.gamma).trans
   (NOF_PowersAssociation.source p a fields g powers)
 rw [h17,bind_tc_ok]
 -- inactive slice, decode, ok_or
 obtain ⟨s,hs,hY⟩ := Port3_PushFrame.bind_success _ _ _ hY
 rw [hs,bind_tc_ok]
 obtain ⟨o,ho,hY⟩ := Port3_PushFrame.bind_success _ _ _ hY
 have h2 := ho
 change (NNH_Tx2SlotTransport.stage m env err r).op2 s = _ at h2
 rw [h2,bind_tc_ok]
 obtain ⟨r1,hr1,hY⟩ := Port3_PushFrame.bind_success _ _ _ hY
 have h0 := hr1
 change (NNH_Tx2SlotTransport.stage m env err r).op0 o _ = _ at h0
 rw [h0,bind_tc_ok]
 rcases r1 with val1 | e1
 swap
 · nof_kill hY
 simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at hY ⊢
 -- folded root
 obtain ⟨s1,hs1,hY⟩ := Port3_PushFrame.bind_success _ _ _ hY
 rw [hs1,bind_tc_ok]
 obtain ⟨r2,hr2,hY⟩ := Port3_PushFrame.bind_success _ _ _ hY
 rw [hr2,bind_tc_ok]
 obtain ⟨fr,hfr,hY⟩ := Port3_PushFrame.bind_success _ _ _ hY
 rcases r2 with arr | e2
 swap
 · first | cases hfr | (nof_head_reduce hfr; cases hfr)
 have hfa : (ok arr : Result (Array U8 32#usize)) = ok fr := hfr
 have h32 : (NNH_Tx2SlotTransport.stage m env err r).unwrap32 (.Ok arr) = ok fr := hfa
 rw [h32,bind_tc_ok]
 -- Merkle
 obtain ⟨x3,hx3,hY⟩ := Port3_PushFrame.bind_success _ _ _ hY
 rcases x3 with u3 | e3
 swap
 · nof_kill hY
 cases u3
 have accepted : NLP_NativeMerkle.action (LIBB_PartitionEnv.H env) (LIBB_PartitionEnv.digest env)
   proof p fr 1#usize () = .ok (.Ok ()) := hx3
 have h5 : (NNH_Tx2SlotTransport.stage m env err r).op5 (LIBB_PartitionEnv.digest env) proof p fr
   1#usize () = .ok (.Ok ()) := by
  rw [NNU_MerkleSlots.installed]
  exact NNY_NNUParent.parent m env err r pub proof ck p a fr resume accepted
 rw [h5]
 simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at hY ⊢
 -- geometry
 rw [NNU_Geometry.source]
 obtain ⟨x4,hx4,hY⟩ := Port3_PushFrame.bind_success _ _ _ hY
 rcases x4 with geo | e4
 swap
 · nof_kill hY
 have h11 : NJC_ClosedCalls.geometry p.queries 10#usize 22#usize = .ok (.Ok geo) := hx4
 rw [h11]
 simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at hY ⊢
 -- pending
 obtain ⟨x5,hx5,hY⟩ := Port3_PushFrame.bind_success _ _ _ hY
 rcases x5 with pend | e5
 swap
 · nof_kill hY
 have init : NJJ_Common.pending (LIBB_Tx2Reservation.reservation env) a.weights.deref
   = .ok (.Ok pend) := hx5
 have h10 : (NNH_Tx2SlotTransport.stage m env err r).op10 a.weights.deref = .ok (.Ok pend) := by
  rw [NNH_Tx2LiteralSlots.pending,← LIBB_Tx2Reservation.reserved env]
  exact init
 rw [h10]
 simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at hY ⊢
 -- query
 rw [NNU_Query.source m env err r proof p a g geo pend fields next powers init]
 obtain ⟨x6,hx6,hY⟩ := Port3_PushFrame.bind_success _ _ _ hY
 rcases x6 with val4 | e6
 swap
 · nof_kill hY
 have h6 : NJJ_Common.query proof p a g none geo pend 22#usize = .ok (.Ok val4) := hx6
 rw [h6]
 simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at hY ⊢
 exact tail_transport m env err r rep pub proof ck domain success p val1 val4 hY

#print axioms source_run
#print axioms tail_transport
#print axioms common
end AspisR1.NOF_CommonConverse
end
