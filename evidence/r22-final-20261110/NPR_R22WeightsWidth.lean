import NPH_R22JoinCW2
import NPH_R22FieldSites
import NNU_Query
import NNU_Offsets
import LIBB_Tx2EnvCode

/-! NPR_ (R22, weights.field producer 1): the weights length at the deployed tx2 finish. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.NPR_R22WeightsWidth
open Aeneas Aeneas.Std Result AspisR1Stage2

theorem bind_congr_ok {α β : Type} (m : Result α) (k k' : α → Result β)
    (h : ∀ x, m = ok x → k x = k' x) : (m >>= k) = (m >>= k') := by
  cases m with
  | ok x => simp only [bind_tc_ok]; exact h x rfl
  | fail e => simp only [bind_tc_fail]
  | div => simp only [bind_tc_div]

theorem branch_ok {T E : Type} {m : Result (core.result.Result T E)} {r : core.result.Result T E} {v : T}
    (hr : m = ok r)
    (hcf : core.result.Result.Insts.CoreOpsTry.branch r = ok (core.ops.control_flow.ControlFlow.Continue v)) :
    m = ok (core.result.Result.Ok v) := by
  cases r with
  | Ok w =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch] at hcf
    cases hcf
    exact hr
  | Err e =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch] at hcf
    cases hcf

/-! ### The tx2 query loop returns a reached state -/

theorem run_reach (proof : Slice U8) (p : verifier.Prepared) (g : Array SAQ_WideABI.E 29#usize)
    (geo : verifier.QueryGeometry) (a0 : verifier.Accumulator) (b0 : verifier.BatchedWeights) :
    ∀ (fuel : Nat) (a : verifier.Accumulator) (b : verifier.BatchedWeights)
      (a1 : verifier.Accumulator) (b1 : verifier.BatchedWeights),
      NPH_R22JoinCW2.Reach proof p g geo a0 b0 a b →
      NFG_QueryLoopDefs.run (fun a b => Port3_NativeQueryBody.verifier.candidate.query_values
          NPH_R22Join094.Dcon proof p a g none geo b) 22#usize fuel (.Ok (a, b)) = ok (.Ok (a1, b1)) →
      NPH_R22JoinCW2.Reach proof p g geo a0 b0 a1 b1 := by
  intro fuel
  induction fuel with
  | zero =>
    intro a b a1 b1 r h
    by_cases s : a.next ≥ 22#usize
    · simp only [NFG_QueryLoopDefs.run, s, if_true] at h
      have e := Result.ok.inj h
      cases e
      exact r
    · simp only [NFG_QueryLoopDefs.run, s, if_false] at h
      cases h
  | succ fuel ih =>
    intro a b a1 b1 r h
    by_cases s : a.next ≥ 22#usize
    · simp only [NFG_QueryLoopDefs.run, s, if_true] at h
      have e := Result.ok.inj h
      cases e
      exact r
    · simp only [NFG_QueryLoopDefs.run, s, if_false] at h
      obtain ⟨next, hq, hr⟩ := Port3_PushFrame.bind_success _ _ _ h
      cases next with
      | Err e => cases fuel <;> simp only [NFG_QueryLoopDefs.run] at hr <;> cases hr
      | Ok pr =>
        obtain ⟨a', b'⟩ := pr
        have inside : a.next.val < 22 := by
          exact Nat.lt_of_not_ge s
        exact ih a' b' a1 b1 (NPH_R22JoinCW2.Reach.step r inside hq) hr

/-- NJJ_Common.query (op6 of the deployed tx2, NNU_Query.source) from a Domain start returns a
reached state, which carries the Domain (width 64). -/
theorem query_domain (proof : Slice U8) (p : verifier.Prepared) (g : Array SAQ_WideABI.E 29#usize)
    (geo : verifier.QueryGeometry) (a : verifier.Accumulator) (b : verifier.BatchedWeights)
    (a1 : verifier.Accumulator) (b1 : verifier.BatchedWeights)
    (d0 : NFS_QueryInvariant.Domain p 10 22 a b)
    (canonical : NEV_DotInputs.Canonical (FIp_DotsAdapter.toArray g))
    (obs : Option (VTop_Stages.verifier.Phase → Result Unit))
    (run : NJJ_Common.query proof p a g obs geo b 22#usize = ok (.Ok (a1, b1))) :
    NPH_R22JoinCW2.Reach proof p g geo a b a1 b1 ∧ NFS_QueryInvariant.Domain p 10 22 a1 b1 := by
  unfold NJJ_Common.query NHT_PacketOps.query NHT_ResultPort.action at run
  rw [NFS_QueryLoopRoot.finite NJJ_QueryOps.concrete proof p g geo 0 0 10 22#usize (by decide)
    canonical 12 (.Ok (a, b)) d0] at run
  obtain ⟨st, hst, hreply⟩ := Port3_PushFrame.bind_success _ _ _ run
  cases st with
  | Err e => simp only [NHT_ResultPort.reply] at hreply; cases hreply
  | Ok v =>
    obtain ⟨a2, b2⟩ := v
    simp only [NHT_ResultPort.reply] at hreply
    cases hreply
    have reach := run_reach proof p g geo a b 12 a b a1 b1 NPH_R22JoinCW2.Reach.init hst
    exact ⟨reach, NPH_R22JoinCW2.reach_domain d0 reach⟩

/-! ### The accumulator handed to the tx2 finish -/

theorem next_of_guard {x : Usize} (hc : ¬ ((x != NHT_Constants.compact.SPLIT) = true)) :
    x = 10#usize := by
  rw [NNU_Offsets.split_value] at hc
  simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hc
  exact hc

/-- Every success of the tx2 prefix before the finish call gives a flushed weights slice of
length 64: the resume Domain (NPH_R22JoinCW2.entered_domain), the pending initial Domain
(NNH_Run5bQueryDomain.initial), the query loop (query_domain: width 64 and raw length 64),
and Port3_FlushInstall.accepted_contents (length preservation). -/
theorem width_at_finish (wr rr : NP6_StdModel.Reservation) {H : Type}
    (D : VTop_Stages.aspis_core.digest.Digest32 H) (ck proof pub : Slice U8) (hash : H)
    (p : verifier.Prepared) (a : verifier.Accumulator)
    (hres : NJJ_Common.resume wr D ck proof pub .S2 hash = ok (.Ok (p, a)))
    (hn : a.next = 10#usize)
    (g : Array SAQ_WideABI.E 29#usize) (hg : NHT_PacketOps.powers 29#usize p.gamma = ok g)
    (pend : verifier.BatchedWeights)
    (hpend : NJJ_Common.pending rr (alloc.vec.Vec.deref a.weights) = ok (.Ok pend))
    (geo : verifier.QueryGeometry) (obs : Option (VTop_Stages.verifier.Phase → Result Unit))
    (a1 : verifier.Accumulator) (b1 : verifier.BatchedWeights)
    (hq : NJJ_Common.query proof p a g obs geo pend 22#usize = ok (.Ok (a1, b1)))
    (s3 : Slice VTop_Stages.aspis_core.field.QM31)
    (back : Slice VTop_Stages.aspis_core.field.QM31 → alloc.vec.Vec VTop_Stages.aspis_core.field.QM31)
    (hs3 : lift (alloc.vec.Vec.deref_mut a1.weights) = ok (s3, back))
    (s4 : Slice VTop_Stages.aspis_core.field.QM31)
    (hs4 : Port3_FlushInstall.flush b1 s3 = ok s4) :
    (back s4).val.length = 64 ∧ s4.val.length = 64 := by
  obtain ⟨d, _, _⟩ := NPH_R22JoinCW2.entered_domain wr D ck proof pub hash p a hres
  have d0 := NNH_Run5bQueryDomain.initial rr p a pend d hn hpend
  have canonical := NNU_Query.powersDomain p a d g hg
  have d1 := (query_domain proof p g geo a pend a1 b1 d0 canonical obs hq).2
  have e : (s3, back) = alloc.vec.Vec.deref_mut a1.weights := (Result.ok.inj hs3).symm
  have h3 : s3 = (alloc.vec.Vec.deref_mut a1.weights).1 := congrArg Prod.fst e
  have hb : back = (alloc.vec.Vec.deref_mut a1.weights).2 := congrArg Prod.snd e
  have l3 : s3.val.length = 64 := by
    rw [h3]; exact d1.width
  have hraw : b1.raw.val.length = 64 := d1.progress.2.1
  have l4 := (Port3_FlushInstall.accepted_contents b1 s3 s4 (by omega) hs4).2
  refine ⟨?_, by omega⟩
  rw [hb]
  show s4.val.length = 64; omega

/-- On every input, NJJ_Common.run calls its finish only on an accumulator whose weights have
length 64: replacing the finish by any finish' that agrees there leaves the run unchanged. -/
theorem run_finish_congr (wr rr : NP6_StdModel.Reservation) (merkle : NJJ_Common.Merkle)
    (finish finish' : NJJ_Common.Finish) {H : Type} (D : VTop_Stages.aspis_core.digest.Digest32 H)
    (pub proof ck : Slice U8) (hash : H) (obs : Option (VTop_Stages.verifier.Phase → Result Unit))
    (agree : ∀ v p a o, a.weights.val.length = 64 → finish' v p a o = finish v p a o) :
    NJJ_Common.run wr rr merkle finish' D pub proof ck hash obs =
      NJJ_Common.run wr rr merkle finish D pub proof ck hash obs := by
  unfold NJJ_Common.run
  refine bind_congr_ok _ _ _ (fun r hr => ?_)
  refine bind_congr_ok _ _ _ (fun cf hcf => ?_)
  cases cf with
  | Break residual => rfl
  | Continue val =>
    obtain ⟨p, a⟩ := val
    have hres := branch_ok hr hcf
    try dsimp only
    refine ite_congr rfl (fun _ => rfl) (fun hc => ?_)
    have hn : a.next = 10#usize := next_of_guard hc
    refine bind_congr_ok _ _ _ (fun g hg => ?_)
    refine bind_congr_ok _ _ _ (fun u _ => ?_)
    refine bind_congr_ok _ _ _ (fun i _ => ?_)
    refine bind_congr_ok _ _ _ (fun i1 _ => ?_)
    refine bind_congr_ok _ _ _ (fun s _ => ?_)
    refine bind_congr_ok _ _ _ (fun o _ => ?_)
    refine bind_congr_ok _ _ _ (fun r1 _ => ?_)
    refine bind_congr_ok _ _ _ (fun cf1 _ => ?_)
    cases cf1 with
    | Break residual => rfl
    | Continue val1 =>
      refine bind_congr_ok _ _ _ (fun i2 _ => ?_)
      refine bind_congr_ok _ _ _ (fun i3 _ => ?_)
      refine bind_congr_ok _ _ _ (fun s1 _ => ?_)
      refine bind_congr_ok _ _ _ (fun r2 _ => ?_)
      refine bind_congr_ok _ _ _ (fun root _ => ?_)
      refine bind_congr_ok _ _ _ (fun r3 _ => ?_)
      refine bind_congr_ok _ _ _ (fun cf2 _ => ?_)
      cases cf2 with
      | Break residual => rfl
      | Continue u2 =>
        refine bind_congr_ok _ _ _ (fun u3 _ => ?_)
        refine bind_congr_ok _ _ _ (fun r4 _ => ?_)
        refine bind_congr_ok _ _ _ (fun cf3 _ => ?_)
        cases cf3 with
        | Break residual => rfl
        | Continue geo =>
          try dsimp only
          refine bind_congr_ok _ _ _ (fun r5 hr5 => ?_)
          refine bind_congr_ok _ _ _ (fun cf4 hcf4 => ?_)
          cases cf4 with
          | Break residual => rfl
          | Continue pend =>
            have hpend := branch_ok hr5 hcf4
            refine bind_congr_ok _ _ _ (fun r6 hr6 => ?_)
            refine bind_congr_ok _ _ _ (fun cf5 hcf5 => ?_)
            cases cf5 with
            | Break residual => rfl
            | Continue val4 =>
              obtain ⟨a1, b1⟩ := val4
              have hq := branch_ok hr6 hcf5
              try dsimp only
              refine bind_congr_ok _ _ _ (fun sb hs3 => ?_)
              obtain ⟨s3, back⟩ := sb
              refine bind_congr_ok _ _ _ (fun s4 hs4 => ?_)
              try dsimp only
              refine bind_congr_ok _ _ _ (fun s5 _ => ?_)
              refine bind_congr_ok _ _ _ (fun s6 _ => ?_)
              refine bind_congr_ok _ _ _ (fun s7 _ => ?_)
              refine bind_congr_ok _ _ _ (fun i4 _ => ?_)
              refine bind_congr_ok _ _ _ (fun s8 _ => ?_)
              refine bind_congr_ok _ _ _ (fun i5 _ => ?_)
              refine bind_congr_ok _ _ _ (fun s9 _ => ?_)
              refine bind_congr_ok _ _ _ (fun s10 _ => ?_)
              exact agree _ _ _ _ (width_at_finish wr rr D ck proof pub hash p a hres hn g hg pend hpend
                geo obs a1 b1 hq s3 back hs3 s4 hs4).1

/-- The finish guarded on width 64. -/
def widthGuard (f : NJJ_Common.Finish) : NJJ_Common.Finish := fun v p a o =>
  if a.weights.val.length = 64 then f v p a o else fail .panic

/-- The deployed tx2 common (LIBB_Tx2EnvCode.common) equals the same run whose finish executes
only on accumulators with weights of length 64. No premise. -/
theorem deployed_common_guarded (env : RSL.Env) (pub proof ck : Slice U8) :
    LIBB_Tx2EnvCode.common env pub proof ck =
      NJJ_Common.run (LIBB_Tx2Reservation.reservation env) (LIBB_Tx2Reservation.reservation env)
        (NLP_NativeMerkle.action (LIBB_PartitionEnv.H env))
        (widthGuard (NLB_Parent.finish (LIBB_Tx2Reservation.reservation env)))
        (LIBB_PartitionEnv.digest env) pub proof ck () none := by
  unfold LIBB_Tx2EnvCode.common
  exact (run_finish_congr _ _ _ _ _ _ _ _ _ _ _
    (fun v p a o h => by unfold widthGuard; exact if_pos h)).symm

#print axioms run_reach
#print axioms query_domain
#print axioms next_of_guard
#print axioms width_at_finish
#print axioms run_finish_congr
#print axioms deployed_common_guarded
end AspisR1.NPR_R22WeightsWidth
