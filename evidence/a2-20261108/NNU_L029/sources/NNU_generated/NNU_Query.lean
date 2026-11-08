import NNU_QueryLoop
import NFW_PowersDomain
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNU_Query
open Aeneas Aeneas.Std Result AspisR1Stage2 Port3_NativeQueryBody NNH_Run5bQuerySlots

theorem powersDomain (p : verifier.Prepared) (a : verifier.Accumulator)
 (d : NID_ResumeFields.Domain p a)
 (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
 (powers : NHT_PacketOps.powers 29#usize p.gamma=.ok g) :
 NEV_DotInputs.Canonical (FIp_DotsAdapter.toArray g) := by
 have gamma : NFN_LPi_FieldValues.canonE (FIo_Install.toE p.gamma) := by
  rcases d.gamma with ⟨⟨a,b,c,d⟩,⟨e,f,g,h⟩⟩
  exact ⟨⟨⟨a,b⟩,c,d⟩,⟨⟨e,f⟩,g,h⟩⟩
 unfold NHT_PacketOps.powers at powers
 obtain ⟨raw,run,equality⟩ := Port3_PushFrame.bind_success _ _ _ powers
 cases Result.ok.inj equality
 exact NFW_PowersDomain.query_domain _ gamma raw run

theorem source (m : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (r : NP6_StdModel.Reservation)
 (proof : Slice U8) (p : verifier.Prepared) (a : verifier.Accumulator)
 (g : Array aspis_core.field.wide_exact.WideExact 29#usize) (geo : verifier.QueryGeometry)
 (pending : verifier.BatchedWeights) (d : NID_ResumeFields.Domain p a) (next : a.next=10#usize)
 (powers : NHT_PacketOps.powers 29#usize p.gamma=.ok g)
 (init : NJJ_Common.pending (LIBB_Tx2Reservation.reservation env) a.weights.deref=.ok (.Ok pending)) :
 (NNH_Tx2SlotTransport.stage m env err r).op6 proof p a g none geo pending 22#usize =
 NJJ_Common.query proof p a g none geo pending 22#usize := by
 have domain:=NNH_Run5bQueryDomain.initial _ p a pending d next init
 have start : a.next.val=10 := congrArg UScalar.val next
 have loop:=NNU_QueryLoop.source m env err r proof p a g geo pending domain start
 have packet:=NFS_QueryLoopRoot.tx2 NJJ_QueryOps.concrete proof p a g geo pending 0 0
  (powersDomain p a d g powers) domain start
 change Port3_QueryInstall.result
  (verifier.candidate.query_loop (actual m env err r) proof p a g none geo pending 22#usize) = _
 rw [loop,NNH_ResultPortTransport.port]
 exact congrArg NHT_ResultPort.action packet.symm

theorem returned : NNH_Tx2OpenSlots.query := by
 intro m env err r proof p a g geo pending afterPending after d next powers _ init accepted
 rw [source m env err r proof p a g geo pending d next powers init]
 exact accepted
#print axioms powersDomain
#print axioms source
#print axioms returned
end AspisR1.NNU_Query
end
