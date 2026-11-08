import NNH_HostOracle
import NNH_ResultPortTransport
import NNH_Tx2LiteralSlots
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_Tx2OpenSlots
open Aeneas Aeneas.Std Result VTop_Stages NNH_Tx2SlotTransport
/-- Exact unproved leaf transport targets at the S3 cap. None is a theorem
hypothesis or a field of the literal host. No final consumer imports them. -/
def inactive : Prop := ∀ bs : Slice U8,
 Port1_LibrarySource.decode bs = NJC_ClosedCalls.inactive bs

def geometry : Prop :=
 ∀ (m : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE) (env : RSL.Env)
 (err : NFN_NEW_GeometryDictionary.CE) (r : NP6_StdModel.Reservation)
 (q : Array U32 22#usize) (start finish : Usize) (out : verifier.QueryGeometry),
 NJC_ClosedCalls.geometry q start finish = .ok (.Ok out) →
 (stage m env err r).op11 q start finish = .ok (.Ok out)

def query : Prop :=
 ∀ (m : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE) (env : RSL.Env)
 (err : NFN_NEW_GeometryDictionary.CE) (r : NP6_StdModel.Reservation)
 (proof : Slice U8) (p : verifier.Prepared) (a : verifier.Accumulator)
 (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
 (geo : verifier.QueryGeometry) (pending afterPending : verifier.BatchedWeights)
 (after : verifier.Accumulator),
 NID_ResumeFields.Domain p a → a.next = 10#usize →
 NHT_PacketOps.powers 29#usize p.gamma = .ok g →
 NJC_ClosedCalls.geometry p.queries a.next 22#usize = .ok (.Ok geo) →
 NJJ_Common.pending (LIBB_Tx2Reservation.reservation env) a.weights.deref = .ok (.Ok pending) →
 NJJ_Common.query proof p a g none geo pending 22#usize = .ok (.Ok (after,afterPending)) →
 (stage m env err r).op6 proof p a g none geo pending 22#usize = .ok (.Ok (after,afterPending))

def merkle : Prop :=
 ∀ (m : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE) (env : RSL.Env)
 (err : NFN_NEW_GeometryDictionary.CE) (r : NP6_StdModel.Reservation)
 (pub proof ck : Slice U8) (p : verifier.Prepared) (a : verifier.Accumulator)
 (root : Array U8 32#usize),
 NJJ_Common.resume (LIBB_Tx2Reservation.reservation env) (LIBB_PartitionEnv.digest env)
  ck proof pub .S2 () = .ok (.Ok (p,a)) →
 NLP_NativeMerkle.action (LIBB_PartitionEnv.H env) (LIBB_PartitionEnv.digest env)
  proof p root 1#usize () = .ok (.Ok ()) →
 (stage m env err r).op5
  (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 (NNH_CorrectConfiguration.sdk m env err r))
  proof p root 1#usize () = .ok (.Ok ())
#print axioms inactive
#print axioms geometry
#print axioms query
#print axioms merkle
end AspisR1.NNH_Tx2OpenSlots
end
