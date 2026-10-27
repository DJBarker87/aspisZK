import F3K_QueryFull
import F3K_RhoJoin
import F3K_PayloadFits
import F3K_InactivePhysical
import S1ClosedPreparationHashCodeV1
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3K_OpeningCalls
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation PreparedHashCode
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OraclePortCompactDraft MultiproofConeCanonical

structure Calls {Hash : Type} (D : aspis_core.Digest32 Hash) (B : PreparedModel.Boundaries)
    (embed : aspis_core.field.M31 → Result aspis_core.field.WideExact)
    (v : verifier.View) (p : Parsed) where
  t0 : transcript.Transcript Hash
  t1 : transcript.Transcript Hash
  t2 : transcript.Transcript Hash
  t3 : transcript.Transcript Hash
  t4 : transcript.Transcript Hash
  t5 : transcript.Transcript Hash
  t6 : transcript.Transcript Hash
  inactive : Array U8 32#usize
  second : alloc.vec.Vec U8
  gamma : aspis_core.field.WideExact
  kappa : aspis_core.field.WideExact
  alpha0 : aspis_core.field.WideExact
  alpha1 : aspis_core.field.WideExact
  rho : aspis_core.field.QM31
  queries : Array U32 22#usize
  firstCall : PreparedModel.scalar B D t0 27#u8 v.y1 true=ok (gamma,t1)
  inactiveCall : B.toBytes v.inactive=ok inactive
  secondCall : PreparedModel.scalar B D t1 28#u8 (Array.to_slice inactive) false=ok (kappa,t2)
  thirdCall : PreparedModel.scalar B D t2 29#u8 v.round0 false=ok (alpha0,t3)
  fourthCall : PreparedModel.scalar B D t3 30#u8 second.deref false=ok (alpha1,t4)
  queryCall : QueriesModel.queries (Query31ConcreteMaterializedSchedule.concreteBoundaries
    Query31ConcreteDriverTraceFacts.sourceDefaultState embed) D t4 31#u8 v.final_message=ok (.Ok queries,t5)
  rhoCall : PreparedModel.scalar_k B D t5 32#u8 PreparedScratchReachability.emptyPayload=ok (rho,t6)
  frame27 : rowBytes p 27=framed (bytesOf v.y1.val)
  frame28 : rowBytes p 28=framed (bytesOf (Array.to_slice inactive).val)
  frame29 : rowBytes p 29=framed (bytesOf v.round0.val)
  frame30 : rowBytes p 30=framed (bytesOf second.val)
  frame31 : rowBytes p 31=framed (bytesOf v.final_message.val)
  frame32 : rowBytes p 32=framed []

def log {Hash : Type} {D : aspis_core.Digest32 Hash} {B : PreparedModel.Boundaries}
    {embed : aspis_core.field.M31 → Result aspis_core.field.WideExact}
    {v : verifier.View} {p : Parsed} (c : Calls D B embed v p) : List (Bytes × State) :=
  observe (run (PreparedScalarEffects.scalar effects B D c.t0 27#u8 v.y1 true)).1 ++
  observe (run (PreparedScalarEffects.scalar effects B D c.t1 28#u8 (Array.to_slice c.inactive) false)).1 ++
  observe (run (PreparedScalarEffects.scalar effects B D c.t2 29#u8 v.round0 false)).1 ++
  observe (run (PreparedScalarEffects.scalar effects B D c.t3 30#u8 c.second.deref false)).1 ++
  observe (run (PreparedQueryEffects.queries effects
    (Query31ConcreteMaterializedSchedule.concreteBoundaries Query31ConcreteDriverTraceFacts.sourceDefaultState embed)
    D c.t4 31#u8 v.final_message)).1 ++
  observe (run (PreparedScalarEffects.scalar_k effects B D c.t5 32#u8 PreparedScratchReachability.emptyPayload)).1

end AspisR1.F3K_OpeningCalls
end
