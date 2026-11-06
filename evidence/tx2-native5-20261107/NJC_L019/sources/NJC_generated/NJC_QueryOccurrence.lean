import NIY_ResumeFields
import NID_ResumePrefix
import NID_ResumeQuery
import NHT_PowersDomain
set_option autoImplicit false
noncomputable section
namespace NJC_QueryOccurrence
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2

/-- Derive checkpoint width from the entered emitted resume, rather than an
additional caller precondition. Wrong size returns Checkpoint before the tail. -/
theorem checkpoint_size (reserved : Bool) {H : Type}
 (d : aspis_core.digest.Digest32 H) (ck proof pub : Slice U8) (hash : H)
 (p : NIL_StatePort.F.P) (a : NIL_StatePort.F.A)
 (run : NIL_FreshOps.resume reserved d ck proof pub .S2 hash=ok (.Ok (p,a))) :
 ck.val.length=1768 := by
 by_contra wrong
 have ne : Slice.len ck≠1768#usize := by
  intro h
  apply wrong
  have hv:=congrArg UScalar.val h
  exact hv
 have bad : NIL_FreshOps.resume reserved d ck proof pub .S2 hash=
   ok (.Err NID_ResumeEmission.verifier.Error.Checkpoint) := by
  unfold NIL_FreshOps.resume
  apply NID_ResumePrefix.size_error
  · rfl
  · exact ne
 rw [bad] at run
 cases run

/-- SAME returned pair supplies the powers and query6 entry domains. This is an
internal reached-branch lemma: run/start are derived by the parent source bind
and its split guard, never permitted as additional positive-root hypotheses.
The missing native producer binding is not asserted by this theorem. -/
theorem closed (reserved : Bool) {H : Type}
 (d : aspis_core.digest.Digest32 H) (ck proof pub : Slice U8) (hash : H)
 (freshP : NIL_StatePort.F.P) (freshA : NIL_StatePort.F.A)
 (run : NIL_FreshOps.resume reserved d ck proof pub .S2 hash=ok (.Ok (freshP,freshA)))
 (start : (NIL_StatePort.accumulator freshA).next.val=10)
 (base : Port3_NativeQueryBody.Ops) (geometry : verifier.QueryGeometry) (qPlace gPlace : Nat) :
 let p:=NIL_StatePort.prepared freshP
 let a:=NIL_StatePort.accumulator freshA
 ∃ g : Array NFN_LPi_FieldValues.NE 29#usize,
 FIo_Native.weights.powers 29#usize (FIo_Install.toE p.gamma)=ok g ∧
 NHT_PacketOps.powers 29#usize p.gamma=ok (FIp_DotsAdapter.fromArray g) ∧
 NHT_PacketOps.query base qPlace gPlace proof p a (FIp_DotsAdapter.fromArray g)
   none geometry (NFW_QueryResume.pending a) 22#usize=
 NHT_ResultPort.action (Port3_NativeQueryBody.verifier.candidate.query_loop
   (NFS_QueryOps.installed base) proof p a (FIp_DotsAdapter.fromArray g)
   none geometry (NFW_QueryResume.pending a) 22#usize) := by
 let p:=NIL_StatePort.prepared freshP
 let a:=NIL_StatePort.accumulator freshA
 have same : verifier.resumeWithOps (CheckpointBytes4Ops.ops reserved) d ck proof pub .S2 hash=
   ok (.Ok (p,a)) := by
  rw [←NIY_ResumePort.source,run]
  rfl
 have size:=checkpoint_size reserved d ck proof pub hash freshP freshA run
 have dom:=NID_ResumeFields.returned reserved d ck proof pub hash p a size same
 have gamma:=NID_ResumeCallerDomain.gamma p.gamma dom.gamma
 obtain ⟨g,call,powers,_⟩:=NHT_PowersDomain.produced p.gamma gamma
 refine ⟨g,call,powers,?_⟩
 exact NHT_PacketOps.query_source base proof p a dom.width
  (NID_ResumeQuery.weights a dom.weights)
  (NID_ResumeCallerDomain.wide a.rhs dom.rhs)
  (NID_ResumeCallerDomain.power a.power dom.power)
  (NID_ResumeCallerDomain.power p.rho dom.rho) start _ gamma g call geometry qPlace gPlace

#print axioms checkpoint_size
#print axioms closed
end NJC_QueryOccurrence
