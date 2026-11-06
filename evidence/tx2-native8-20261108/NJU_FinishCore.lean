import NJU_FinishDomain
import NJF_Root
set_option autoImplicit false
noncomputable section
namespace NJU_FinishCore
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2

/-- Intrinsic caller fields only. No View, bytes, history or successful result. -/
structure Holds (p : verifier.Prepared) (a : verifier.Accumulator) : Prop where
 accumulator : NGM_FinishDomain.AccumulatorDomain a
 s2 : p.variant=.S2
 alpha : ∀ i, i<2 → ∀ x,p.alpha.val[i]?=some x→NBO_TailDomain.WideCanonical x

theorem selected (p : verifier.Prepared) (a : verifier.Accumulator) (core : Holds p a)
 (i : Usize) (inside : i.val<2) :
 Array.index_usize p.alpha i=ok (NIG_FinishAlpha.alpha p i.val inside) ∧
 LPi_FieldValues.canonE (FIo_Install.toE (NIG_FinishAlpha.alpha p i.val inside)) := by
 refine ⟨NHI_ScalarDomain.index p.alpha i inside,NIG_FinishAlpha.canonical _ ?_⟩
 apply core.alpha i.val inside
 simp [NIG_FinishAlpha.alpha,NHI_ScalarDomain.pick,
  show i.val<p.alpha.val.length by rw [p.alpha.property];exact inside]

/-- The SAME resume/query/flush supplies the intrinsic fields before any
case split on proof bytes. Both allocator outcomes remain in the caller. -/
theorem reached (reserved : Bool) {H : Type} (d : aspis_core.digest.Digest32 H)
 (ck proof pub : Slice U8) (hash : H) (p : verifier.Prepared) (a after : verifier.Accumulator)
 (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
 (geometry : verifier.QueryGeometry) (pending : verifier.BatchedWeights)
 (ckSize : ck.val.length=1768)
 (resume : verifier.resumeWithOps (CheckpointBytes4Ops.ops reserved) d ck proof pub .S2 hash=ok (.Ok (p,a)))
 (start : a.next.val=10)
 (query : Port3_NativeQueryBody.verifier.candidate.query_loop
  (NFS_QueryOps.installed NJJ_QueryOps.concrete) proof p a g none geometry
  (NFW_QueryResume.pending a) 22#usize=ok (.Ok (after,pending))) :
 ∃ out : Slice aspis_core.field.QM31,
 Port3_FlushInstall.flush pending after.weights.deref=ok out ∧
 Holds p {after with weights:=⟨out.val,out.property⟩} := by
 have dom:=NID_ResumeFields.returned reserved d ck proof pub hash p a ckSize resume
 have qdom:=NFW_QueryResume.domain p a dom.width
  (NID_ResumeQuery.weights a dom.weights)
  (NID_ResumeCallerDomain.wide a.rhs dom.rhs)
  (NID_ResumeCallerDomain.power a.power dom.power)
  (NID_ResumeCallerDomain.power p.rho dom.rho) start
 obtain ⟨out,flush,acc,_⟩:=NGM_FinishDomain.tx2_writeback NJJ_QueryOps.concrete proof p a after g
  geometry (NFW_QueryResume.pending a) pending qdom start query
 refine ⟨out,flush,acc,dom.variant,?_⟩
 intro i _ x hx
 exact NID_ResumeCallerDomain.wide x (dom.alpha x (List.mem_of_getElem? hx))

/-- Generalized SOURCE erasure, with no raw-window clauses at all. This is
not yet a generalized native pair certificate. All Result arms are retained. -/
theorem source (r : NP6_StdModel.Reservation) (v : verifier.View)
 (p : verifier.Prepared) (a : verifier.Accumulator) (core : Holds p a) :
 Port3_NativeFinishBody.verifier.finish_relation (NIG_Slots.installed r) v p a none=
 NIT_FinishSkeleton.run r v p a := by
 obtain ⟨i0,c0⟩:=selected p a core 0#usize (by decide)
 obtain ⟨i1,c1⟩:=selected p a core 1#usize (by decide)
 have h:=NHT_FinishCaller.source (NIG_Slots.installed r) r v p a none _ _ i0 i1 c0 c1
  (NIG_Slots.folds r p core.s2) (NIG_Slots.round0 r _ _ _)
  (fun claim _=>NIG_Slots.round1 r _ _ _) core.accumulator (NIG_Slots.dot r _ _)
  (FIn_WeightsInstall.newWeights p.variant p.semantic_alpha p.z) (NIG_Slots.NHM_new r p)
  (NIG_PairExport.packet r) (NIG_PairExport.NHM_pair r p v)
 exact h.trans (NIT_FinishSkeleton.packet r v p a)

#print source
#print axioms selected
#print axioms reached
#print axioms source
end NJU_FinishCore
