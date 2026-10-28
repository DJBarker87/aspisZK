import NBA_ClaimInputs
import NBA_TraceReplay
set_option autoImplicit false
noncomputable section
namespace AspisR1.NBA_PrepareSuffix
open Aeneas Aeneas.Std Result AspisR1PublicPreparation AspisR1ClaimPreparedBridge
open PreparedScratchReachability

/-- Construction of the entire two-fold cohort result from linked child-call
observations. Powers, claim, prepared output and final scratch are conclusions.
The separate native P6 association must supply the observations in this theorem. -/
theorem source {H : Type} (D : aspis_core.Digest32 H) (sem : r1_semantic.Verified H)
    (v : verifier.View) (hash : H) (old : Array PE 29#usize)
    (hs : LPq_ReadPorts.SemCanonical (toClaimSem sem))
    (compact before : Slice U8) (len : compact.val.length=464) (size : before.val.length=928)
    (checked : LPt_External.compact.check_values compact=ok (.Ok ()))
    (expand : LPt_LPn.Expand.NativeTrace compact.val before.val 29 v.y1.val)
    (hi : LPi_FieldValues.canonE (NBA_Carriers.back v.inactive))
    (start t1 t2 t3 t4 t5 t6 : transcript.Transcript H) (bytes : Array U8 32#usize)
    (gamma kappa alpha0 alpha1 : PE) (root : Array U8 32#usize)
    (b1 b2 : alloc.vec.Vec U8) (queries : Array U32 22#usize) (rho : aspis_core.field.QM31)
    (seed : transcript.Transcript.new D hash sem.transcript.state v.variant=ok start)
    (gc : PreparedModel.scalar NBA_Installed.actual.sampling D start 27#u8 v.y1 true=ok (gamma,t1))
    (bytesCall : NBA_Installed.actual.sampling.toBytes v.inactive=ok bytes)
    (kc : PreparedModel.scalar NBA_Installed.actual.sampling D t1 28#u8 (Array.to_slice bytes) false=ok (kappa,t2))
    (a0 : PreparedModel.scalar NBA_Installed.actual.sampling D t2 29#u8 v.round0 false=ok (alpha0,t3))
    (folds : transport.Variant.folds v.variant=ok 2#usize)
    (rootCall : core.option.Option.unwrap v.folded_root=ok root)
    (first : alloc.vec.Vec.extend_from_slice core.clone.CloneU8 (alloc.vec.Vec.with_capacity U8 256#usize) (Array.to_slice root)=ok b1)
    (second : alloc.vec.Vec.extend_from_slice core.clone.CloneU8 b1 v.round1=ok b2)
    (a1 : PreparedModel.scalar NBA_Installed.actual.sampling D t3 30#u8 (alloc.vec.Vec.deref b2) false=ok (alpha1,t4))
    (qc : NBA_Installed.actual.sampling.queries D t4 31#u8 v.final_message=ok (.Ok queries,t5))
    (rc : PreparedModel.scalar_k NBA_Installed.actual.sampling D t5 32#u8 emptyPayload=ok (rho,t6)) :
    ∃ (g : Array LPi_FieldValues.NE 29#usize) (claim : LPi_FieldValues.NE),
      FIo_Native.weights.powers 29#usize (NBA_Carriers.back gamma)=ok g ∧
      LPq_PreparedTrace.Trace (toClaimSem sem) v.y1 (XRo_Join_Carriers.arr LPq_Powers.claim g)
        (NBA_Carriers.back v.inactive) (NBA_Carriers.back kappa) claim ∧
      LPi_FieldValues.canonE claim ∧
      PreparedScratchModel.prepare NBA_Installed.actual D sem v hash old=
        ok (.Ok (output sem v gamma kappa (Array.make 2#usize [alpha0,alpha1]) rho queries
          (NBA_ClaimCallee.wide claim) t6),mapArray NBA_ClaimCallee.wide g) := by
  obtain ⟨g,claim,native,powers,trace,canonical,call⟩ := NBA_ClaimInputs.source D sem hs
    compact before v.y1 len size checked expand start t1 t2 (Array.to_slice bytes)
    gamma v.inactive kappa gc kc hi
  refine ⟨g,claim,native,trace,canonical,?_⟩
  apply NBA_TraceReplay.source
  refine ⟨start,t1,t2,t3,bytes,gamma,kappa,alpha0,seed,gc,bytesCall,kc,a0,?_⟩
  apply Tail.double folds root b1 b2 alpha1 t4 rootCall first second a1
  refine ⟨queries,t5,t6,rho,NBA_ClaimCallee.wide claim,qc,?_,powers,call,rfl⟩
  simpa only [show ¬(31#u8=30#u8) by decide,↓reduceIte] using rc

#print axioms source
end AspisR1.NBA_PrepareSuffix
end
