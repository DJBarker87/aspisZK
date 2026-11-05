import NHL_PreparedScalars
set_option autoImplicit false
noncomputable section
namespace AspisR1.NHL_PreparedOpening
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NFW_PreparedControl
open NHL_PreparedScalars

def foldPayload (v : verifier.View) : Result (Slice U8) := do
 let capacity ← 32#usize+224#usize
 let root ← core.option.Option.unwrap v.folded_root
 let payload ← lift (Array.to_slice root)
 let b1 ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 (alloc.vec.Vec.with_capacity U8 capacity) payload
 let b2 ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 b1 v.round1
 ok (alloc.vec.Vec.deref b2)

theorem single {H : Type} (D : aspis_core.Digest32 H) (v : verifier.View)
 (gamma kappa alpha0 : aspis_core.field.WideExact) (before : transcript.Transcript H)
 (folds : transport.Variant.folds v.variant=ok 1#usize) :
 NGN_Opening.foldCut actual D v gamma kappa alpha0 before=
 ok ⟨gamma,kappa,Array.make 2#usize [alpha0,aspis_core.field.WideExact.ZERO],before,30#u8⟩ := by
 unfold NGN_Opening.foldCut
 rw [folds,bind_tc_ok]
 rfl

theorem double_factor {H : Type} (D : aspis_core.Digest32 H) (v : verifier.View)
 (gamma kappa alpha0 : aspis_core.field.WideExact) (before : transcript.Transcript H)
 (folds : transport.Variant.folds v.variant=ok 2#usize) :
 NGN_Opening.foldCut actual D v gamma kappa alpha0 before=
 (do let payload ← foldPayload v
     let (a,last) ← PreparedModel.scalar actual.sampling D before 30#u8 payload false
     ok (Opening.mk gamma kappa (Array.make 2#usize [alpha0,a]) last 31#u8)) := by
 unfold NGN_Opening.foldCut foldPayload
 rw [folds,bind_tc_ok]
 simp only [↓reduceIte,bind_assoc_eq,bind_tc_ok]

/-- S4 actually substitutes NGT's scalar30 law, at the exact produced payload. -/
theorem double {H : Type} (D : aspis_core.Digest32 H) (v : verifier.View)
 (gamma kappa alpha0 alpha1 : aspis_core.field.WideExact) (before : transcript.Transcript H)
 (folds : transport.Variant.folds v.variant=ok 2#usize)
 (payload : Slice U8) (produced : foldPayload v=ok payload)
 (b : NGT_NBL_BlockTrace.Block D before 30#u8 payload)
 (reduction : NGT_Reduction.Scalar b.value false alpha1) :
 NGN_Opening.foldCut actual D v gamma kappa alpha0 before=
 ok ⟨gamma,kappa,Array.make 2#usize [alpha0,alpha1],{before with state:=b.final},31#u8⟩ := by
 rw [double_factor D v gamma kappa alpha0 before folds,produced,bind_tc_ok]
 rw [scalar_dictionary]
 rw [NGT_CallerInterface.scalar _ D before 30#u8 payload false b alpha1 reduction,bind_tc_ok]
 rfl

/-- Closed scalar packets consumed in source order. The argument to S4 is the
S3 transcript from THIS trace. Seed/serialization are existing runtime/Std
observations, not OPEN scalar child semantics. -/
theorem prefix_result {H : Type} (D : aspis_core.Digest32 H)
 (sem : r1_semantic.Verified H) (v : verifier.View) (hash : H)
 (state : Array U8 32#usize) (start : transcript.Transcript H)
 (seed : r1_wire.SemanticTranscript.impl.state D sem.transcript=ok state)
 (newStart : transcript.Transcript.new D hash state v.variant=ok start)
 (bGamma : NGT_NBL_BlockTrace.Block D start 27#u8 v.y1)
 (gamma : aspis_core.field.WideExact) (gammaReduction : NGT_Reduction.Scalar bGamma.value true gamma)
 (bytes : Array U8 32#usize) (serialize : actual.sampling.toBytes v.inactive=ok bytes)
 (bKappa : NGT_NBL_BlockTrace.Block D {start with state:=bGamma.final} 28#u8 (Array.to_slice bytes))
 (kappa : aspis_core.field.WideExact) (kappaReduction : NGT_Reduction.Scalar bKappa.value false kappa)
 (bAlpha : NGT_NBL_BlockTrace.Block D {start with state:=bKappa.final} 29#u8 v.round0)
 (alpha0 : aspis_core.field.WideExact) (alphaReduction : NGT_Reduction.Scalar bAlpha.value false alpha0) :
 NGN_Opening.seedCut actual D sem v hash=
 NGN_Opening.foldCut actual D v gamma kappa alpha0 {start with state:=bAlpha.final} := by
 unfold NGN_Opening.seedCut
 rw [seed,bind_tc_ok,newStart,bind_tc_ok,
   NHL_PreparedScalars.gamma D v start bGamma gamma gammaReduction]
 rw [NHL_PreparedScalars.kappa D v _ gamma kappa bytes serialize bKappa kappaReduction]
 rw [NHL_PreparedScalars.alpha0 D v _ gamma kappa alpha0 bAlpha alphaReduction]
#print axioms single
#print axioms double_factor
#print axioms double
#print axioms prefix_result
end AspisR1.NHL_PreparedOpening
